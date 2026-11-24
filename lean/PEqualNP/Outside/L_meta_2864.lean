import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2864

open PEqualNP.CircuitLowerBounds

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true)
    (hv : op.eval (ins.map fun i => w.getD i false) = true) :
    op.eval (ins.map fun i => w'.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hv ⊢
    rintro _ ⟨a, ha, rfl⟩
    exact h a (hv _ ⟨a, ha, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hv ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, h a hv⟩

theorem getD_snoc (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    rw [hk]
    simp

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
         (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    refine ⟨by simp [hl], fun i hv => ?_⟩
    rw [getD_snoc] at hv ⊢
    rw [← hl]
    split_ifs at hv ⊢ with h1 h2
    · exact hi i hv
    · exact op_mono g.op (hgs g (by simp)) g.inputs w w' hi hv

def W (C : Circuit) {n : ℕ} (P L : Fin n → Bool) (k : ℕ) : Bool :=
  (C.wires (List.ofFn P ++ List.ofFn L)).getD k false

theorem getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < m then f ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem W_mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {n : ℕ}
    (P P' L L' : Fin n → Bool) (hP : ∀ i, P i = true → P' i = true)
    (hL : ∀ i, L i = true → L' i = true) (k : ℕ) (hv : W C P L k = true) :
    W C P' L' k = true := by
  unfold W Circuit.wires at *
  rw [← List.ofFn_fin_append] at *
  have hle : Le (List.ofFn (Fin.append P L)) (List.ofFn (Fin.append P' L')) := by
    refine ⟨by simp, fun i hi => ?_⟩
    rw [getD_ofFn] at hi ⊢
    split_ifs at hi ⊢ with h
    by_cases hin : i < n
    · have e : (⟨i, h⟩ : Fin (n + n)) = Fin.castAdd n ⟨i, hin⟩ := rfl
      rw [e, Fin.append_left] at hi ⊢
      exact hP _ hi
    · have e : (⟨i, h⟩ : Fin (n + n)) = Fin.natAdd n ⟨i - n, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Fin.append_right] at hi ⊢
      exact hL _ hi
  refine (fold_le C.gates (fun g hg => ?_) _ _ hle).2 k hv
  have := (hC g hg).1
  simpa using this

theorem indL (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {n : ℕ} (k : ℕ)
    (h : ∀ P : Fin n → Bool, (C.wires (List.ofFn P ++ List.replicate n false)).getD k false =
      (C.wires (List.ofFn P ++ List.replicate n true)).getD k false) :
    ∀ P L : Fin n → Bool, W C P L k = W C P (fun _ => false) k := by
  intro P L
  have h' := h P
  rw [← List.ofFn_const, ← List.ofFn_const] at h'
  change W C P (fun _ => false) k = W C P (fun _ => true) k at h'
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rw [h']
    exact W_mono C hC P P L _ (fun _ h => h) (fun _ _ => rfl) k hv
  · intro hv
    exact W_mono C hC P P _ L (fun _ h => h) (fun _ h => by simp at h) k hv

theorem indP (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) {n : ℕ} (k : ℕ)
    (h : ∀ L : Fin n → Bool, (C.wires (List.replicate n false ++ List.ofFn L)).getD k false =
      (C.wires (List.replicate n true ++ List.ofFn L)).getD k false) :
    ∀ P L : Fin n → Bool, W C P L k = W C (fun _ => false) L k := by
  intro P L
  have h' := h L
  rw [← List.ofFn_const, ← List.ofFn_const] at h'
  change W C (fun _ => false) L k = W C (fun _ => true) L k at h'
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rw [h']
    exact W_mono C hC P _ L L (fun _ _ => rfl) (fun _ h => h) k hv
  · intro hv
    exact W_mono C hC _ P L L (fun _ h => by simp at h) (fun _ h => h) k hv

theorem ca_ne_na {m : ℕ} (a c : Fin m) : Fin.castAdd m a ≠ Fin.natAdd m c := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem na_ne_ca {m : ℕ} (a c : Fin m) : Fin.natAdd m c ≠ Fin.castAdd m a :=
  fun h => ca_ne_na a c h.symm

theorem na_inj {m : ℕ} (a c : Fin m) (h : Fin.natAdd m a = Fin.natAdd m c) : a = c := by
  have := congrArg Fin.val h
  rw [Fin.val_natAdd, Fin.val_natAdd] at this
  exact Fin.ext (by omega)

theorem ca_inj {m : ℕ} (a c : Fin m) (h : Fin.castAdd m a = Fin.castAdd m c) : a = c := by
  have := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_castAdd] at this
  exact Fin.ext this

end PEqualNP.Outside.L_meta_2864

theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  intro x1 x2 x3 x4 x5 hx1 huniq hmono hsound x10 x11 hdep x13 x14
  have hinc : ∀ a c : Fin x2, PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5
      (fun x20 => decide (x20 = Fin.castAdd x2 a ∨ x20 = Fin.natAdd x2 c)) = true → x3 a c := by
    intro a c hC
    by_contra hn
    have hf := hsound (fun x20 => decide (x20 = Fin.castAdd x2 a ∨ x20 = Fin.natAdd x2 c)) ?_ ?_
    · rw [hf] at hC
      exact absurd hC (by simp)
    · refine le_trans ?_ hx1
      apply Fintype.card_le_one_iff.mpr
      rintro ⟨l1, h1⟩ ⟨l2, h2⟩
      apply Subtype.ext
      simp only [decide_eq_true_eq] at h1 h2
      show l1 = l2
      exact (PEqualNP.Outside.L_meta_2864.na_inj _ _ (h1.resolve_left (PEqualNP.Outside.L_meta_2864.na_ne_ca _ _))).trans
        (PEqualNP.Outside.L_meta_2864.na_inj _ _ (h2.resolve_left (PEqualNP.Outside.L_meta_2864.na_ne_ca _ _))).symm
    · rintro ⟨p, l, hpl, hp, hl⟩
      simp only [decide_eq_true_eq] at hp hl
      have hpa := PEqualNP.Outside.L_meta_2864.ca_inj _ _ (hp.resolve_right (PEqualNP.Outside.L_meta_2864.ca_ne_na _ _))
      have hlc := PEqualNP.Outside.L_meta_2864.na_inj _ _ (hl.resolve_left (PEqualNP.Outside.L_meta_2864.na_ne_ca _ _))
      subst hpa
      subst hlc
      exact hn hpl
  have rect : ∀ f g : (Fin x2 → Bool) → Bool,
      (∀ (a c : Fin x2), (f (x14 a) && g (x14 c)) = true →
        PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5
          (fun x20 => decide (x20 = Fin.castAdd x2 a ∨ x20 = Fin.natAdd x2 c)) = true) →
      ∀ a b c d : Fin x2, (f (x14 a) && g (x14 c)) = true → (f (x14 b) && g (x14 d)) = true →
        a = b ∨ c = d := by
    intro f g hfg a b c d h1 h2
    rw [Bool.and_eq_true] at h1 h2
    have hac := hinc a c (hfg a c (by rw [Bool.and_eq_true]; exact ⟨h1.1, h1.2⟩))
    have had := hinc a d (hfg a d (by rw [Bool.and_eq_true]; exact ⟨h1.1, h2.2⟩))
    have hbc := hinc b c (hfg b c (by rw [Bool.and_eq_true]; exact ⟨h2.1, h1.2⟩))
    have hbd := hinc b d (hfg b d (by rw [Bool.and_eq_true]; exact ⟨h2.1, h2.2⟩))
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr ((huniq a b hab).unique ⟨hac, hbc⟩ ⟨had, hbd⟩)
  have hW : ∀ k P L, x13 k P L = PEqualNP.Outside.L_meta_2864.W x5 P L k := fun _ _ _ => rfl
  rw [not_or] at hdep
  obtain ⟨hA, hB⟩ := hdep
  push Not at hA hB
  obtain ⟨u, hu, huL⟩ := hA
  obtain ⟨v, hv, hvP⟩ := hB
  have uL := PEqualNP.Outside.L_meta_2864.indL x5 hmono u huL
  have vP := PEqualNP.Outside.L_meta_2864.indP x5 hmono v hvP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  have const : ∀ k, (∀ P L : Fin x2 → Bool, PEqualNP.Outside.L_meta_2864.W x5 P L k = PEqualNP.Outside.L_meta_2864.W x5 P (fun _ => false) k) →
      (∀ P L : Fin x2 → Bool, PEqualNP.Outside.L_meta_2864.W x5 P L k = PEqualNP.Outside.L_meta_2864.W x5 (fun _ => false) L k) →
      ∀ P L : Fin x2 → Bool, PEqualNP.Outside.L_meta_2864.W x5 P L k = PEqualNP.Outside.L_meta_2864.W x5 (fun _ : Fin x2 => false) (fun _ : Fin x2 => false) k := by
    intro k h1 h2 P L
    rw [h1, h2]
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu] at uL <;> rw [hv] at vP
  · left
    have hc := const x10 uL vP
    cases hb : PEqualNP.Outside.L_meta_2864.W x5 (fun _ : Fin x2 => false) (fun _ : Fin x2 => false) x10
    · refine ⟨x10, by simp, fun P L => ?_⟩
      rw [hW, hW, hc P L, hb]
      simp
    · refine ⟨x11, by simp, fun P L => ?_⟩
      rw [hW, hW, hc P L, hb]
      simp
  · right
    refine ⟨fun P => PEqualNP.Outside.L_meta_2864.W x5 P (fun _ => false) x10, fun L => PEqualNP.Outside.L_meta_2864.W x5 (fun _ => false) L x11, ?_, ?_⟩
    · intro P L
      rw [hW, hW, uL P L, vP P L]
    · exact rect (fun P => PEqualNP.Outside.L_meta_2864.W x5 P (fun _ => false) x10) (fun L => PEqualNP.Outside.L_meta_2864.W x5 (fun _ => false) L x11)
  · right
    refine ⟨fun P => PEqualNP.Outside.L_meta_2864.W x5 P (fun _ => false) x11, fun L => PEqualNP.Outside.L_meta_2864.W x5 (fun _ => false) L x10, ?_, ?_⟩
    · intro P L
      rw [hW, hW, uL P L, vP P L, Bool.and_comm]
    · exact rect (fun P => PEqualNP.Outside.L_meta_2864.W x5 P (fun _ => false) x11) (fun L => PEqualNP.Outside.L_meta_2864.W x5 (fun _ => false) L x10)
  · left
    have hc := const x11 uL vP
    cases hb : PEqualNP.Outside.L_meta_2864.W x5 (fun _ : Fin x2 => false) (fun _ : Fin x2 => false) x11
    · refine ⟨x11, by simp, fun P L => ?_⟩
      rw [hW, hW, hc P L, hb]
      simp
    · refine ⟨x10, by simp, fun P L => ?_⟩
      rw [hW, hW, hc P L, hb]
      simp
