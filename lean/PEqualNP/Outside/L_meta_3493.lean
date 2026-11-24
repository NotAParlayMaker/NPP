import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3493

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def dg : Gate := ⟨GateOp.or, []⟩

def val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD w false

theorem wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) o).wires x = (Circuit.mk gs o).wires x ++
      [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_len (gs : List Gate) (o : ℕ) (x : List Bool) :
    ((Circuit.mk gs o).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => rw [wires_snoc]; simp [ih]; omega

theorem val_snoc_old {n : ℕ} {gs : List Gate} {g : Gate} {x : Fin n → Bool} {w : ℕ}
    (h : w < n + gs.length) : val n (gs ++ [g]) x w = val n gs x w := by
  unfold val
  rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_len]; simpa using h)]

theorem val_snoc_new {n : ℕ} {gs : List Gate} {g : Gate} {x : Fin n → Bool} :
    val n (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map (val n gs x)) := by
  unfold val
  have hl := wires_len gs 0 (List.ofFn x)
  rw [wires_snoc, List.getD_append_right _ _ _ _ (by rw [hl]; simp)]
  simp [hl]

theorem val_append_old {n : ℕ} {gs : List Gate} (ext : List Gate) {x : Fin n → Bool} {w : ℕ}
    (h : w < n + gs.length) : val n (gs ++ ext) x w = val n gs x w := by
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext g ih =>
    rw [← List.append_assoc, val_snoc_old (by simp; omega), ih]

theorem val_input {n : ℕ} {x : Fin n → Bool} {w : ℕ} (h : w < n) :
    val n [] x w = x ⟨w, h⟩ := by
  simp [val, Circuit.wires, List.getD_eq_getElem?_getD, h]

theorem gl {gs ext : List Gate} {j : ℕ} (h : j < gs.length) :
    (gs ++ ext).getD j dg = gs.getD j dg := List.getD_append _ _ _ _ h

theorem gr {gs : List Gate} {g : Gate} : (gs ++ [g]).getD gs.length dg = g := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

def W (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    ∀ j < gs.length, ∀ i ∈ (gs.getD j dg).inputs, i < n + j

theorem W_snoc {n : ℕ} {gs : List Gate} {g : Gate} (h : W n gs)
    (h1 : g.op = GateOp.and ∨ g.op = GateOp.or) (h2 : g.inputs.length = 2)
    (h3 : ∀ i ∈ g.inputs, i < n + gs.length) : W n (gs ++ [g]) := by
  constructor
  · intro g' hg'
    rcases List.mem_append.1 hg' with hg' | hg'
    · exact h.1 g' hg'
    · rw [List.mem_singleton.1 hg']; exact ⟨h1, h2⟩
  · intro j hj i hi
    by_cases hlt : j < gs.length
    · rw [gl hlt] at hi; exact h.2 j hlt i hi
    · have : j = gs.length := by simp at hj; omega
      subst this
      rw [gr] at hi; exact h3 i hi

def Closed (n : ℕ) (gs : List Gate) (b : ℕ → Prop) (S : Finset ℕ) : Prop :=
  ∀ w ∈ S, b w ∨ ∃ j < gs.length, w = n + j ∧ (gs.getD j dg).op = GateOp.or ∧
    ∀ i ∈ (gs.getD j dg).inputs, i ∈ S

theorem closed_mono {n : ℕ} {gs : List Gate} {b : ℕ → Prop} {S : Finset ℕ} (ext : List Gate)
    (h : Closed n gs b S) : Closed n (gs ++ ext) b S := by
  intro w hw
  rcases h w hw with h | ⟨j, hj, e, ho, hi⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, by simp; omega, e, by rwa [gl hj], by rwa [gl hj]⟩

theorem closed_ins {n : ℕ} {gs : List Gate} {b : ℕ → Prop} {S : Finset ℕ} {a c : ℕ}
    (h : Closed n gs b S) (ha : a ∈ S) (hc : c ∈ S) :
    Closed n (gs ++ [⟨GateOp.or, [a, c]⟩]) b (insert (n + gs.length) S) := by
  intro w hw
  rcases Finset.mem_insert.1 hw with rfl | hw
  · refine Or.inr ⟨gs.length, by simp, rfl, by rw [gr], ?_⟩
    rw [gr]
    intro i hi
    simp at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_insert_of_mem ha
    · exact Finset.mem_insert_of_mem hc
  · rcases closed_mono [⟨GateOp.or, [a, c]⟩] h w hw with h | ⟨j, hj, e, ho, hi⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, e, ho, fun i h => Finset.mem_insert_of_mem (hi i h)⟩

def AndOK (gs : List Gate) (P L : Finset ℕ) : Prop :=
  ∀ j < gs.length, (gs.getD j dg).op = GateOp.and →
    ∃ a b, (gs.getD j dg).inputs = [a, b] ∧ a ∈ L ∧ b ∈ P

theorem andok_snoc {gs : List Gate} {g : Gate} {P L P' L' : Finset ℕ} (h : AndOK gs P L)
    (hP : P ⊆ P') (hL : L ⊆ L')
    (hg : g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧ a ∈ L' ∧ b ∈ P') :
    AndOK (gs ++ [g]) P' L' := by
  intro j hj hop
  by_cases hlt : j < gs.length
  · rw [gl hlt] at hop ⊢
    obtain ⟨a, b, e, ha, hb⟩ := h j hlt hop
    exact ⟨a, b, e, hL ha, hP hb⟩
  · have : j = gs.length := by simp at hj; omega
    subst this
    rw [gr] at hop ⊢
    exact hg hop

theorem andok_ext {gs : List Gate} {P L P' L' : Finset ℕ} (h : AndOK gs P L)
    (hP : P ⊆ P') (hL : L ⊆ L') : ∀ ext : List Gate, (∀ g ∈ ext, g.op = GateOp.or) →
    AndOK (gs ++ ext) P' L' := by
  intro ext
  induction ext using List.reverseRecOn with
  | nil =>
    intro _ j hj hop
    simp at hj hop ⊢
    obtain ⟨a, b, e, ha, hb⟩ := h j hj hop
    exact ⟨a, b, e, hL ha, hP hb⟩
  | append_singleton ext g ih =>
    intro hor
    rw [← List.append_assoc]
    refine andok_snoc (ih fun g hg => hor g (by simp [hg])) (le_refl _) (le_refl _) ?_
    intro hop
    rw [hor g (by simp)] at hop
    cases hop

theorem chain (n : ℕ) (b : ℕ → Prop) : ∀ (ws : List ℕ) (gs : List Gate) (S : Finset ℕ) (w0 : ℕ),
    W n gs → Closed n gs b S → w0 ∈ S → w0 < n + gs.length →
    (∀ w ∈ ws, w ∈ S ∧ w < n + gs.length) →
    ∃ (ext : List Gate) (S' : Finset ℕ) (w : ℕ), S ⊆ S' ∧ ext.length = ws.length ∧
      (∀ g ∈ ext, g.op = GateOp.or) ∧ W n (gs ++ ext) ∧ Closed n (gs ++ ext) b S' ∧ w ∈ S' ∧
      w < n + (gs ++ ext).length ∧
      ∀ x : Fin n → Bool, val n (gs ++ ext) x w = (val n gs x w0 || ws.any (val n gs x)) := by
  intro ws
  induction ws with
  | nil =>
    intro gs S w0 hW hC h0 hlt _
    exact ⟨[], S, w0, le_refl _, rfl, by simp, by simpa using hW, by simpa using hC, h0,
      by simpa using hlt, by simp⟩
  | cons a ws ih =>
    intro gs S w0 hW hC h0 hlt hws
    have ha := hws a (by simp)
    obtain ⟨ext, S', w, hsub, hlen, hor, hW', hC', hw, hlt', hv⟩ :=
      ih (gs ++ [⟨GateOp.or, [w0, a]⟩]) (insert (n + gs.length) S) (n + gs.length)
        (W_snoc hW (Or.inr rfl) rfl (by
          intro i hi; simp at hi; rcases hi with rfl | rfl
          · exact hlt
          · exact ha.2))
        (closed_ins hC h0 ha.1) (Finset.mem_insert_self _ _) (by simp)
        (fun w hw => ⟨Finset.mem_insert_of_mem (hws w (by simp [hw])).1, by
          have := (hws w (by simp [hw])).2; simp; omega⟩)
    have e : gs ++ (⟨GateOp.or, [w0, a]⟩ :: ext) = gs ++ [⟨GateOp.or, [w0, a]⟩] ++ ext := by simp
    refine ⟨⟨GateOp.or, [w0, a]⟩ :: ext, S', w, fun y hy => hsub (Finset.mem_insert_of_mem hy),
      by simp [hlen], ?_, by rw [e]; exact hW', by rw [e]; exact hC', hw, by rw [e]; exact hlt', ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · rfl
      · exact hor g hg
    · intro x
      rw [e, hv x, val_snoc_new]
      have hany : ws.any (val n (gs ++ [⟨GateOp.or, [w0, a]⟩]) x) = ws.any (val n gs x) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        constructor
        · rintro ⟨y, hy, hy2⟩
          exact ⟨y, hy, by rwa [val_snoc_old (hws y (by simp [hy])).2] at hy2⟩
        · rintro ⟨y, hy, hy2⟩
          exact ⟨y, hy, by rwa [val_snoc_old (hws y (by simp [hy])).2]⟩
      rw [hany]
      simp [GateOp.eval, Bool.or_assoc]

theorem val_in {n : ℕ} (gs : List Gate) {x : Fin n → Bool} {w : ℕ} (h : w < n) :
    val n gs x w = val n [] x w := by
  simpa using val_append_old (gs := []) gs (x := x) (w := w) (by simpa using h)

theorem any_cg {l : List ℕ} {f g : ℕ → Bool} (h : ∀ y ∈ l, f y = g y) : l.any f = l.any g := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hy2⟩; exact ⟨y, hy, by rwa [h y hy] at hy2⟩
  · rintro ⟨y, hy, hy2⟩; exact ⟨y, hy, by rwa [h y hy]⟩

theorem star_sem {n : ℕ} {gs ext : List Gate} {x : Fin n → Bool} {w w0 u : ℕ} {ws : List ℕ}
    {Nu : Finset ℕ} (hv : val n (gs ++ ext) x w = (val n gs x w0 || ws.any (val n gs x)))
    (hm : ∀ y, y ∈ Nu ↔ y = w0 ∨ y ∈ ws) (hN : ∀ y ∈ Nu, y < n) (hu : u < n) :
    (val n (gs ++ ext) x w = true ∧ val n (gs ++ ext) x u = true) ↔
      (val n [] x u = true ∧ ∃ y ∈ Nu, val n [] x y = true) := by
  rw [hv, val_in (gs ++ ext) hu, and_comm]
  apply and_congr Iff.rfl
  rw [Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (h | ⟨y, hy, h⟩)
    · exact ⟨w0, (hm w0).2 (Or.inl rfl), by rwa [val_in gs (hN w0 ((hm w0).2 (Or.inl rfl)))] at h⟩
    · exact ⟨y, (hm y).2 (Or.inr hy), by rwa [val_in gs (hN y ((hm y).2 (Or.inr hy)))] at h⟩
  · rintro ⟨y, hy, h⟩
    rcases (hm y).1 hy with rfl | hy'
    · exact Or.inl (by rwa [val_in gs (hN y hy)])
    · exact Or.inr ⟨y, hy', by rwa [val_in gs (hN y hy)]⟩

theorem build (x1 x2 : ℕ) (N : ℕ → Finset ℕ) : ∀ U : Finset ℕ,
    (∀ u ∈ U, (N u).Nonempty ∧ ((u < x1 ∧ ∀ w ∈ N u, x1 ≤ w ∧ w < x1 + x2) ∨
      (x1 ≤ u ∧ u < x1 + x2 ∧ ∀ w ∈ N u, w < x1))) →
    ∃ (gs : List Gate) (P L : Finset ℕ) (outs : List ℕ), W (x1 + x2) gs ∧
      Closed (x1 + x2) gs (fun w => w < x1) P ∧
      Closed (x1 + x2) gs (fun w => x1 ≤ w ∧ w < x1 + x2) L ∧ AndOK gs P L ∧
      Finset.range x1 ⊆ P ∧ Finset.Ico x1 (x1 + x2) ⊆ L ∧
      gs.length = ∑ u ∈ U, (N u).card ∧ outs.length = U.card ∧
      (∀ o ∈ outs, o < x1 + x2 + gs.length) ∧
      ∀ x : Fin (x1 + x2) → Bool, outs.any (val (x1 + x2) gs x) =
        decide (∃ u ∈ U, val (x1 + x2) [] x u = true ∧ ∃ w ∈ N u, val (x1 + x2) [] x w = true) := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨[], Finset.range x1, Finset.Ico x1 (x1 + x2), [], ⟨by simp, by simp⟩, ?_, ?_, ?_,
      le_refl _, le_refl _, by simp, by simp, by simp, by simp⟩
    · intro w hw; exact Or.inl (by simpa using hw)
    · intro w hw; exact Or.inl (by simpa using hw)
    · intro j hj; simp at hj
  | insert u U hu ih =>
    intro h
    obtain ⟨gs, P, L, outs, hW, hCP, hCL, hA, hP, hL, hlen, hol, hob, hsem⟩ :=
      ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    obtain ⟨hne, hside⟩ := h u (Finset.mem_insert_self _ _)
    obtain ⟨w0, ws, hl⟩ : ∃ w0 ws, (N u).toList = w0 :: ws := by
      cases hh : (N u).toList with
      | nil => rw [Finset.toList_eq_nil] at hh; rw [hh] at hne; simp at hne
      | cons a l => exact ⟨a, l, rfl⟩
    have hm : ∀ y, y ∈ N u ↔ y = w0 ∨ y ∈ ws := by
      intro y; rw [← Finset.mem_toList, hl, List.mem_cons]
    have hcard : (N u).card = ws.length + 1 := by rw [← Finset.length_toList, hl]; simp
    have hNn : ∀ y ∈ N u, y < x1 + x2 := by
      intro y hy
      rcases hside with ⟨_, h2⟩ | ⟨_, _, h2⟩
      · exact (h2 y hy).2
      · have := h2 y hy; omega
    have hun : u < x1 + x2 := by
      rcases hside with ⟨h1, _⟩ | ⟨_, h1, _⟩
      · omega
      · exact h1
    have hfin : ∀ (ext : List Gate) (w a c : ℕ) (x : Fin (x1 + x2) → Bool),
        ((a = w ∧ c = u) ∨ (a = u ∧ c = w)) → ext.length = ws.length →
        val (x1 + x2) (gs ++ ext) x w = (val (x1 + x2) gs x w0 || ws.any (val (x1 + x2) gs x)) →
        ((x1 + x2 + (gs ++ ext).length) :: outs).any
          (val (x1 + x2) (gs ++ ext ++ [⟨GateOp.and, [a, c]⟩]) x) =
        decide (∃ v ∈ insert u U, val (x1 + x2) [] x v = true ∧
          ∃ w ∈ N v, val (x1 + x2) [] x w = true) := by
      intro ext w a c x hac hel hv
      have hold : outs.any (val (x1 + x2) (gs ++ ext ++ [⟨GateOp.and, [a, c]⟩]) x) =
          outs.any (val (x1 + x2) gs x) := by
        apply any_cg
        intro y hy
        rw [List.append_assoc, val_append_old _ (hob y hy)]
      have hs := star_sem hv hm hNn hun
      rw [List.any_cons, hold, hsem x, val_snoc_new, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.exists_mem_insert]
      apply or_congr _ Iff.rfl
      rw [← hs]
      rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [GateOp.eval]
      · simp [GateOp.eval, and_comm]
    rcases hside with ⟨hu1, hN1⟩ | ⟨hu1, hu2, hN1⟩
    · obtain ⟨ext, L', w, hsub, hel, hor, hW', hC', hw, hlt, hv⟩ :=
        chain (x1 + x2) (fun w => x1 ≤ w ∧ w < x1 + x2) ws gs L w0 hW hCL
          (hL (Finset.mem_Ico.2 (hN1 w0 ((hm w0).2 (Or.inl rfl))))) (by
            have := hNn w0 ((hm w0).2 (Or.inl rfl)); omega)
          (fun y hy => ⟨hL (Finset.mem_Ico.2 (hN1 y ((hm y).2 (Or.inr hy)))), by
            have := hNn y ((hm y).2 (Or.inr hy)); omega⟩)
      refine ⟨gs ++ ext ++ [⟨GateOp.and, [w, u]⟩], P, L', (x1 + x2 + (gs ++ ext).length) :: outs,
        W_snoc hW' (Or.inl rfl) rfl ?_, closed_mono _ (closed_mono _ hCP), closed_mono _ hC',
        andok_snoc (andok_ext hA (le_refl _) hsub ext hor) (le_refl _) (le_refl _)
          (fun _ => ⟨w, u, rfl, hw, hP (Finset.mem_range.2 hu1)⟩),
        hP, hL.trans hsub, ?_, ?_, ?_, fun x => hfin ext w w u x (Or.inl ⟨rfl, rfl⟩) hel (hv x)⟩
      · intro i hi; simp at hi; rcases hi with rfl | rfl
        · exact hlt
        · omega
      · rw [Finset.sum_insert hu, hcard, ← hlen]; simp [hel]; omega
      · simp [Finset.card_insert_of_notMem hu, hol]
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · simp
        · have := hob o ho; simp; omega
    · obtain ⟨ext, P', w, hsub, hel, hor, hW', hC', hw, hlt, hv⟩ :=
        chain (x1 + x2) (fun w => w < x1) ws gs P w0 hW hCP
          (hP (Finset.mem_range.2 (hN1 w0 ((hm w0).2 (Or.inl rfl))))) (by
            have := hNn w0 ((hm w0).2 (Or.inl rfl)); omega)
          (fun y hy => ⟨hP (Finset.mem_range.2 (hN1 y ((hm y).2 (Or.inr hy)))), by
            have := hNn y ((hm y).2 (Or.inr hy)); omega⟩)
      refine ⟨gs ++ ext ++ [⟨GateOp.and, [u, w]⟩], P', L, (x1 + x2 + (gs ++ ext).length) :: outs,
        W_snoc hW' (Or.inl rfl) rfl ?_, closed_mono _ hC', closed_mono _ (closed_mono _ hCL),
        andok_snoc (andok_ext hA hsub (le_refl _) ext hor) (le_refl _) (le_refl _)
          (fun _ => ⟨u, w, rfl, hL (Finset.mem_Ico.2 ⟨hu1, hu2⟩), hw⟩),
        hP.trans hsub, hL, ?_, ?_, ?_, fun x => hfin ext w u w x (Or.inr ⟨rfl, rfl⟩) hel (hv x)⟩
      · intro i hi; simp at hi; rcases hi with rfl | rfl
        · omega
        · exact hlt
      · rw [Finset.sum_insert hu, hcard, ← hlen]; simp [hel]; omega
      · simp [Finset.card_insert_of_notMem hu, hol]
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · simp
        · have := hob o ho; simp; omega

end PEqualNP.Outside.L_meta_3493

theorem PEqualNP.Outside.L_meta_3493 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : Finset (Fin (x1 + x2))), (∀ (x6 : Fin x1) (x7 : Fin x2), x3 x6 x7 → Fin.castAdd x2 x6 ∈ x5 ∨ Fin.natAdd x1 x7 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x7.size ≤ (PEqualNP.ReadTwo.incid x3).card + x5.card - (1 : ℕ) ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x1 + x2 ∨ ∃ x12 < x7.gates.length, x10 = x1 + x2 + x12 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).inputs = [x13, x14] ∧ x13 ∈ x9 ∧ x14 ∈ x8 := by
  intro x1 x2 I inst T hcov
  classical
  have hE : ∀ e : Fin x1 × Fin x2, e ∈ PEqualNP.ReadTwo.incid I ↔ I e.1 e.2 := by
    intro e; simp [PEqualNP.ReadTwo.incid]
  obtain ⟨f, hf⟩ : ∃ f : Fin x1 × Fin x2 → ℕ, ∀ e, f e =
      if Fin.castAdd x2 e.1 ∈ T then e.1.val else x1 + e.2.val := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin x1 × Fin x2 → ℕ, ∀ e, g e =
      if Fin.castAdd x2 e.1 ∈ T then x1 + e.2.val else e.1.val := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → Finset ℕ, ∀ u, N u =
      ((PEqualNP.ReadTwo.incid I).filter (fun e => f e = u)).image g := ⟨_, fun _ => rfl⟩
  obtain ⟨gs, P, L, outs, hW, hCP, hCL, hA, hP, hL, hlen, hol, hob, hsem⟩ :=
    PEqualNP.Outside.L_meta_3493.build x1 x2 N ((PEqualNP.ReadTwo.incid I).image f) (by
      intro u hu
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hu
      refine ⟨⟨g e, by rw [hNdef]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨he, rfl⟩)⟩, ?_⟩
      have b1 := e.1.isLt
      have b2 := e.2.isLt
      by_cases hT : Fin.castAdd x2 e.1 ∈ T
      · left
        refine ⟨by rw [hf, ite_eq_left hT]; exact b1, ?_⟩
        intro w hw
        rw [hNdef] at hw
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hw
        have h3 := (Finset.mem_filter.1 he').2
        have c1 := e'.1.isLt
        have c2 := e'.2.isLt
        rw [hf, hf, ite_eq_left hT] at h3
        rw [hg]
        split_ifs at h3 ⊢ <;> omega
      · right
        refine ⟨by rw [hf, ite_eq_right hT]; omega, by rw [hf, ite_eq_right hT]; omega, ?_⟩
        intro w hw
        rw [hNdef] at hw
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hw
        have h3 := (Finset.mem_filter.1 he').2
        have c1 := e'.1.isLt
        have c2 := e'.2.isLt
        rw [hf, hf, ite_eq_right hT] at h3
        rw [hg]
        split_ifs at h3 ⊢ <;> omega)
  have hcount : gs.length = (PEqualNP.ReadTwo.incid I).card := by
    rw [hlen, Finset.card_eq_sum_card_image f (PEqualNP.ReadTwo.incid I)]
    apply Finset.sum_congr rfl
    intro u _
    rw [hNdef]
    apply Finset.card_image_of_injOn
    intro e1 h1 e2 h2 h12
    have a1 := (Finset.mem_filter.1 (Finset.mem_coe.1 h1)).2
    have a2 := (Finset.mem_filter.1 (Finset.mem_coe.1 h2)).2
    have b1 := e1.1.isLt
    have b2 := e2.1.isLt
    rw [hf] at a1 a2
    rw [hg, hg] at h12
    apply Prod.ext <;> apply Fin.ext <;> split_ifs at a1 a2 h12 <;> omega
  have hUT : ((PEqualNP.ReadTwo.incid I).image f).card ≤ T.card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := fun t : Fin (x1 + x2) => t.val))
    intro u hu
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hu
    by_cases hT : Fin.castAdd x2 e.1 ∈ T
    · exact Finset.mem_image.2 ⟨_, hT, by rw [hf, ite_eq_left hT]; rfl⟩
    · rcases hcov e.1 e.2 ((hE e).1 he) with h | h
      · exact absurd h hT
      · exact Finset.mem_image.2 ⟨_, h, by rw [hf, ite_eq_right hT]; rfl⟩
  have hbr : ∀ x : Fin (x1 + x2) → Bool,
      (∃ u ∈ (PEqualNP.ReadTwo.incid I).image f, PEqualNP.Outside.L_meta_3493.val (x1 + x2) [] x u = true ∧
        ∃ w ∈ N u, PEqualNP.Outside.L_meta_3493.val (x1 + x2) [] x w = true) ↔
      ∃ (p : Fin x1) (l : Fin x2), I p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true := by
    intro x
    have hp : ∀ p : Fin x1, PEqualNP.Outside.L_meta_3493.val (x1 + x2) [] x p.val = x (Fin.castAdd x2 p) :=
      fun p => (PEqualNP.Outside.L_meta_3493.val_input (by have := p.isLt; omega)).trans (congrArg x (Fin.ext rfl))
    have hl : ∀ l : Fin x2, PEqualNP.Outside.L_meta_3493.val (x1 + x2) [] x (x1 + l.val) = x (Fin.natAdd x1 l) :=
      fun l => (PEqualNP.Outside.L_meta_3493.val_input (by have := l.isLt; omega)).trans (congrArg x (Fin.ext rfl))
    constructor
    · rintro ⟨u, _, h1, w, hw, h2⟩
      rw [hNdef] at hw
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨he1, rfl⟩ := Finset.mem_filter.1 he
      refine ⟨e.1, e.2, (hE e).1 he1, ?_⟩
      rw [hf] at h1
      rw [hg] at h2
      by_cases hT : Fin.castAdd x2 e.1 ∈ T
      · rw [ite_eq_left hT] at h1 h2; rw [hp] at h1; rw [hl] at h2; exact ⟨h1, h2⟩
      · rw [ite_eq_right hT] at h1 h2; rw [hl] at h1; rw [hp] at h2; exact ⟨h2, h1⟩
    · rintro ⟨p, l, hI, hxp, hxl⟩
      refine ⟨f (p, l), Finset.mem_image_of_mem _ ((hE (p, l)).2 hI), ?_, g (p, l), ?_, ?_⟩
      · rw [hf]; split_ifs
        · rw [hp]; exact hxp
        · rw [hl]; exact hxl
      · rw [hNdef]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨(hE (p, l)).2 hI, rfl⟩)
      · rw [hg]; split_ifs
        · rw [hl]; exact hxl
        · rw [hp]; exact hxp
  cases outs with
  | nil =>
    have hU0 : ((PEqualNP.ReadTwo.incid I).image f) = ∅ := by
      rw [← Finset.card_eq_zero, ← hol]; rfl
    have hg0 : gs = [] := by
      rw [← List.length_eq_zero_iff, hlen, hU0]; simp
    subst hg0
    refine ⟨⟨[], x1 + x2⟩, P, L, ⟨fun g hg => (hW.1 g hg).1, hW.2, fun g hg => (hW.1 g hg).2⟩,
      ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], hCP, hCL, hA⟩
    intro x
    have h1 := hsem x
    simp only [hbr x] at h1
    rw [← h1]
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires]
  | cons o0 rest =>
    obtain ⟨ext, S', w, _, hel, hor, hW', _, _, _, hv⟩ :=
      PEqualNP.Outside.L_meta_3493.chain (x1 + x2) (fun _ => True) rest gs
        (Finset.range (x1 + x2 + gs.length)) o0 hW (fun _ _ => Or.inl trivial)
        (Finset.mem_range.2 (hob o0 (by simp))) (hob o0 (by simp))
        (fun y hy => ⟨Finset.mem_range.2 (hob y (by simp [hy])), hob y (by simp [hy])⟩)
    refine ⟨⟨gs ++ ext, w⟩, P, L, ⟨fun g hg => (hW'.1 g hg).1, hW'.2, fun g hg => (hW'.1 g hg).2⟩,
      ?_, ?_, PEqualNP.Outside.L_meta_3493.closed_mono ext hCP,
      PEqualNP.Outside.L_meta_3493.closed_mono ext hCL,
      PEqualNP.Outside.L_meta_3493.andok_ext hA (le_refl _) (le_refl _) ext hor⟩
    · intro x
      have h1 := hsem x
      simp only [hbr x] at h1
      rw [← h1]
      exact hv x
    · show (gs ++ ext).length ≤ _
      rw [List.length_append, hel, hcount]
      simp at hol
      omega
