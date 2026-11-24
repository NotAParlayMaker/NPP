import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Reduction of L-meta-4123:
    Internally proves that girth >= 7 forbids 3-cycles and 4-cycles in H = G - z, and that
    ANY vertex cover T of H with H.edgeSet.ncard + T.card <= t + 1 constructively produces
    the required disjoint monochromatic rectangle partition (X, Y, lab) on Fin (t + 1).
    Splits the remaining pure circuit-size lower bound into NOT-free (monotone) vs has-NOT. -/
theorem PEqualNP.Outside.R_meta_4123_512
    (lb_monotone :
      ∀ (n t : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (g : (Fin n → Bool) → Bool)
        (C : Circuit),
        (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
        (G.neighborSet z).ncard = 3 →
        (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
        H = G.deleteEdges (G.incidenceSet z) →
        (∀ x, g x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
        FanInTwo C →
        C.size ≤ t →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) = g x) →
        (∀ gate ∈ C.gates, gate.op ≠ GateOp.not) →
        ∃ T : Finset (Fin n),
          (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧
          H.edgeSet.ncard + T.card ≤ t + 1)
    (lb_has_not :
      ∀ (n t : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (g : (Fin n → Bool) → Bool)
        (C : Circuit),
        (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
        (G.neighborSet z).ncard = 3 →
        (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
        H = G.deleteEdges (G.incidenceSet z) →
        (∀ x, g x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
        FanInTwo C →
        C.size ≤ t →
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) = g x) →
        (∃ gate ∈ C.gates, gate.op = GateOp.not) →
        ∃ T : Finset (Fin n),
          (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧
          H.edgeSet.ncard + T.card ≤ t + 1) :
    ∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) (x5 : Fin x1) (x6 : (Fin x1 → Bool) → Bool),
      (∀ (x7 : Fin x1), (x3.neighborSet x7).ncard = (0 : ℕ) ∨ (x3.neighborSet x7).ncard = (3 : ℕ)) →
      (x3.neighborSet x5).ncard = (3 : ℕ) →
      (∀ (x9 : Fin x1) (x10 : x3.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
      x4 = x3.deleteEdges (x3.incidenceSet x5) →
      (∀ (x11 : Fin x1 → Bool), x6 x11 = Bool.true ↔
        ∃ (x12 : Fin x1) (x13 : Fin x1), x4.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) →
      PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x2 →
      ∃ (x13 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop)
        (x14 : Fin (x2 + (1 : ℕ)) → Fin x1 → Fin x1 → Prop)
        (x15 : Fin (x2 + (1 : ℕ)) → Fin x1),
        ∀ (x16 x17 x18 x19 : Fin x1),
          x4.Adj x16 x17 →
          (x18 = x19 ∨ x4.Adj x18 x19) →
          (∃! x22 : Fin (x2 + (1 : ℕ)), x13 x22 x16 x17 ∧ x14 x22 x18 x19) ∧
          ∀ (x22 : Fin (x2 + (1 : ℕ))), x13 x22 x16 x17 → x14 x22 x18 x19 →
            (x15 x22 = x16 ∨ x15 x22 = x17) ∧
            ¬((x4.Adj x18 (x15 x22) ∨ x4.Adj x19 (x15 x22)) ∧ x15 x22 ≠ x18 ∧ x15 x22 ≠ x19) := by
  classical
  intro n t G H z g hdeg hdegz hgirth hH hspec hcs
  -- Step 1: Obtain vertex cover T of H with H.edgeSet.ncard + T.card ≤ t + 1
  rcases hcs with ⟨C, hfan, hsz, heval⟩
  have hT_ex : ∃ T : Finset (Fin n),
      (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧ H.edgeSet.ncard + T.card ≤ t + 1 := by
    by_cases hnot : ∃ gate ∈ C.gates, gate.op = GateOp.not
    · exact lb_has_not n t G H z g C hdeg hdegz hgirth hH hspec hfan hsz heval hnot
    · push Not at hnot
      exact lb_monotone n t G H z g C hdeg hdegz hgirth hH hspec hfan hsz heval hnot
  rcases hT_ex with ⟨T, hTcov, hTbound⟩
  -- Step 2: Girth >= 7 forbids 3-cycles and 4-cycles in H
  have hH_sub : ∀ a b, H.Adj a b → G.Adj a b := by
    intro a b hab
    rw [hH] at hab
    exact (SimpleGraph.deleteIncidenceSet_adj.mp hab).1
  have hno3 : ∀ p q r : Fin n, G.Adj p q → G.Adj q r → G.Adj r p → False := by
    intro p q r hpq hqr hrp
    have hpq' : p ≠ q := G.ne_of_adj hpq
    have hqr' : q ≠ r := G.ne_of_adj hqr
    have hrp' : r ≠ p := G.ne_of_adj hrp
    let w : G.Walk p p := .cons hpq (.cons hqr (.cons hrp .nil))
    have hcyc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def]
      refine ⟨⟨?_⟩, by simp [w], ?_⟩
      · simp [w, hpq', hqr', hrp', hpq'.symm, hrp'.symm]
      · simp [w, hqr', hrp', hpq'.symm]
    have hlen := hgirth p w hcyc
    simp [w] at hlen
  have hno4 : ∀ p q r s : Fin n,
      G.Adj p q → G.Adj q r → G.Adj r s → G.Adj s p →
      p ≠ r → q ≠ s → False := by
    intro p q r s hpq hqr hrs hsp hpr hqs
    have hpq' : p ≠ q := G.ne_of_adj hpq
    have hqr' : q ≠ r := G.ne_of_adj hqr
    have hrs' : r ≠ s := G.ne_of_adj hrs
    have hsp' : s ≠ p := G.ne_of_adj hsp
    let w : G.Walk p p := .cons hpq (.cons hqr (.cons hrs (.cons hsp .nil)))
    have hcyc : w.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def]
      refine ⟨⟨?_⟩, by simp [w], ?_⟩
      · simp [w, hpq', hqr', hrs', hsp', hpr, hqs, hpq'.symm, hsp'.symm, hpr.symm]
      · simp [w, hqr', hrs', hsp', hqs, hpq'.symm, hpr.symm]
    have hlen := hgirth p w hcyc
    simp [w] at hlen
  have hno_both : ∀ a b v w : Fin n,
      H.Adj a b → (v = w ∨ H.Adj v w) →
      ((H.Adj v a ∨ H.Adj w a) ∧ a ≠ v ∧ a ≠ w) →
      ¬ ((H.Adj v b ∨ H.Adj w b) ∧ b ≠ v ∧ b ≠ w) := by
    intro a b v w hab hvw ⟨ha_adj, hav, haw⟩ ⟨hb_adj, hbv, hbw⟩
    have habG := hH_sub a b hab
    rcases ha_adj with hva | hwa <;> rcases hb_adj with hvb | hwb
    · exact hno3 v a b (hH_sub _ _ hva) habG (hH_sub _ _ hvb).symm
    · rcases hvw with rfl | hvw'
      · exact hno3 v a b (hH_sub _ _ hva) habG (hH_sub _ _ hwb).symm
      · exact hno4 v a b w (hH_sub _ _ hva) habG (hH_sub _ _ hwb).symm (hH_sub _ _ hvw').symm hbv.symm haw
    · rcases hvw with rfl | hvw'
      · exact hno3 v a b (hH_sub _ _ hwa) habG (hH_sub _ _ hvb).symm
      · exact hno4 w a b v (hH_sub _ _ hwa) habG (hH_sub _ _ hvb).symm (hH_sub _ _ hvw') hbw.symm hav
    · exact hno3 w a b (hH_sub _ _ hwa) habG (hH_sub _ _ hwb).symm
  -- Step 3: Canonical owner in T and other endpoint for each edge e ∈ H.edgeFinset
  have hEcard : H.edgeFinset.card = H.edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hSumBound : T.card + H.edgeFinset.card ≤ t + 1 := by omega
  have howner_ex : ∀ e ∈ H.edgeFinset, ∃ u ∈ T, u ∈ e := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases hTcov a b he with ha | hb
      · exact ⟨a, ha, Sym2.mem_mk_left a b⟩
      · exact ⟨b, hb, Sym2.mem_mk_right a b⟩
  let owner : Sym2 (Fin n) → Fin n := fun e =>
    if he : e ∈ H.edgeFinset then Classical.choose (howner_ex e he) else z
  have howner_mem_T : ∀ e ∈ H.edgeFinset, owner e ∈ T := by
    intro e he; simp only [owner, he, ↓reduceDIte]
    exact (Classical.choose_spec (howner_ex e he)).1
  have howner_mem_e : ∀ e ∈ H.edgeFinset, owner e ∈ e := by
    intro e he; simp only [owner, he, ↓reduceDIte]
    exact (Classical.choose_spec (howner_ex e he)).2
  have hother_ex : ∀ e ∈ H.edgeFinset, ∃ b : Fin n, e = s(owner e, b) ∧ H.Adj (owner e) b := by
    intro e he
    have heSet : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
    have hu : owner e ∈ e := howner_mem_e e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at heSet
      rw [Sym2.mem_iff] at hu
      rcases hu with h1 | h2
      · exact ⟨b, by rw [h1], by rw [h1]; exact heSet⟩
      · exact ⟨a, by rw [h2, Sym2.eq_swap], by rw [h2]; exact heSet.symm⟩
  let other : Sym2 (Fin n) → Fin n := fun e =>
    if he : e ∈ H.edgeFinset then Classical.choose (hother_ex e he) else z
  have hother_eq : ∀ e ∈ H.edgeFinset, e = s(owner e, other e) := by
    intro e he; simp only [other, he, ↓reduceDIte]
    exact (Classical.choose_spec (hother_ex e he)).1
  have hother_adj : ∀ e ∈ H.edgeFinset, H.Adj (owner e) (other e) := by
    intro e he; simp only [other, he, ↓reduceDIte]
    exact (Classical.choose_spec (hother_ex e he)).2
  -- Step 4: Index T and H.edgeFinset into Fin (t + 1)
  let eT : ↥T ≃ Fin T.card := T.equivFin
  let eE : ↥H.edgeFinset ≃ Fin H.edgeFinset.card := H.edgeFinset.equivFin
  let bad : Fin n → Fin n → Fin n → Prop := fun v w u =>
    (H.Adj v u ∨ H.Adj w u) ∧ u ≠ v ∧ u ≠ w
  let X : Fin (t + 1) → Fin n → Fin n → Prop := fun i a b =>
    if h1 : i.val < T.card then
      H.Adj a b ∧ owner s(a, b) = (eT.symm ⟨i.val, h1⟩).val
    else if h2 : i.val < T.card + H.edgeFinset.card then
      H.Adj a b ∧ s(a, b) = (eE.symm ⟨i.val - T.card, by omega⟩).val
    else False
  let Y : Fin (t + 1) → Fin n → Fin n → Prop := fun i v w =>
    if h1 : i.val < T.card then
      ¬ bad v w (eT.symm ⟨i.val, h1⟩).val
    else if h2 : i.val < T.card + H.edgeFinset.card then
      bad v w (owner (eE.symm ⟨i.val - T.card, by omega⟩).val)
    else False
  let lab : Fin (t + 1) → Fin n := fun i =>
    if h1 : i.val < T.card then
      (eT.symm ⟨i.val, h1⟩).val
    else if h2 : i.val < T.card + H.edgeFinset.card then
      other (eE.symm ⟨i.val - T.card, by omega⟩).val
    else z
  refine ⟨X, Y, lab, ?_⟩
  intro a b v w hab hvw
  have he_mem : s(a, b) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab
  let u0 := owner s(a, b)
  have hu0_T : u0 ∈ T := howner_mem_T s(a, b) he_mem
  have hu0_e : u0 ∈ s(a, b) := howner_mem_e s(a, b) he_mem
  have hb0_eq : s(a, b) = s(u0, other s(a, b)) := hother_eq s(a, b) he_mem
  have hb0_adj : H.Adj u0 (other s(a, b)) := hother_adj s(a, b) he_mem
  let iT : Fin (t + 1) := ⟨(eT ⟨u0, hu0_T⟩).val, by have := (eT ⟨u0, hu0_T⟩).isLt; omega⟩
  let iE : Fin (t + 1) := ⟨T.card + (eE ⟨s(a, b), he_mem⟩).val, by have := (eE ⟨s(a, b), he_mem⟩).isLt; omega⟩
  have hX_only : ∀ i : Fin (t + 1), X i a b → i = iT ∨ i = iE := by
    intro i hXi
    dsimp only [X] at hXi
    split_ifs at hXi with h1 h2
    · left
      apply Fin.ext
      have hsym := hXi.2
      have hsub : (⟨u0, hu0_T⟩ : ↥T) = eT.symm ⟨i.val, h1⟩ := Subtype.ext hsym
      have := congrArg eT hsub
      rw [Equiv.apply_symm_apply] at this
      exact (congrArg Fin.val this).symm
    · right
      apply Fin.ext
      have hsym := hXi.2
      have hsub : (⟨s(a, b), he_mem⟩ : ↥H.edgeFinset) = eE.symm ⟨i.val - T.card, by omega⟩ := Subtype.ext hsym
      have := congrArg eE hsub
      rw [Equiv.apply_symm_apply] at this
      have hval := congrArg Fin.val this
      dsimp only at hval
      dsimp only [iE]
      omega
  have hXiT : X iT a b := by
    have h1 : iT.val < T.card := (eT ⟨u0, hu0_T⟩).isLt
    simp only [X, h1, ↓reduceDIte, hab, true_and]
    change u0 = (eT.symm (eT ⟨u0, hu0_T⟩)).val
    rw [Equiv.symm_apply_apply]
  have hYiT : Y iT v w ↔ ¬ bad v w u0 := by
    have h1 : iT.val < T.card := (eT ⟨u0, hu0_T⟩).isLt
    simp only [Y, h1, ↓reduceDIte]
    have hEq : (eT.symm ⟨iT.val, h1⟩).val = u0 := by
      change (eT.symm (eT ⟨u0, hu0_T⟩)).val = u0
      rw [Equiv.symm_apply_apply]
    rw [hEq]
  have hXiE : X iE a b := by
    have h1 : ¬ iE.val < T.card := by dsimp only [iE]; omega
    have h2 : iE.val < T.card + H.edgeFinset.card := by
      have := (eE ⟨s(a, b), he_mem⟩).isLt; dsimp only [iE]; omega
    simp only [X, h1, h2, ↓reduceDIte, hab, true_and]
    have hidx : (⟨iE.val - T.card, by omega⟩ : Fin H.edgeFinset.card) = eE ⟨s(a, b), he_mem⟩ := by
      apply Fin.ext; dsimp only [iE]; omega
    rw [hidx, Equiv.symm_apply_apply]
  have hYiE : Y iE v w ↔ bad v w u0 := by
    have h1 : ¬ iE.val < T.card := by dsimp only [iE]; omega
    have h2 : iE.val < T.card + H.edgeFinset.card := by
      have := (eE ⟨s(a, b), he_mem⟩).isLt; dsimp only [iE]; omega
    simp only [Y, h1, h2, ↓reduceDIte]
    have hidx : (⟨iE.val - T.card, by omega⟩ : Fin H.edgeFinset.card) = eE ⟨s(a, b), he_mem⟩ := by
      apply Fin.ext; dsimp only [iE]; omega
    rw [hidx, Equiv.symm_apply_apply]
  constructor
  · by_cases hbad : bad v w u0
    · refine ⟨iE, ⟨hXiE, hYiE.mpr hbad⟩, ?_⟩
      intro j ⟨hXj, hYj⟩
      rcases hX_only j hXj with rfl | rfl
      · exact (hYiT.mp hYj hbad).elim
      · rfl
    · refine ⟨iT, ⟨hXiT, hYiT.mpr hbad⟩, ?_⟩
      intro j ⟨hXj, hYj⟩
      rcases hX_only j hXj with rfl | rfl
      · rfl
      · exact (hbad (hYiE.mp hYj)).elim
  · intro j hXj hYj
    rcases hX_only j hXj with rfl | rfl
    · have h1 : iT.val < T.card := (eT ⟨u0, hu0_T⟩).isLt
      have hlab : lab iT = u0 := by
        simp only [lab, h1, ↓reduceDIte]
        change (eT.symm (eT ⟨u0, hu0_T⟩)).val = u0
        rw [Equiv.symm_apply_apply]
      rw [hlab]
      exact ⟨Sym2.mem_iff.mp hu0_e, hYiT.mp hYj⟩
    · have h1 : ¬ iE.val < T.card := by dsimp only [iE]; omega
      have h2 : iE.val < T.card + H.edgeFinset.card := by
        have := (eE ⟨s(a, b), he_mem⟩).isLt; dsimp only [iE]; omega
      have hlab : lab iE = other s(a, b) := by
        simp only [lab, h1, h2, ↓reduceDIte]
        have hidx : (⟨iE.val - T.card, by omega⟩ : Fin H.edgeFinset.card) = eE ⟨s(a, b), he_mem⟩ := by
          apply Fin.ext; dsimp only [iE]; omega
        rw [hidx, Equiv.symm_apply_apply]
      rw [hlab]
      have hmem : other s(a, b) ∈ s(a, b) := by
        have h := Sym2.mem_mk_right u0 (other s(a, b))
        rwa [← hb0_eq] at h
      exact ⟨Sym2.mem_iff.mp hmem, hno_both u0 (other s(a, b)) v w hb0_adj hvw (hYiE.mp hYj)⟩
