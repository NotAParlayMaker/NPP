import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2355

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl step acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
    omega

lemma foldl_getD_lt (gs : List Gate) (acc : List Bool) (k : ℕ) (hk : k < acc.length) :
    (gs.foldl step acc).getD k false = acc.getD k false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (step acc g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [ih (step acc g) hk']
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma eval_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  unfold Circuit.wires
  change (C.gates.foldl step (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hlen : w < (List.ofFn x).length := by simp [hw]
  rw [foldl_getD_lt C.gates (List.ofFn x) w hlen, List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]

lemma eval_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hback : ∀ a ∈ (gateAt C j).inputs, a < n + j) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun a => (C.wires (List.ofFn x)).getD a false) := by
  have hgate : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [hj]
  rw [hgate] at hback ⊢
  unfold Circuit.wires
  change (C.gates.foldl step (List.ofFn x)).getD (n + j) false =
    C.gates[j].op.eval (C.gates[j].inputs.map fun a => (C.gates.foldl step (List.ofFn x)).getD a false)
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) :=
      (List.cons_getElem_drop_succ (h := hj)).symm
    rw [← h2, h1]
  let acc := (C.gates.take j).foldl step (List.ofFn x)
  have hacc_len : acc.length = n + j := by
    dsimp [acc]
    rw [foldl_length]
    simp [Nat.le_of_lt hj]
  have hfold : C.gates.foldl step (List.ofFn x) = (C.gates.drop (j + 1)).foldl step (step acc C.gates[j]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hstep_len : n + j < (step acc C.gates[j]).length := by
    simp only [step, List.length_append, List.length_singleton, hacc_len]
    omega
  rw [hfold, foldl_getD_lt _ _ (n + j) hstep_len]
  have hlhs : (step acc C.gates[j]).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun a => acc.getD a false) := by
    simp only [step, List.getD_eq_getElem?_getD, ← hacc_len, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro a ha
  have ha_lt : a < acc.length := by rw [hacc_len]; exact hback a ha
  have ha_lt2 : a < (step acc C.gates[j]).length := by
    simp only [step, List.length_append, List.length_singleton]
    omega
  rw [foldl_getD_lt _ _ a ha_lt2]
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left ha_lt]

lemma readsBack_gate (n : ℕ) (C : Circuit) (hreads : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    ∀ a ∈ (gateAt C j).inputs, a < n + j := by
  intro a ha
  exact hreads j hj a ha

lemma eval_or_true_up (n : ℕ) (C : Circuit) (hreads : ReadsBack n C) (x : Fin n → Bool)
    {a b : ℕ}
    (hR : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b)
    (ha : (C.wires (List.ofFn x)).getD a false = true) :
    (C.wires (List.ofFn x)).getD b false = true := by
  induction hR with
  | refl => exact ha
  | tail _ hstep ih =>
    obtain ⟨_, rj, rfl, hrj, hor, hmem⟩ := hstep
    rw [eval_gate n C x rj hrj (readsBack_gate n C hreads rj hrj), hor]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    exact ⟨true, ⟨_, hmem, ih⟩, rfl⟩

lemma eval_and_true (n : ℕ) (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (h0 : (C.wires (List.ofFn x)).getD ((gateAt C j).inputs.getD 0 0) false = true)
    (h1 : (C.wires (List.ofFn x)).getD ((gateAt C j).inputs.getD 1 0) false = true) :
    (C.wires (List.ofFn x)).getD (n + j) false = true := by
  have hgate : gateAt C j = C.gates[j] := by unfold gateAt; simp [hj]
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [hgate]
    exact hao.2.2 C.gates[j] (List.getElem_mem hj)
  cases hinp : (gateAt C j).inputs with
  | nil => rw [hinp] at hlen; simp at hlen
  | cons a rest =>
    cases rest with
    | nil => rw [hinp] at hlen; simp at hlen
    | cons b rest2 =>
      cases rest2 with
      | nil =>
        rw [hinp] at h0 h1
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
        rw [eval_gate n C x j hj (readsBack_gate n C hao.2.1 j hj), hand, hinp]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h0, h1, Bool.and_true]
      | cons c rest3 => rw [hinp] at hlen; simp at hlen

end PEqualNP.Outside.L_meta_2355

theorem PEqualNP.Outside.L_meta_2355 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l := by
  intro n N M pw lw I C hao _ _ _ hpw hlw hsound R hR T hT p l L _ hL
  subst hR hT
  obtain ⟨⟨j0, L1, L2, hj0, hand0, hR0, hT1, hT2, hLeq⟩, hLmem, hLx_len, _⟩ := hL
  have hTree : ∀ (tt : ℕ) (tL : List (ℕ × ℕ)),
      (∀ Q : ℕ → List (ℕ × ℕ) → Prop,
        (∀ (qv qt : ℕ), qv < n → Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) qv qt → Q qt [(qt, qv)]) →
        (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) →
        Q tt tL) →
      (∀ gv ∈ tL, Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) gv.2 gv.1) ∧
      (∀ x : Fin n → Bool,
        (∀ gv ∈ tL, ∃ (w : ℕ) (hw : w < n),
          Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) w gv.1 ∧
          x ⟨w, hw⟩ = true) →
        (C.wires (List.ofFn x)).getD tt false = true) := by
    intro tt tL hTtt
    apply hTtt
    · intro qv qt _ hRqv
      refine ⟨?_, ?_⟩
      · intro gv hgv
        simp only [List.mem_singleton] at hgv
        subst hgv
        exact hRqv
      · intro x hx
        obtain ⟨w, hw, hRw, hxw⟩ := hx (qt, qv) (List.mem_singleton_self _)
        have hwa : (C.wires (List.ofFn x)).getD w false = true := by
          rw [PEqualNP.Outside.L_meta_2355.eval_input n C x w hw]
          exact hxw
        exact PEqualNP.Outside.L_meta_2355.eval_or_true_up n C hao.2.1 x hRw hwa
    · intro qj qt qL1 qL2 hqj handj hRj ih1 ih2
      refine ⟨?_, ?_⟩
      · intro gv hgv
        rcases List.mem_append.mp hgv with h1 | h2
        · exact ih1.1 gv h1
        · exact ih2.1 gv h2
      · intro x hx
        have he1 := ih1.2 x (fun gv hgv => hx gv (List.mem_append_left _ hgv))
        have he2 := ih2.2 x (fun gv hgv => hx gv (List.mem_append_right _ hgv))
        have hand_t := PEqualNP.Outside.L_meta_2355.eval_and_true n C hao x qj hqj handj he1 he2
        exact PEqualNP.Outside.L_meta_2355.eval_or_true_up n C hao.2.1 x hRj hand_t
  by_contra hcontra
  push Not at hcontra
  classical
  let Lx := L.filter (fun e1 => decide (e1.2 = pw p))
  have hLx_le : Lx.length ≤ 2 := by
    change Lx.length ∈ ({1, 2} : Finset ℕ) at hLx_len
    simp only [Finset.mem_insert, Finset.mem_singleton] at hLx_len
    omega
  have hchoose : ∀ gv ∈ Lx, ∃ q : Fin N,
      Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) (pw q) gv.1 ∧ ¬ I q l := by
    intro gv hgv
    have h1 := List.mem_filter.mp hgv
    exact hcontra gv h1.1 (of_decide_eq_true h1.2)
  let f : ℕ × ℕ → Fin N := fun gv =>
    if h : gv ∈ Lx then Classical.choose (hchoose gv h) else p
  let P : Finset (Fin N) := (Lx.map f).toFinset
  let Y : Finset (Fin M) := {l}
  have hPcard : P.card ≤ 2 := by
    refine le_trans (List.toFinset_card_le _) ?_
    rw [List.length_map]
    exact hLx_le
  have hYcard : Y.card ≤ 2 := by simp [Y]
  have hnoinc : ∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3 := by
    intro p3 hp3 l3 hl3
    have hl3eq : l3 = l := Finset.mem_singleton.mp hl3
    subst hl3eq
    rw [List.mem_toFinset, List.mem_map] at hp3
    obtain ⟨gv, hgv, rfl⟩ := hp3
    dsimp [f]
    rw [dif_pos hgv]
    exact (Classical.choose_spec (hchoose gv hgv)).2
  have hcf := hsound P Y hPcard hYcard hnoinc
  let x : Fin n → Bool := fun k3 => decide (k3.val ∈ P.image pw ∪ Y.image lw)
  have hT1' := hTree _ _ hT1
  have hT2' := hTree _ _ hT2
  have hallL : ∀ gv ∈ L, ∃ (w : ℕ) (hw : w < n),
      Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) w gv.1 ∧
      x ⟨w, hw⟩ = true := by
    intro gv hgv
    rcases hLmem gv hgv with hp_eq | hl_eq
    · have hgv_Lx : gv ∈ Lx := List.mem_filter.mpr ⟨hgv, decide_eq_true hp_eq⟩
      let q := Classical.choose (hchoose gv hgv_Lx)
      have hqspec := Classical.choose_spec (hchoose gv hgv_Lx)
      refine ⟨pw q, hpw q, hqspec.1, ?_⟩
      dsimp [x]
      rw [decide_eq_true_iff]
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨gv, hgv_Lx, ?_⟩
      dsimp [f]
      rw [dif_pos hgv_Lx]
    · have hRgv : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) gv.2 gv.1 := by
        rw [hLeq] at hgv
        rcases List.mem_append.mp hgv with h1 | h2
        · exact hT1'.1 gv h1
        · exact hT2'.1 gv h2
      rw [hl_eq] at hRgv
      refine ⟨lw l, hlw l, hRgv, ?_⟩
      dsimp [x]
      rw [decide_eq_true_iff]
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨l, Finset.mem_singleton_self l, rfl⟩
  have he1 := hT1'.2 x (fun gv hgv => hallL gv (by rw [hLeq]; exact List.mem_append_left _ hgv))
  have he2 := hT2'.2 x (fun gv hgv => hallL gv (by rw [hLeq]; exact List.mem_append_right _ hgv))
  have hand_t := PEqualNP.Outside.L_meta_2355.eval_and_true n C hao x j0 hj0 hand0 he1 he2
  have hout_t := PEqualNP.Outside.L_meta_2355.eval_or_true_up n C hao.2.1 x hR0 hand_t
  change PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn x) = false at hcf
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval at hcf
  rw [hout_t] at hcf
  exact Bool.noConfusion hcf
