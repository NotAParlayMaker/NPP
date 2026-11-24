import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2355_aux

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem two_le_countP {α : Type} (p : α → Bool) : ∀ (l : List α) (a b : α), a ∈ l → b ∈ l →
    a ≠ b → p a = true → p b = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro a b ha; simp at ha
  | cons c l ih =>
    intro a b ha hb hab hpa hpb
    rw [List.countP_cons]
    classical
    by_cases hca : c = a
    · subst hca
      have hb' : b ∈ l := by
        rcases List.mem_cons.1 hb with e | e
        · exact absurd e.symm hab
        · exact e
      have := List.countP_pos_iff.2 ⟨b, hb', hpb⟩
      simp only [hpa, ite_true]
      omega
    · by_cases hcb : c = b
      · subst hcb
        have ha' : a ∈ l := by
          rcases List.mem_cons.1 ha with e | e
          · exact absurd e.symm hca
          · exact e
        have := List.countP_pos_iff.2 ⟨a, ha', hpa⟩
        simp only [hpb, ite_true]
        omega
      · have ha' : a ∈ l := by
          rcases List.mem_cons.1 ha with e | e
          · exact absurd e.symm hca
          · exact e
        have hb' : b ∈ l := by
          rcases List.mem_cons.1 hb with e | e
          · exact absurd e.symm hcb
          · exact e
        have := ih a b ha' hb' hab hpa hpb
        split <;> omega



theorem wire_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < x.length + j) :
    (wiresFrom gs x).getD (x.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i => (wiresFrom gs x).getD i false) := by
  set g := gs.getD j ⟨GateOp.or, []⟩ with hg
  have hgj : g = gs[j] := by rw [hg, List.getD_eq_getElem _ _ hj]
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [hgj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  set w0 := wiresFrom (gs.take j) x with hw0
  have hl0 : w0.length = x.length + j := by
    rw [hw0, length_wiresFrom, List.length_take]; omega
  set v := g.op.eval (g.inputs.map fun i => w0.getD i false) with hv
  have hfull : wiresFrom gs x = wiresFrom (gs.drop (j + 1)) (w0 ++ [v]) := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]
    rfl
  have hpre : ∀ i, i < x.length + j → (wiresFrom gs x).getD i false = w0.getD i false := by
    intro i hi
    rw [hfull, getD_wiresFrom _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  have hat : (wiresFrom gs x).getD (x.length + j) false = v := by
    rw [hfull, getD_wiresFrom _ _ _ (by simp; omega), ← hl0, getD_snoc_eq]
  rw [hat, hv]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hpre i (hrb i hi)).symm

theorem wire_gateAt (C : Circuit) (n : ℕ) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
          fun i => (C.wires x).getD i false) := by
  subst hx
  exact wire_gate C.gates x j hj (fun i hi => hrb j hj i hi)

def Rel (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = GateOp.or ∧
    ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs)

theorem or_prop (C : Circuit) (n : ℕ) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (a b : ℕ) (hR : Rel n C a b) :
    (C.wires x).getD a false = true → (C.wires x).getD b false = true := by
  induction hR with
  | refl => exact id
  | tail _ hstep ih =>
    intro ha
    obtain ⟨_, rj, rfl, hrj, hor, hin⟩ := hstep
    rw [wire_gateAt C n x hx hrb rj hrj, hor]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    exact ⟨true, ⟨_, hin, ih ha⟩, rfl⟩

theorem and_val (C : Circuit) (n : ℕ) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (qj : ℕ) (hqj : qj < C.gates.length)
    (hand : (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = GateOp.and)
    (h0 : (C.wires x).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0)
      false = true)
    (h1 : (C.wires x).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0)
      false = true) :
    (C.wires x).getD (n + qj) false = true := by
  have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt C qj ∈ C.gates := by
    show C.gates.getD qj _ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hqj]
    exact List.getElem_mem hqj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h2 _ hmem)
  rw [wire_gateAt C n x hx hrb qj hqj, hand, hab]
  rw [hab] at h0 h1
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  simp only [GateOp.eval, List.map_cons, List.map_nil, h0, h1]
  rfl

theorem tree_true (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (x : List Bool) (hx : x.length = n)
    (top : ℕ) (L : List (ℕ × ℕ))
    (hT : ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
      (∀ (qv qt : ℕ), qv < n → Rel n C qv qt → Q qt [(qt, qv)]) →
      (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = GateOp.and →
        Rel n C (n + qj) qt →
        Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 →
        Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 →
        Q qt (qL1 ++ qL2)) → Q top L)
    (hlit : ∀ e ∈ L, (C.wires x).getD e.1 false = true ∨ (C.wires x).getD e.2 false = true) :
    (C.wires x).getD top false = true := by
  refine hT (fun t L' => (∀ e ∈ L', (C.wires x).getD e.1 false = true ∨
    (C.wires x).getD e.2 false = true) → (C.wires x).getD t false = true) ?_ ?_ hlit
  · intro qv qt _ hR hprem
    rcases hprem (qt, qv) (by simp) with h | h
    · exact h
    · exact or_prop C n x hx hrb qv qt hR h
  · intro qj qt qL1 qL2 hqj hand hR ih1 ih2 hprem
    apply or_prop C n x hx hrb _ _ hR
    apply and_val C n x hx hrb h2 qj hqj hand
    · exact ih1 (fun e he => hprem e (List.mem_append_left _ he))
    · exact ih2 (fun e he => hprem e (List.mem_append_right _ he))

theorem input_val (C : Circuit) (n : ℕ) (f : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (C.wires (List.ofFn f)).getD k false = f ⟨k, hk⟩ := by
  rw [show C.wires (List.ofFn f) = wiresFrom C.gates (List.ofFn f) from rfl,
    getD_wiresFrom _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hk]

end PEqualNP.Outside.L_meta_2355_aux

theorem PEqualNP.Outside.L_meta_2355 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l := by
  intro n N M pw lw I C hAO hpw _ hdisj hpn hln hsound R hR T hT p l L hI hL
  subst hR
  subst hT
  obtain ⟨⟨j0, L1, L2, hj0, hand, hRout, hT1, hT2, rfl⟩, hleaf, hpcount, _⟩ := hL
  obtain ⟨_, hrb, h2⟩ := hAO
  by_contra hno
  push Not at hno
  classical
  let qf : ℕ × ℕ → Fin N := fun gv =>
    if hh : gv ∈ L1 ++ L2 ∧ gv.2 = pw p then Classical.choose (hno gv hh.1 hh.2) else p
  have hqf : ∀ gv ∈ L1 ++ L2, gv.2 = pw p →
      PEqualNP.Outside.L_meta_2355_aux.Rel n C (pw (qf gv)) gv.1 ∧ ¬ I (qf gv) l := by
    intro gv hgv hgp
    have hh : gv ∈ L1 ++ L2 ∧ gv.2 = pw p := ⟨hgv, hgp⟩
    have := Classical.choose_spec (hno gv hgv hgp)
    simp only [qf, dif_pos hh]
    exact this
  let Fl := (L1 ++ L2).filter (fun e1 => decide (e1.2 = pw p))
  let P : Finset (Fin N) := (Fl.map qf).toFinset
  have hPcard : P.card ≤ 2 := by
    have h1 : P.card ≤ (Fl.map qf).length := List.toFinset_card_le _
    rw [List.length_map] at h1
    have hFl : Fl.length = 1 ∨ Fl.length = 2 := by
      simpa only [Fl, Finset.mem_insert, Finset.mem_singleton] using hpcount
    omega
  have hPoff : ∀ q ∈ P, ¬ I q l := by
    intro q hq
    simp only [P, Fl, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hq
    obtain ⟨gv, ⟨hgv, hgp⟩, rfl⟩ := hq
    exact (hqf gv hgv hgp).2
  have hfalse := hsound P {l} hPcard (by simp) (by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton] at hl3
    subst hl3
    exact hPoff p3 hp3)
  apply absurd hfalse
  rw [Bool.not_eq_false]
  set x := List.ofFn (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ ({l} : Finset (Fin M)).image lw))
    with hx
  have hxl : x.length = n := by simp [hx]
  have hlit : ∀ e ∈ L1 ++ L2,
      (C.wires x).getD e.1 false = true ∨ (C.wires x).getD e.2 false = true := by
    intro e he
    rcases hleaf e he with h | h
    · left
      have hq := hqf e he h
      apply PEqualNP.Outside.L_meta_2355_aux.or_prop C n x hxl hrb _ _ hq.1
      rw [hx, PEqualNP.Outside.L_meta_2355_aux.input_val C n _ _ (hpn _)]
      simp only [decide_eq_true_eq, Finset.mem_union, Finset.mem_image]
      left
      refine ⟨qf e, ?_, rfl⟩
      simp only [P, Fl, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
      exact ⟨e, ⟨he, h⟩, rfl⟩
    · right
      rw [h, hx, PEqualNP.Outside.L_meta_2355_aux.input_val C n _ _ (hln l)]
      simp
  have hc1 := PEqualNP.Outside.L_meta_2355_aux.tree_true n C hrb h2 x hxl _ L1 hT1
    (fun e he => hlit e (List.mem_append_left _ he))
  have hc2 := PEqualNP.Outside.L_meta_2355_aux.tree_true n C hrb h2 x hxl _ L2 hT2
    (fun e he => hlit e (List.mem_append_right _ he))
  have hgate := PEqualNP.Outside.L_meta_2355_aux.and_val C n x hxl hrb h2 j0 hj0 hand hc1 hc2
  have hout := PEqualNP.Outside.L_meta_2355_aux.or_prop C n x hxl hrb _ _ hRout hgate
  exact hout
