import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2412_aux

-- helpers adapted from L_meta_640
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma runWires_nil (x : List Bool) : runWires [] x = x := rfl

lemma runWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    runWires (gs1 ++ gs2) x = runWires gs2 (runWires gs1 x) := by
  simp [runWires, List.foldl_append]

lemma runWires_singleton (g : Gate) (x : List Bool) :
    runWires [g] x = stepWire x g := rfl

lemma runWires_length (gs : List Gate) (x : List Bool) :
    (runWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [stepWire]
    omega

lemma getD_append_left_lt (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma runWires_getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (runWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).getD i false = x.getD i false
    have hlt : i < (stepWire x g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire x g) hlt]
    exact getD_append_left_lt x _ i hi

lemma wires_eq_runWires (C : Circuit) (x : List Bool) :
    C.wires x = runWires C.gates x := rfl

lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval
        ((C.gates[k]).inputs.map fun a =>
          if a < x.length + k then (C.wires x).getD a false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  let pref := runWires (C.gates.take k) x
  have hpref_len : pref.length = x.length + k := by
    change (runWires (C.gates.take k) x).length = x.length + k
    rw [runWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hwires : C.wires x = runWires (C.gates.drop (k + 1)) (stepWire pref C.gates[k]) := by
    rw [wires_eq_runWires]
    conv_lhs => rw [hsplit]
    rw [runWires_append, runWires_append, runWires_singleton]
  have hstep_len : x.length + k < (stepWire pref C.gates[k]).length := by
    simp [stepWire, hpref_len]
  rw [hwires, runWires_getD_prefix _ _ _ hstep_len]
  have hstep_eq : (stepWire pref C.gates[k]).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => pref.getD a false) := by
    rw [← hpref_len]
    exact getD_append_singleton_eq pref _
  rw [hstep_eq]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < x.length + k
  · rw [if_pos ha]
    have ha' : a < (stepWire pref C.gates[k]).length := by omega
    rw [runWires_getD_prefix _ _ _ ha']
    have ha'' : a < pref.length := by omega
    exact (getD_append_left_lt pref _ a ha'').symm
  · rw [if_neg ha]
    exact getD_of_le pref a (by omega)

-- value of gate wire in a ReadsBack circuit, on an input list of length n
lemma wire_gate (n : ℕ) (C : Circuit) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map
          fun a => (C.wires x).getD a false) := by
  have h := wires_getD_gate C x j hj
  rw [hx] at h
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
  rw [h, hg]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [if_pos]
  have := hrb j hj a (by rw [hg]; exact ha)
  exact this

lemma or_mono (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (a b : ℕ)
    (h : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) a b)
    (ha : (C.wires x).getD a false = true) : (C.wires x).getD b false = true := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    obtain ⟨_, rj, hb, hrj, hop, hmem⟩ := hst
    subst hb
    rw [wire_gate n C hrb x hx rj hrj, hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    exact ⟨_, ⟨_, hmem, rfl⟩, ih⟩

lemma and_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2) (j : ℕ) (hj : j < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and)
    (h0 : (C.wires x).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) false = true)
    (h1 : (C.wires x).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) false = true) :
    (C.wires x).getD (n + j) false = true := by
  rw [wire_gate n C hrb x hx j hj, hop]
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
  have hl := hlen _ (List.getElem_mem hj)
  rw [hg] at h0 h1 ⊢
  generalize C.gates[j].inputs = ins at *
  match ins, hl with
  | [a, b], _ =>
    simp only [List.getD_cons_zero, List.getD_cons_succ, List.getD_nil] at h0 h1
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, h0, h1]
    rfl

def xl (n : ℕ) (S : Finset ℕ) : List Bool := List.ofFn (fun k0 : Fin n => decide (k0.val ∈ S))

lemma xl_length (n : ℕ) (S : Finset ℕ) : (xl n S).length = n := by simp [xl]

lemma wires_input (n : ℕ) (C : Circuit) (S : Finset ℕ) (i : ℕ) (hi : i < n) :
    (C.wires (xl n S)).getD i false = decide (i ∈ S) := by
  rw [wires_eq_runWires, runWires_getD_prefix]
  · rw [List.getD_eq_getElem?_getD]
    simp [xl, List.getElem?_ofFn, hi]
  · rw [xl_length]; exact hi

lemma tree_true (n : ℕ) (C : Circuit) (S : Finset ℕ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (R : ℕ → ℕ → Prop)
    (hR : R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs))
    (top : ℕ) (L : List (ℕ × ℕ))
    (hT : ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) →
      (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        R (n + qj) qt →
        Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 →
        Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 →
        Q qt (qL1 ++ qL2)) → Q top L)
    (hgood : ∀ e ∈ L, (C.wires (xl n S)).getD e.2 false = true ∨
      (C.wires (xl n S)).getD e.1 false = true) :
    (C.wires (xl n S)).getD top false = true := by
  have hRm : ∀ a b, R a b → (C.wires (xl n S)).getD a false = true →
      (C.wires (xl n S)).getD b false = true := by
    intro a b h ha
    rw [hR] at h
    exact or_mono n C (xl n S) (xl_length n S) hrb a b h ha
  have := hT (fun tt tL => (∀ e ∈ tL, (C.wires (xl n S)).getD e.2 false = true ∨
      (C.wires (xl n S)).getD e.1 false = true) → (C.wires (xl n S)).getD tt false = true)
    (by
      intro qv qt _ hr hall
      rcases hall (qt, qv) (List.mem_singleton_self _) with h | h
      · exact hRm _ _ hr h
      · exact h)
    (by
      intro qj qt L1 L2 hj hop hr ih1 ih2 hall
      apply hRm _ _ hr
      apply and_gate n C (xl n S) (xl_length n S) hrb hlen qj hj hop
      · exact ih1 (fun e he => hall e (List.mem_append_left _ he))
      · exact ih2 (fun e he => hall e (List.mem_append_right _ he)))
  exact this hgood

end PEqualNP.Outside.L_meta_2412_aux

theorem PEqualNP.Outside.L_meta_2412 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (top : ℕ) (L : List (ℕ × ℕ)), I p l → T top L → (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) → (L.filter (fun e1 => decide (e1.2 = pw p))).length ≤ 1 → (∀ gx ∈ L, gx.2 = pw p → ∃ q : Fin N, R (pw q) gx.1 ∧ ¬ I q l) → (∀ pz0 : Fin N, ¬ I pz0 l → ∃ (P0 : Finset (Fin N)) (Y0 : Finset (Fin M)), P0.card ≤ 1 ∧ Y0.card ≤ 2 ∧ (∀ a0 ∈ insert pz0 P0, ∀ m0 ∈ Y0, ¬ I a0 m0) ∧ (C.wires (List.ofFn (fun k0 : Fin n => decide (k0.val ∈ P0.image pw ∪ Y0.image lw)))).getD (top) false = true) := by
  intro n N M pw lw I C hao hpw hlw hdis hpn hln R hR T hT p l top L hI hTt hL hcnt hq pz0 hz
  have hrb := hao.2.1
  have hlen := hao.2.2
  have hTt' := hT ▸ hTt
  have hsub : ∀ a ∈ L, a.2 = pw p → ∀ b ∈ L, b.2 = pw p → a = b := by
    intro a ha ha2 b hb hb2
    have ha' : a ∈ L.filter (fun e1 => decide (e1.2 = pw p)) :=
      List.mem_filter.2 ⟨ha, by simpa using ha2⟩
    have hb' : b ∈ L.filter (fun e1 => decide (e1.2 = pw p)) :=
      List.mem_filter.2 ⟨hb, by simpa using hb2⟩
    generalize L.filter (fun e1 => decide (e1.2 = pw p)) = F at *
    match F, hcnt, ha', hb' with
    | [], _, h, _ => simp at h
    | [c], _, h1, h2 => simp at h1 h2; rw [h1, h2]
    | _ :: _ :: _, h, _, _ => simp at h
  have key : ∀ P0 : Finset (Fin N), (∀ gx ∈ L, gx.2 = pw p →
      (C.wires (PEqualNP.Outside.L_meta_2412_aux.xl n (P0.image pw ∪ ({l} : Finset (Fin M)).image lw))).getD
        gx.1 false = true) →
      (C.wires (List.ofFn (fun k0 : Fin n =>
        decide (k0.val ∈ P0.image pw ∪ ({l} : Finset (Fin M)).image lw)))).getD top false = true := by
    intro P0 hP0
    apply PEqualNP.Outside.L_meta_2412_aux.tree_true n C _ hrb hlen R hR top L hTt'
    intro e he
    rcases hL e he with h | h
    · right; exact hP0 e he h
    · left
      rw [PEqualNP.Outside.L_meta_2412_aux.wires_input n C _ _ (by rw [h]; exact hln l)]
      simp [h]
  by_cases hex : ∃ gx ∈ L, gx.2 = pw p
  · obtain ⟨gx, hgxL, hgx2⟩ := hex
    obtain ⟨q, hRq, hqI⟩ := hq gx hgxL hgx2
    refine ⟨{q}, {l}, by simp, by simp, ?_, ?_⟩
    · intro a0 ha0 m0 hm0
      rw [Finset.mem_singleton] at hm0
      subst hm0
      rw [Finset.mem_insert, Finset.mem_singleton] at ha0
      rcases ha0 with rfl | rfl
      · exact hz
      · exact hqI
    · apply key
      intro e he he2
      have hee := hsub e he he2 gx hgxL hgx2
      subst hee
      have hqin := PEqualNP.Outside.L_meta_2412_aux.wires_input n C
        (({q} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw) (pw q) (hpn q)
      have htrue : (C.wires (PEqualNP.Outside.L_meta_2412_aux.xl n
          (({q} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw))).getD (pw q) false = true := by
        rw [hqin]; simp
      rw [hR] at hRq
      exact PEqualNP.Outside.L_meta_2412_aux.or_mono n C _ (PEqualNP.Outside.L_meta_2412_aux.xl_length _ _)
        hrb _ _ hRq htrue
  · refine ⟨∅, {l}, by simp, by simp, ?_, ?_⟩
    · intro a0 ha0 m0 hm0
      rw [Finset.mem_singleton] at hm0
      subst hm0
      rw [Finset.mem_insert] at ha0
      simp at ha0
      subst ha0
      exact hz
    · apply key
      intro e he he2
      exact absurd ⟨e, he, he2⟩ hex
