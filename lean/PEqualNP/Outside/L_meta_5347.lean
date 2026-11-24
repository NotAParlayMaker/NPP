import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5347_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.EdgeOwnership

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def setsFrom (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (orStep n) cs

theorem orStep_spec (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    ∃ E : List ℕ, orStep n cs g = cs ++ [cs.length :: E] ∧
      ∀ k ∈ E, g.op = GateOp.or ∧ ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧
        k ∈ cs.getD (w - n) [] := by
  refine ⟨_, rfl, ?_⟩
  intro k hk
  split_ifs at hk with hor
  · obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.1 hk
    obtain ⟨hwin, hwd⟩ := List.mem_filter.1 hw
    have hwd' := of_decide_eq_true hwd
    exact ⟨hor, w, hwin, hwd'.1, hwd'.2, hkw⟩
  · simp at hk

theorem setsFrom_prefix (n : ℕ) (gs : List Gate) : ∀ cs : List (List ℕ),
    ∃ t : List (List ℕ), setsFrom n gs cs = cs ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro cs; exact ⟨[], by simp [setsFrom], rfl⟩
  | cons g gs ih =>
    intro cs
    obtain ⟨E, hE, _⟩ := orStep_spec n cs g
    obtain ⟨t, ht, hl⟩ := ih (cs ++ [cs.length :: E])
    refine ⟨(cs.length :: E) :: t, ?_, by simp [hl]⟩
    change setsFrom n gs (orStep n cs g) = _
    rw [hE, ht]; simp

theorem sets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  obtain ⟨t, ht, hl⟩ := setsFrom_prefix n C.gates []
  change (setsFrom n C.gates []).length = _
  rw [ht]; simp [hl]

theorem sets_gate (n : ℕ) (C : Circuit) {p : ℕ} {g : Gate} (hp : C.gates[p]? = some g) :
    ∃ E : List ℕ, (orSets n C).getD p [] = p :: E ∧
      ∀ k ∈ E, g.op = GateOp.or ∧ ∃ w ∈ g.inputs, n ≤ w ∧ w < n + p ∧
        k ∈ (orSets n C).getD (w - n) [] := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  obtain ⟨t, ht, hl⟩ := setsFrom_prefix n (C.gates.take p) []
  have hcs : (setsFrom n (C.gates.take p) []).length = p := by
    rw [ht]; simp [hl, List.length_take, Nat.min_eq_left hb.le]
  obtain ⟨E, hE, hEp⟩ := orStep_spec n (setsFrom n (C.gates.take p) []) g
  rw [hcs] at hE hEp
  obtain ⟨t2, ht2, _⟩ := setsFrom_prefix n (C.gates.drop (p+1))
    (orStep n (setsFrom n (C.gates.take p) []) g)
  have hfull : orSets n C = (setsFrom n (C.gates.take p) [] ++ [p :: E]) ++ t2 := by
    rw [← hE, ← ht2]
    change setsFrom n C.gates [] = _
    conv_lhs => rw [hsplit]
    simp [setsFrom, List.foldl_append]
  have hstab : ∀ i, i < p →
      (orSets n C).getD i [] = (setsFrom n (C.gates.take p) []).getD i [] := by
    intro i hi
    rw [hfull, List.getD_append _ _ _ _ (by simp [hcs]; omega),
      List.getD_append _ _ _ _ (by omega)]
  refine ⟨E, ?_, ?_⟩
  · rw [hfull, List.getD_append _ _ _ _ (by simp [hcs]),
      List.getD_append_right _ _ _ _ (by omega)]
    simp [hcs]
  · intro k hk
    obtain ⟨hor, w, hwin, h1, h2, hkw⟩ := hEp k hk
    exact ⟨hor, w, hwin, h1, h2, by rw [hstab (w - n) (by omega)]; exact hkw⟩

theorem reach_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    ∀ j k : ℕ, k ∈ (orSets n C).getD j [] → val C x (n + k) = true →
      val C x (n + j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k hk hv
    by_cases hj : j < C.gates.length
    · have hp : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨E, hE, hEp⟩ := sets_gate n C hp
      rw [hE] at hk
      rcases List.mem_cons.1 hk with rfl | hk'
      · exact hv
      · obtain ⟨hor, w, hwin, h1, h2, hkw⟩ := hEp k hk'
        have hw : val C x w = true := by
          have := ih (w - n) (by omega) k hkw hv
          rwa [Nat.add_sub_cancel' h1] at this
        rw [val_gate C x hp, hor]
        change (List.map (operand C x (n + j)) (C.gates[j]).inputs).any id = true
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.2 ⟨w, hwin, by simp [operand, h2, hw]⟩, rfl⟩
    · rw [List.getD_eq_default _ _ (by rw [sets_length]; omega)] at hk
      simp at hk

theorem side_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (u : Fin n)
    (hu : u ∈ orIn n C w) (hx : x u = true) : val C x w = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hreach, hor, hin⟩
  · rw [← h, val_input]; exact hx
  · obtain ⟨hnw, hmem⟩ := hreach
    have hp : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
    have hg : gateAt C k = C.gates[k] := by simp [gateAt, hp]
    rw [hg] at hor hin
    have hul : u.val < n + k := by have := u.isLt; omega
    have hvk : val C x (n + k) = true := by
      rw [val_gate C x hp, hor]
      change (List.map (operand C x (n + k)) (C.gates[k]).inputs).any id = true
      rw [List.any_eq_true]
      exact ⟨true, List.mem_map.2 ⟨u.val, hin, by simp [operand, hul, val_input, hx]⟩, rfl⟩
    have := reach_val C x (w - n) k hmem hvk
    rwa [Nat.add_sub_cancel' hnw] at this

theorem and_val {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (a : ℕ)
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (h0 : val C x (opnd C a 0) = true) (h1 : val C x (opnd C a 1) = true) :
    val C x (n + a) = true := by
  have hp : C.gates[a]? = some C.gates[a] := List.getElem?_eq_getElem ha
  have hg : gateAt C a = C.gates[a] := by simp [gateAt, hp]
  obtain ⟨_, hback, hlen⟩ := hC
  have hl := hlen _ (List.getElem_mem ha)
  have hb := hback a ha
  unfold opnd at h0 h1
  rw [hg] at hand hb h0 h1
  obtain ⟨i0, i1, hi⟩ := List.length_eq_two.1 hl
  rw [hi] at h0 h1 hb
  simp at h0 h1
  have b0 := hb i0 (by simp)
  have b1 := hb i1 (by simp)
  rw [val_gate C x hp, hand, hi]
  simp [GateOp.eval, operand, b0, b1, h0, h1]

theorem adj_of_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (u w : Fin n)
    (hu : u ∈ side C a b) (hw : w ∈ side C a (1 - b)) : G.Adj u w := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨hlen, hand, hbelow⟩ := ha
  have hxu : pairInput u w u = true := by simp [pairInput]
  have hxw : pairInput u w w = true := by simp [pairInput]
  have hv : val C (pairInput u w) (n + a) = true := by
    have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hb with rfl | rfl
    · have h10 : (1 : Fin 2) - 0 = 1 := by decide
      rw [h10] at hw
      exact and_val C hC _ a hlen hand (side_val C _ _ u hu hxu) (side_val C _ _ w hw hxw)
    · have h11 : (1 : Fin 2) - 1 = 0 := by decide
      rw [h11] at hw
      exact and_val C hC _ a hlen hand (side_val C _ _ w hw hxw) (side_val C _ _ u hu hxu)
  have hF := hbelow (pairInput u w) hv
  simp [graphFun] at hF
  obtain ⟨p, q, hpq, hp, hq⟩ := hF
  simp [pairInput] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq.ne
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl hpq.ne

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (hL : IsLeastAO G C) (u1 u2 v w : Fin n) (a1 a2 : ℕ) (b1 b2 : Fin 2)
    (h1 : s(u1, v) ∈ Ustar G C) (h2 : s(u2, v) ∈ Ustar G C)
    (ha1 : a1 ∈ tops G C) (ha2 : a2 ∈ tops G C)
    (hu1 : u1 ∈ side C a1 b1) (hu2 : u2 ∈ side C a2 b2)
    (hw1 : w ∈ side C a1 (1 - b1)) (hw2 : w ∈ side C a2 (1 - b2)) : u1 = u2 := by
  have hC := hL.1
  have e1 : G.Adj u1 w := adj_of_sides G C hC a1 ha1 b1 u1 w hu1 hw1
  have e2 : G.Adj u2 w := adj_of_sides G C hC a2 ha2 b2 u2 w hu2 hw2
  unfold Ustar at h1 h2
  obtain ⟨m1, n1⟩ := Finset.mem_sdiff.1 h1
  obtain ⟨m2, _⟩ := Finset.mem_sdiff.1 h2
  have f1 : G.Adj u1 v := by simpa using m1
  have f2 : G.Adj u2 v := by simpa using m2
  by_contra hne
  by_cases hvw : v = w
  · subst hvw
    apply n1
    unfold starEdges
    rw [Finset.mem_biUnion]
    refine ⟨a1, ha1, ?_⟩
    rw [Finset.mem_image]
    have hb : b1 = 0 ∨ b1 = 1 := by fin_cases b1 <;> simp
    rcases hb with rfl | rfl
    · have h10 : (1 : Fin 2) - 0 = 1 := by decide
      rw [h10] at hw1
      exact ⟨(u1, v), Finset.mem_product.2 ⟨hu1, hw1⟩, rfl⟩
    · have h11 : (1 : Fin 2) - 1 = 0 := by decide
      rw [h11] at hw1
      exact ⟨(v, u1), Finset.mem_product.2 ⟨hw1, hu1⟩, Sym2.eq_swap⟩
  · have hne' : u2 ≠ u1 := fun h => hne h.symm
    have hwv : w ≠ v := fun h => hvw h.symm
    have hp : (SimpleGraph.Walk.cons f1 (SimpleGraph.Walk.cons f2.symm
        (SimpleGraph.Walk.cons e2 (SimpleGraph.Walk.cons e1.symm SimpleGraph.Walk.nil)))).IsCycle := by
      simp [SimpleGraph.Walk.cons_isCycle_iff, hne, hne', hvw, hwv, f1.ne, f1.ne.symm, f2.ne,
        f2.ne.symm, e1.ne, e1.ne.symm, e2.ne, e2.ne.symm]
    have := hg u1 _ hp
    simp at this

end PEqualNP.Outside.L_meta_5347_aux

theorem PEqualNP.Outside.L_meta_5347 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → PEqualNP.TopForm.IsLeastAO x2 x4 → ∀ (x7 x8 x9 x10 : Fin x1) (x11 x12 : ℕ) (x13 x14 : Fin (2 : ℕ)), s(x7, x9) ∈ PEqualNP.TopForm.Ustar x2 x4 → s(x8, x9) ∈ PEqualNP.TopForm.Ustar x2 x4 → x11 ∈ PEqualNP.TopForm.tops x2 x4 → x12 ∈ PEqualNP.TopForm.tops x2 x4 → x7 ∈ PEqualNP.TopForm.side x4 x11 x13 → x8 ∈ PEqualNP.TopForm.side x4 x12 x14 → x10 ∈ PEqualNP.TopForm.side x4 x11 ((1 : Fin (2 : ℕ)) - x13) → x10 ∈ PEqualNP.TopForm.side x4 x12 ((1 : Fin (2 : ℕ)) - x14) → x7 = x8 := by
  intro n G _ C hg hL u1 u2 v w a1 a2 b1 b2 h1 h2 ha1 ha2 hu1 hu2 hw1 hw2
  exact PEqualNP.Outside.L_meta_5347_aux.main G C hg hL u1 u2 v w a1 a2 b1 b2 h1 h2 ha1 ha2 hu1 hu2 hw1 hw2
