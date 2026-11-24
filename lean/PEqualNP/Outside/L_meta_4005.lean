import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4005_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem fold_gen {α β : Type} (F : List β → α → List β) (h : List β → α → β)
    (hF : ∀ acc g, F acc g = acc ++ [h acc g]) (l : List α) (init : List β) :
    (l.foldl F init).length = init.length + l.length ∧
    (l.foldl F init).take init.length = init ∧
    ∀ j (hj : j < l.length), (l.foldl F init)[init.length + j]? =
      some (h ((l.foldl F init).take (init.length + j)) l[j]) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, hF]
    refine ⟨by simp [h1]; omega, ?_, ?_⟩
    · rw [List.take_append_of_le_length (by omega)]; exact h2
    · intro j hj
      simp at hj
      rcases Nat.lt_or_eq_of_le hj with hlt | heq
      · rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega),
          h3 j hlt]
        simp [List.getElem_append_left hlt]
      · subst heq
        rw [← h1]
        simp

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]
  exact List.getElem_mem hj

theorem wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  have h := (fold_gen (fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) (fun _ _ => rfl)
    C.gates (List.ofFn x)).2.1
  have h' : ((C.wires (List.ofFn x)).take n)[(i : ℕ)]? = (List.ofFn x)[(i : ℕ)]? := by
    unfold Circuit.wires
    simp only [List.length_ofFn] at h
    rw [h]
  rw [List.getElem?_take] at h'
  simp at h'
  simp [List.getD_eq_getElem?_getD, h']

theorem wv_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ReadsBack n C) :
    gateVal n C j x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have h := (fold_gen (fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) (fun _ _ => rfl)
    C.gates (List.ofFn x)).2.2 j hj
  simp only [List.length_ofFn] at h
  unfold gateVal
  unfold Circuit.wires
  rw [List.getD_eq_getElem?_getD, h, gateAt_eq C j hj]
  simp only [Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < n + j := by
    have := hrb j hj i
    rw [gateAt_eq C j hj] at this
    exact this hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi']

theorem or_facts (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    j ∈ (orSets n C).getD j [] ∧ ((gateAt C j).op = GateOp.or → ∀ w ∈ (gateAt C j).inputs,
      n ≤ w → w < n + j → ∀ g ∈ (orSets n C).getD (w - n) [], g ∈ (orSets n C).getD j []) := by
  have H := fold_gen (orStep n) (fun cs g => ((orStep n cs g).getLast?).getD [])
    (by intro acc g; simp [orStep]) C.gates []
  obtain ⟨h1, -, h3⟩ := H
  have h3' := h3 j hj
  simp only [List.length_nil, Nat.zero_add] at h3' h1
  have hO : orSets n C = C.gates.foldl (orStep n) [] := rfl
  rw [← hO] at h3' h1
  have hlen : ((orSets n C).take j).length = j := by simp [h1]; omega
  rw [gateAt_eq C j hj, List.getD_eq_getElem?_getD, h3']
  simp only [orStep, hlen]
  constructor
  · simp
  · intro hop w hw hnw hwj g hg
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some, hop,
      if_true, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    right
    refine ⟨w, ⟨hw, hnw, hwj⟩, ?_⟩
    have : w - n < j := by omega
    simpa [List.getD_eq_getElem?_getD, List.getElem?_take, this] using hg

theorem cone_facts (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    ∀ w ∈ (gateAt C j).inputs, n ≤ w → w < n + j →
      InCone n C (w - n) j ∧ ∀ i, InCone n C i (w - n) → InCone n C i j := by
  have H := fold_gen (coneStep n) (fun cs g => ((coneStep n cs g).getLast?).getD [])
    (by intro acc g; simp [coneStep]) C.gates []
  obtain ⟨h1, -, h3⟩ := H
  have h3' := h3 j hj
  simp only [List.length_nil, Nat.zero_add] at h3' h1
  have hO : cones n C = C.gates.foldl (coneStep n) [] := rfl
  rw [← hO] at h3' h1
  have hlen : ((cones n C).take j).length = j := by simp [h1]; omega
  intro w hw hnw hwj
  rw [gateAt_eq C j hj] at hw
  have hlt : w - n < j := by omega
  unfold InCone
  rw [List.getD_eq_getElem?_getD, h3']
  simp only [coneStep, hlen, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.getD_some, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · exact ⟨w, ⟨hw, hnw, hwj⟩, Or.inl rfl⟩
  · intro i hi
    refine ⟨w, ⟨hw, hnw, hwj⟩, Or.inr ?_⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_take, hlt] using hi

theorem key (n : ℕ) (C : Circuit) (hAO : AndOrOnly C) (hRB : ReadsBack n C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → gateVal n C k x = true →
      (∃ a, a ≤ k ∧ (a = k ∨ InCone n C a k) ∧ (gateAt C a).op = GateOp.and ∧
        gateVal n C a x = true) ∨
      (∃ i : Fin n, x i = true ∧ ∃ k2 < C.gates.length, OrReaches n C (n + k) k2 ∧
        (gateAt C k2).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k2).inputs) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hv
    rcases hAO _ (gateAt_mem C k hk) with ha | ho
    · exact Or.inl ⟨k, le_rfl, Or.inl rfl, ha, hv⟩
    · have hv2 := hv
      rw [wv_gate n C x k hk hRB, ho] at hv2
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv2
      obtain ⟨w, hw, hwv⟩ := hv2
      have hwlt := hRB k hk w hw
      by_cases hwn : w < n
      · right
        refine ⟨⟨w, hwn⟩, ?_, k, hk, ⟨by omega, ?_⟩, ho, hw⟩
        · rw [← wv_input n C x ⟨w, hwn⟩]; exact hwv
        · simpa using (or_facts n C k hk).1
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have hk' : k' < k := by omega
        have hcf := cone_facts n C k hk (n + k') hw (by omega) (by omega)
        simp only [Nat.add_sub_cancel_left] at hcf
        rcases ih k' hk' (by omega) hwv with
          ⟨a, hale, hor, hand, hav⟩ | ⟨i, hi, k2, hk2, hreach, hop, hmem⟩
        · left
          refine ⟨a, by omega, Or.inr ?_, hand, hav⟩
          rcases hor with rfl | hc
          · exact hcf.1
          · exact hcf.2 a hc
        · right
          refine ⟨i, hi, k2, hk2, ⟨by omega, ?_⟩, hop, hmem⟩
          have h2 := (or_facts n C k hk).2 ho (n + k') hw (by omega) (by omega) k2 hreach.2
          simpa using h2

end PEqualNP.Outside.L_meta_4005_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4005_aux in
theorem PEqualNP.Outside.L_meta_4005 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ (x7 : Fin x1 → Bool), (∃ x8 ∈ PEqualNP.TopForm.junk x2 x4, PEqualNP.EdgeOwnership.gateVal x1 x4 x8 x7 = Bool.true) → ∃ x9 ∈ PEqualNP.TopForm.junk x2 x4, ∀ (x10 : Fin (2 : ℕ)), ∃ x11 ∈ PEqualNP.TopForm.side x4 x9 x10, x7 x11 = Bool.true := by
  intro n G _ C hL hT x hex0
  obtain ⟨⟨hAO, hRB, h2⟩, -, -⟩ := hL
  classical
  have hex : ∃ g, g ∈ junk G C ∧ gateVal n C g x = true := by
    obtain ⟨g0, hg0, hv0⟩ := hex0
    exact ⟨g0, hg0, hv0⟩
  obtain ⟨g, ⟨hgj, hgv⟩, hmin⟩ : ∃ g, (g ∈ junk G C ∧ gateVal n C g x = true) ∧
      ∀ a < g, ¬ (a ∈ junk G C ∧ gateVal n C a x = true) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun a ha => Nat.find_min hex ha⟩
  refine ⟨g, hgj, ?_⟩
  intro b
  have hgj' := hgj
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgj'
  obtain ⟨hglen, hgand, -⟩ := hgj'
  have hlen2 := h2 _ (gateAt_mem C g hglen)
  have hb : (b : ℕ) < (gateAt C g).inputs.length := by rw [hlen2]; exact b.2
  have hw0 : opnd C g b ∈ (gateAt C g).inputs := by
    unfold opnd
    rw [List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem hb
  have hall := hgv
  rw [wv_gate n C x g hglen hRB, hgand] at hall
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hall
  have hw0v := hall _ hw0
  have hw0lt := hRB g hglen _ hw0
  unfold side
  generalize opnd C g b = w0 at hw0 hw0v hw0lt
  by_cases hwn : w0 < n
  · refine ⟨⟨w0, hwn⟩, ?_, ?_⟩
    · simp [orIn]
    · rw [← wv_input n C x ⟨w0, hwn⟩]; exact hw0v
  · obtain ⟨k, rfl⟩ : ∃ k, w0 = n + k := ⟨w0 - n, by omega⟩
    have hk : k < g := by omega
    have hcf := cone_facts n C g hglen (n + k) hw0 (by omega) (by omega)
    simp only [Nat.add_sub_cancel_left] at hcf
    rcases key n C hAO hRB x k (by omega) hw0v with
      ⟨a, hale, hor, hand, hav⟩ | ⟨i, hi, k2, hk2, hreach, hop, hmem⟩
    · exfalso
      have hcone : InCone n C a g := by
        rcases hor with rfl | hc
        · exact hcf.1
        · exact hcf.2 a hc
      by_cases hB : BelowF G C a
      · exact hT a (by omega) g hglen hand hB hgand hcone
      · apply hmin a (by omega)
        refine ⟨?_, hav⟩
        simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
        unfold BelowF at hB
        push_neg at hB
        obtain ⟨y, hy1, hy2⟩ := hB
        exact ⟨by omega, hand, by omega, y, hy1, by simpa using hy2⟩
    · refine ⟨i, ?_, hi⟩
      simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨k2, hk2, hreach, hop, hmem⟩
