import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem op_le (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) {l l' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) l l') : op.eval l ≤ op.eval l' := by
  rcases hop with rfl | rfl
  · induction h with
    | nil => simp
    | cons hab _ ih =>
      simp only [GateOp.eval, List.all_cons, id, bool_le, Bool.and_eq_true] at ih hab ⊢
      exact fun h => ⟨hab h.1, ih h.2⟩
  · induction h with
    | nil => simp
    | cons hab _ ih =>
      simp only [GateOp.eval, List.any_cons, id, bool_le, Bool.or_eq_true] at ih hab ⊢
      rintro (h | h)
      · exact Or.inl (hab h)
      · exact Or.inr (ih h)

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  apply op_le _ hg
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun i _ => getD_le h i

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := ext gs w
  rw [hs]; exact List.getD_append _ _ _ _ h

theorem le_set : ∀ (L : List Bool) (i : ℕ) (c : Bool), L.getD i false ≤ c →
    List.Forall₂ (fun a b => a ≤ b) L (L.set i c)
  | [], _, _, _ => by simp
  | a :: L, 0, c, h => List.Forall₂.cons (by simpa using h) (List.forall₂_same.mpr fun _ _ => le_rfl)
  | a :: L, i+1, c, h => List.Forall₂.cons le_rfl (le_set L i c (by simpa using h))

end PEqualNP.Outside.L_meta_2772_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_2772_aux in
theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  rintro n C g b w w' ⟨hAO, hRB, hg, hb, hw, hw', hle, hf⟩
  obtain ⟨hAnd, -, hTwo⟩ := hAO
  obtain ⟨gs, out⟩ := C
  simp only at hg hle hf hAnd hTwo ⊢
  have hge : gateAt ⟨gs, out⟩ g = gs[g] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hg]
  have hRBg := hRB g hg
  have hgj : ∀ j, j ≠ g → gateAt ⟨gs.set g ⟨(gateAt ⟨gs, out⟩ g).op, (gateAt ⟨gs, out⟩ g).inputs.set b w'⟩, out⟩ j = gateAt ⟨gs, out⟩ j := by
    intro j hj
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]
  have hgg : gateAt ⟨gs.set g ⟨(gateAt ⟨gs, out⟩ g).op, (gateAt ⟨gs, out⟩ g).inputs.set b w'⟩, out⟩ g = ⟨(gateAt ⟨gs, out⟩ g).op, (gateAt ⟨gs, out⟩ g).inputs.set b w'⟩ := by
    simp [gateAt, List.getD_eq_getElem?_getD, hg]
  generalize hG : gateAt ⟨gs, out⟩ g = G0 at hge hw hRBg hgj hgg ⊢
  have hmem : G0 ∈ gs := hge ▸ List.getElem_mem hg
  have hlen2 : G0.inputs.length = 2 := hTwo _ hmem
  have hbl : b < G0.inputs.length := by omega
  have hwb : G0.inputs[b] = w := by
    rw [← hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl]; rfl
  have hwlt : w < n + g := hRBg w (hwb ▸ List.getElem_mem hbl)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro G hG
    rcases List.mem_or_eq_of_mem_set hG with h | rfl
    · exact hAnd G h
    · exact hAnd G0 hmem
  · intro j hj i hi
    simp only [List.length_set] at hj
    by_cases hjg : j = g
    · subst hjg
      rw [hgg] at hi
      rcases List.mem_or_eq_of_mem_set hi with h | rfl
      · exact hRBg i h
      · exact hw'
    · rw [hgj j hjg] at hi
      exact hRB j hj i hi
  · intro G hG
    rcases List.mem_or_eq_of_mem_set hG with h | rfl
    · exact hTwo G h
    · simp [hlen2]
  · funext x
    have hdec : gs = gs.take g ++ G0 :: gs.drop (g + 1) := by
      conv_lhs => rw [← List.take_append_drop g gs, List.drop_eq_getElem_cons hg, ← hge]
    have hset : gs.set g ⟨G0.op, G0.inputs.set b w'⟩ = gs.take g ++ ⟨G0.op, G0.inputs.set b w'⟩ :: gs.drop (g + 1) := by
      simp [List.set_eq_take_append_cons_drop, hg]
    have hev : ∀ G o, (Circuit.mk G o).eval (List.ofFn x) = (G.foldl step (List.ofFn x)).getD o false := fun _ _ => rfl
    obtain ⟨q, hq, hql⟩ := ext (gs.take g) (List.ofFn x)
    have hW : ((gs.take g).foldl step (List.ofFn x)).length = n + g := by
      rw [hq]; simp [hql]; omega
    have hfull : ∀ G1 : Gate, ∀ i, i < n + g → ((gs.take g ++ G1 :: gs.drop (g + 1)).foldl step (List.ofFn x)).getD i false = ((gs.take g).foldl step (List.ofFn x)).getD i false := by
      intro G1 i hi
      rw [List.foldl_append, List.foldl_cons, fold_get _ _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hD : ∀ G ∈ gs.drop (g + 1), G.op = GateOp.and ∨ G.op = GateOp.or := fun G h => hAnd G (List.mem_of_mem_drop h)
    have h1 := hle x
    have h2 := hf x
    simp only [PEqualNP.MetaComplexity.circuitFun] at h2 ⊢
    rw [hev, hev] at h1
    rw [hev, hev] at h2
    rw [hev, hev, hset]
    rw [hdec, hfull _ _ hwlt, hfull _ _ hw'] at h1
    rw [hdec, hfull _ _ hw', List.foldl_append, List.foldl_cons] at h2
    conv_rhs => rw [hdec]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
    generalize (gs.take g).foldl step (List.ofFn x) = W at h1 h2 ⊢
    generalize gs.drop (g + 1) = D at hD h2 ⊢
    have hst : List.Forall₂ (fun a b => a ≤ b) (step W G0) (step W ⟨G0.op, G0.inputs.set b w'⟩) := by
      unfold step
      refine List.rel_append (List.forall₂_same.mpr fun _ _ => le_rfl) (List.Forall₂.cons (op_le G0.op (hAnd G0 hmem) ?_) List.Forall₂.nil)
      rw [List.map_set]
      apply le_set
      rw [bool_le]
      simpa [List.getD_eq_getElem?_getD, hbl, hwb] using h1
    cases hC : (D.foldl step (step W G0)).getD out false
    · have hw'f : W.getD w' false = false := by
        cases h : W.getD w' false
        · rfl
        · rw [h2 h] at hC; exact absurd hC (by simp)
      have hwf : W.getD w false = false := by
        cases h : W.getD w false
        · rfl
        · rw [h1 h] at hw'f; exact absurd hw'f (by simp)
      have heq : step W ⟨G0.op, G0.inputs.set b w'⟩ = step W G0 := by
        unfold step
        congr 3
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          simp only [List.getElem_map, List.getElem_set]
          split_ifs with hib
          · subst hib; rw [hwb, hw'f, hwf]
          · rfl
      rw [heq, hC]
    · have := getD_le (fold_le D hD _ _ hst) out
      rw [hC, bool_le] at this
      exact this rfl
  · simp [Circuit.size]
