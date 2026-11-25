import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17623_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl stp w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, h1, h2⟩ := ih (stp w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, h1]; simp [stp]
    · simp [h2]

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  obtain ⟨t, h1, h2⟩ := foldl_ext gs w
  rw [h1, List.length_append, h2]

theorem foldl_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stp w).getD i false = w.getD i false := by
  obtain ⟨t, h1, -⟩ := foldl_ext gs w
  rw [h1, List.getD_append _ _ _ _ hi]

theorem gd_out (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

def Inv (n m p : ℕ) (rest : List Gate) (U V : List Bool) : Prop :=
  V.length = U.length + 1 ∧ n + m ≤ U.length ∧ p < n + m ∧
  (∀ i, i ≠ n + m → U.getD (eraseRedirect n m p i) false = V.getD i false) ∧
  (U.getD p false = V.getD (n + m) false ∨ ∀ g ∈ rest, n + m ∉ g.inputs)

theorem run (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool), Inv n m p rest U V →
    Inv n m p [] ((rest.map fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate)).foldl stp U)
      (rest.foldl stp V) := by
  intro rest
  induction rest with
  | nil => intro U V h; simpa [Inv] using h
  | cons g rest ih =>
    intro U V ⟨hl, hk, hp, hrel, hc⟩
    have hread : (g.inputs.map (eraseRedirect n m p)).map (fun i => U.getD i false) =
        g.inputs.map (fun i => V.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      by_cases hrk : r = n + m
      · subst hrk
        rcases hc with hc | hc
        · simpa [eraseRedirect] using hc
        · exact absurd hr (hc g (List.mem_cons_self ..))
      · exact hrel r hrk
    apply ih
    refine ⟨?_, ?_, hp, ?_, ?_⟩
    · simp [stp, hl]
    · simp [stp]; omega
    · intro i hi
      simp only [stp]
      rw [hread]
      rcases lt_trichotomy i V.length with h | h | h
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by
          unfold eraseRedirect; split_ifs <;> omega)]
        exact hrel i hi
      · have he : eraseRedirect n m p i = U.length := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [he, h, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]; simp
      · rw [gd_out _ _ (by simp; unfold eraseRedirect; split_ifs <;> omega),
          gd_out _ _ (by simp; omega)]
    · rcases hc with hc | hc
      · left
        simp only [stp]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hc
      · exact Or.inr fun g' hg' => hc g' (List.mem_cons_of_mem _ hg')



theorem erase_ok : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List Bool), x5.length = x1 → x3 < x2.gates.length → x4 < x1 + x3 → ((x2.wires x5).getD (x1 + x3) Bool.false = (x2.wires x5).getD x4 Bool.false ∨ x2.output ≠ x1 + x3 ∧ ∀ x9 ∈ List.drop (x3 + (1 : ℕ)) x2.gates, x1 + x3 ∉ x9.inputs) → (PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4).eval x5 = x2.eval x5 ∧ (PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4).size + (1 : ℕ) = x2.size := by
  intro n C m p y hy hm hp hc
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hE : PEqualNP.CircuitMoves.eraseGate n C m p =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map
          (fun g => (⟨g.op, g.inputs.map (PEqualNP.CircuitMoves.eraseRedirect n m p)⟩ :
            PEqualNP.CircuitLowerBounds.Gate))
        output := PEqualNP.CircuitMoves.eraseRedirect n m p C.output } := by
    unfold PEqualNP.CircuitMoves.eraseGate; rw [if_pos hm]
  refine ⟨?_, ?_⟩
  · set A := (C.gates.take m).foldl stp y with hA
    have hAl : A.length = n + m := by
      rw [hA, foldl_len, hy, List.length_take]; omega
    have hW : C.wires y = (C.gates.drop (m + 1)).foldl stp (stp A C.gates[m]) := by
      change C.gates.foldl stp y = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hW' : (PEqualNP.CircuitMoves.eraseGate n C m p).wires y =
        ((C.gates.drop (m + 1)).map (fun g => (⟨g.op, g.inputs.map
          (PEqualNP.CircuitMoves.eraseRedirect n m p)⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl
          stp A := by
      rw [hE]
      change List.foldl stp y (_ ++ _) = _
      rw [List.foldl_append]
    have hVl : (stp A C.gates[m]).length = A.length + 1 := by simp [stp]
    have hkeep : ∀ i, i < n + m + 1 →
        (C.wires y).getD i false = (stp A C.gates[m]).getD i false := by
      intro i hi; rw [hW, foldl_keep _ _ _ (by omega)]
    have hinv : Inv n m p (C.gates.drop (m + 1)) A (stp A C.gates[m]) := by
      refine ⟨hVl, by omega, hp, ?_, ?_⟩
      · intro i hi
        unfold PEqualNP.CircuitMoves.eraseRedirect
        rw [if_neg hi]
        split_ifs with h
        · rw [gd_out _ _ (by omega), gd_out _ _ (by omega)]
        · simp only [stp]; rw [List.getD_append _ _ _ _ (by omega)]
      · rcases hc with hc | ⟨-, hc⟩
        · left
          rw [← hkeep _ (by omega), hc, hkeep _ (by omega)]
          simp only [stp]; rw [List.getD_append _ _ _ _ (by omega)]
        · exact Or.inr hc
    obtain ⟨-, -, -, hrel, hfin⟩ := run n m p _ _ _ hinv
    rw [← hW', ← hW] at hrel hfin
    have hEo : (PEqualNP.CircuitMoves.eraseGate n C m p).output =
        PEqualNP.CircuitMoves.eraseRedirect n m p C.output := by rw [hE]
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [hEo]
    by_cases ho : C.output = n + m
    · have hr : PEqualNP.CircuitMoves.eraseRedirect n m p C.output = p := by
        unfold PEqualNP.CircuitMoves.eraseRedirect; rw [if_pos ho]
      rw [hr, ho]
      rcases hc with hc | ⟨hc, -⟩
      · rw [hc, hW', foldl_keep _ _ _ (by omega), hkeep _ (by omega)]
        simp only [stp]
        rw [List.getD_append _ _ _ _ (by omega)]
      · exact absurd ho hc
    · exact hrel _ ho
  · unfold PEqualNP.CircuitLowerBounds.Circuit.size
    rw [hE]
    simp
    omega

theorem rb (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (h : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n (eraseGate n C m p) := by
  have hE : eraseGate n C m p =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map
          (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))
        output := eraseRedirect n m p C.output } := by
    unfold eraseGate; rw [if_pos hm]
  rw [hE]
  intro j hj i hi
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop] at hj
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  rw [List.getD_eq_getElem _ _ (by simp; omega)] at hi
  by_cases hjm : j < m
  · rw [List.getElem_append_left (by simp; omega)] at hi
    simp only [List.getElem_take] at hi
    have := h j (by omega) i (by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hi)
    exact this
  · rw [List.getElem_append_right (by simp; omega)] at hi
    simp only [List.getElem_map, List.getElem_drop, List.mem_map, List.length_take] at hi
    obtain ⟨r, hr, rfl⟩ := hi
    have := h (j + 1) (by omega) r (by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ (by omega)]
      have e : j + 1 = m + 1 + (j - min m C.gates.length) := by omega
      simp only [e]; exact hr)
    unfold eraseRedirect; split_ifs <;> omega

end PEqualNP.Outside.L_meta_17623_aux

open PEqualNP.Outside.L_meta_17623_aux PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves in
theorem PEqualNP.Outside.L_meta_17623 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → ∀ x6 < x4.size, x1 + x6 ≠ x4.output → x1 + x6 ∈ List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates := by
  intro n G _ C ⟨⟨hao, hrb, h2⟩, hf, hmin⟩ m hm hout
  by_contra hnot
  have hm' : m < C.gates.length := hm
  have hpos : 0 < n + m := by
    rcases Nat.eq_zero_or_pos (n + m) with h0 | h0
    · have hg := h2 _ (List.getElem_mem hm')
      have hr := hrb m hm'
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hr
      rw [List.getD_eq_getElem _ _ hm'] at hr
      obtain ⟨a, b, hab⟩ : ∃ a b, C.gates[m].inputs = [a, b] := by
        match h : C.gates[m].inputs, hg with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      have := hr a (by rw [hab]; simp)
      omega
    · exact h0
  have hun : ∀ g ∈ C.gates, n + m ∉ g.inputs := by
    intro g hg hmem
    exact hnot (List.mem_flatMap.2 ⟨g, hg, hmem⟩)
  have key := fun (y : List Bool) (hy : y.length = n) =>
    erase_ok n C m 0 y hy hm' hpos (Or.inr ⟨fun h => hout h.symm, fun g hg => hun g (List.mem_of_mem_drop hg)⟩)
  have hE : eraseGate n C m 0 =
      { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map
          (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m 0)⟩ : Gate))
        output := eraseRedirect n m 0 C.output } := by
    unfold eraseGate; rw [if_pos hm']
  have hao2 : PEqualNP.TopForm.IsAO2 n (eraseGate n C m 0) := by
    refine ⟨?_, rb n C m 0 hm' hpos hrb, ?_⟩
    · intro g hg
      rw [hE] at hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact hao g (List.mem_of_mem_take hg)
      · exact hao g' (List.mem_of_mem_drop hg')
    · intro g hg
      rw [hE] at hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact h2 g (List.mem_of_mem_take hg)
      · simpa using h2 g' (List.mem_of_mem_drop hg')
  have hfun : PEqualNP.MetaComplexity.circuitFun n (eraseGate n C m 0) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    rw [← hf]
    funext x
    exact (key (List.ofFn x) (by simp)).1
  have := hmin _ hao2 hfun
  have := (key (List.replicate n false) (by simp)).2
  unfold Circuit.size at *
  omega
