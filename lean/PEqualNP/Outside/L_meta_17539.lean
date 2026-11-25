import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17539_aux

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

end PEqualNP.Outside.L_meta_17539_aux

open PEqualNP.Outside.L_meta_17539_aux in
theorem PEqualNP.Outside.L_meta_17539 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List Bool), x5.length = x1 → x3 < x2.gates.length → x4 < x1 + x3 → ((x2.wires x5).getD (x1 + x3) Bool.false = (x2.wires x5).getD x4 Bool.false ∨ x2.output ≠ x1 + x3 ∧ ∀ x9 ∈ List.drop (x3 + (1 : ℕ)) x2.gates, x1 + x3 ∉ x9.inputs) → (PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4).eval x5 = x2.eval x5 ∧ (PEqualNP.CircuitMoves.eraseGate x1 x2 x3 x4).size + (1 : ℕ) = x2.size := by
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
