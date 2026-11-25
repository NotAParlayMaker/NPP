import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8781

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- One AND gate with no inputs: the constant true. It is a Monotone2 circuit.
def C0 : Circuit := ⟨[⟨GateOp.and, []⟩], 26⟩

lemma C0_mono : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_singleton] at hg
  subst hg
  simp

lemma C0_eval (x : Fin 26 → Bool) : C0.eval (List.ofFn x) = true := by
  simp [C0, Circuit.eval, Circuit.wires, GateOp.eval]

-- On the all-false input every wire of an AND/OR circuit of fan-in two is false.
lemma fold_false (gs : List Gate) (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    g.inputs.length = 2) (w : List Bool) (hw : ∀ b ∈ w, b = false) :
    ∀ b ∈ gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w,
      b = false := by
  induction gs generalizing w with
  | nil => simpa using hw
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hw b hb
    · rw [List.mem_singleton] at hb
      subst hb
      obtain ⟨hop, hlen⟩ := h g (List.mem_cons_self ..)
      have hall : ∀ i, w.getD i false = false := by
        intro i
        rcases Nat.lt_or_ge i w.length with hi | hi
        · rw [List.getD_eq_getElem _ _ hi]
          exact hw _ (List.getElem_mem hi)
        · exact List.getD_eq_default _ _ hi
      obtain ⟨a, c, hac⟩ : ∃ a c, g.inputs = [a, c] := by
        match g.inputs, hlen with
        | [a, c], _ => exact ⟨a, c, rfl⟩
      rw [hac]
      rcases hop with hop | hop <;> rw [hop] <;> simp only [List.map, GateOp.eval, hall] <;> rfl

lemma eval_false (D : Circuit) (hD : IsAO2 26 D) : D.eval (List.ofFn fun _ : Fin 26 => false) = false := by
  obtain ⟨hAO, _, h2⟩ := hD
  unfold Circuit.eval Circuit.wires
  rcases Nat.lt_or_ge D.output
      (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun _ : Fin 26 => false)).length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact fold_false D.gates (fun g hg => ⟨hAO g hg, h2 g hg⟩) _ (by simp) _ (List.getElem_mem hi)
  · exact List.getD_eq_default _ _ hi

end PEqualNP.Outside.L_meta_8781

theorem PEqualNP.Outside.L_meta_8781 : ¬ (∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 26 D ∧ D.size ≤ C.size ∧
        ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) := by
  intro h
  obtain ⟨D, hD, _, heq⟩ := h PEqualNP.Outside.L_meta_8781.C0 PEqualNP.Outside.L_meta_8781.C0_mono
  have h1 := heq (fun _ => false)
  rw [PEqualNP.Outside.L_meta_8781.eval_false D hD, PEqualNP.Outside.L_meta_8781.C0_eval] at h1
  exact Bool.false_ne_true h1
