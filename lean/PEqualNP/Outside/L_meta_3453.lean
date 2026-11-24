import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3453

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl step w = w ++ t ∧ (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]
      simp [step]
    · rw [List.foldl_cons, hl]
      simp [step]
      omega

lemma getD_append_left (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_past (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma foldl_length (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length :=
  (foldl_prefix gs x).choose_spec.2

lemma foldl_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl step x).getD i false = x.getD i false := by
  obtain ⟨t, ht, -⟩ := foldl_prefix gs x
  rw [ht, getD_append_left _ _ _ hi]

lemma foldl_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (gs.foldl step x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl step x).getD i false) := by
  set g := gs[j] with hg
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [hg, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  set W0 := (gs.take j).foldl step x with hW0
  have hW0len : W0.length = x.length + j := by
    rw [hW0, foldl_length, List.length_take]
    omega
  have hfull : gs.foldl step x = (gs.drop (j + 1)).foldl step (step W0 g) := by
    have h := congrArg (fun l => l.foldl step x) hsplit
    rw [h, List.foldl_append, List.foldl_cons]
  obtain ⟨t, ht, -⟩ := foldl_prefix (gs.drop (j + 1)) (step W0 g)
  rw [hfull, ht]
  have hpre : ∀ i, i < W0.length → (step W0 g ++ t).getD i false = W0.getD i false := by
    intro i hi
    rw [step, List.append_assoc, getD_append_left _ _ _ hi]
  have hmap : g.inputs.map (fun i => (step W0 g ++ t).getD i false) =
      g.inputs.map (fun i => W0.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpre i (by rw [hW0len]; exact hr i hi)
  rw [hmap, step, List.append_assoc, ← hW0len]
  simp

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (p q : ℕ → Bool) (h : ∀ i ∈ l, p i = true → q i = true) :
    op.eval (l.map p) = true → op.eval (l.map q) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hp i hi
    exact h i hi (hp i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, hp⟩
    exact ⟨i, hi, h i hi hp⟩

end PEqualNP.Outside.L_meta_3453

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hAO hu hsig
  obtain ⟨hAndOr, hRB, -⟩ := hAO
  set C' := PEqualNP.FactorSubst.substReads C n u sigma with hC'
  set f : ℕ → ℕ → ℕ := fun j i => if i = n + u then sigma j else i with hf
  have hlen' : C'.gates.length = C.gates.length := by
    simp [hC', PEqualNP.FactorSubst.substReads]
  have hget' : ∀ j (hj : j < C'.gates.length),
      C'.gates[j] = ⟨(C.gates[j]'(hlen' ▸ hj)).op,
        (C.gates[j]'(hlen' ▸ hj)).inputs.map (f j)⟩ := by
    intro j hj
    simp [hC', PEqualNP.FactorSubst.substReads, hf]
  have hgateAt : ∀ j (hj : j < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    intro j hj
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
  have hRB' : ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < n + j := by
    intro j hj i hi
    exact hRB j hj i (by rw [hgateAt j hj]; exact hi)
  have hn : (List.ofFn x).length = n := List.length_ofFn
  set W := C.wires (List.ofFn x) with hW
  set W' := C'.wires (List.ofFn x) with hW'
  have hWlen : W.length = n + C.gates.length := by
    rw [hW, PEqualNP.Outside.L_meta_3453.wires_eq, PEqualNP.Outside.L_meta_3453.foldl_length, hn]
  have hW'len : W'.length = n + C.gates.length := by
    rw [hW', PEqualNP.Outside.L_meta_3453.wires_eq, PEqualNP.Outside.L_meta_3453.foldl_length, hn,
      hlen']
  -- the wire equations
  have hinW : ∀ i < n, W.getD i false = (List.ofFn x).getD i false := by
    intro i hi
    rw [hW, PEqualNP.Outside.L_meta_3453.wires_eq]
    exact PEqualNP.Outside.L_meta_3453.foldl_input _ _ _ (by rw [hn]; exact hi)
  have hinW' : ∀ i < n, W'.getD i false = (List.ofFn x).getD i false := by
    intro i hi
    rw [hW', PEqualNP.Outside.L_meta_3453.wires_eq]
    exact PEqualNP.Outside.L_meta_3453.foldl_input _ _ _ (by rw [hn]; exact hi)
  have hgW : ∀ j (hj : j < C.gates.length), W.getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => W.getD i false) := by
    intro j hj
    have h := PEqualNP.Outside.L_meta_3453.foldl_gate C.gates (List.ofFn x) j hj
      (by rw [hn]; exact hRB' j hj)
    rw [hn] at h
    rw [hW, PEqualNP.Outside.L_meta_3453.wires_eq]
    exact h
  have hfread : ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, f j i < n + j := by
    intro j hj i hi
    simp only [hf]
    split_ifs with h
    · have h1 := hsig j
      have h2 := hRB' j hj i hi
      omega
    · exact hRB' j hj i hi
  have hgW' : ∀ j (hj : j < C.gates.length), W'.getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => W'.getD (f j i) false) := by
    intro j hj
    have hj' : j < C'.gates.length := by rw [hlen']; exact hj
    have h := PEqualNP.Outside.L_meta_3453.foldl_gate C'.gates (List.ofFn x) j hj'
      (by
        rw [hn, hget' j hj']
        intro i hi
        simp only [List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        exact hfread j hj i0 hi0)
    rw [hn, hget' j hj', List.map_map] at h
    rw [hW', PEqualNP.Outside.L_meta_3453.wires_eq]
    exact h
  have hop : ∀ j (hj : j < C.gates.length),
      (C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or :=
    fun j hj => hAndOr _ (List.getElem_mem hj)
  have hreader : ∀ j (hj : j < C.gates.length), n + u ∈ (C.gates[j]).inputs →
      n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
    intro j hj h
    rw [hgateAt j hj]
    exact h
  constructor
  · intro hyp i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi'
      by_cases hlt : i < n
      · rw [hinW' i hlt] at hi'
        rw [hinW i hlt]
        exact hi'
      by_cases hge : n + C.gates.length ≤ i
      · rw [PEqualNP.Outside.L_meta_3453.getD_past _ _ (by rw [hW'len]; exact hge)] at hi'
        exact absurd hi' (by simp)
      obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      rw [hgW' j hj] at hi'
      rw [hgW j hj]
      refine PEqualNP.Outside.L_meta_3453.eval_mono _ (hop j hj) _ _ _ ?_ hi'
      intro i hi hval
      by_cases hiu : i = n + u
      · subst hiu
        have hfu : f j (n + u) = sigma j := by simp [hf]
        rw [hfu] at hval
        have hs : sigma j < n + j := by
          have := hfread j hj (n + u) hi
          simpa [hfu] using this
        exact hyp j hj (hreader j hj hi) (ih (sigma j) hs hval)
      · have hfi : f j i = i := by simp [hf, hiu]
        rw [hfi] at hval
        exact ih i (hRB' j hj i hi) hval
  · intro hyp
    have key : ∀ i, W'.getD i false = W.getD i false := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        by_cases hlt : i < n
        · rw [hinW' i hlt, hinW i hlt]
        by_cases hge : n + C.gates.length ≤ i
        · rw [PEqualNP.Outside.L_meta_3453.getD_past _ _ (by rw [hW'len]; exact hge),
            PEqualNP.Outside.L_meta_3453.getD_past _ _ (by rw [hWlen]; exact hge)]
        obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [hgW' j hj, hgW j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hiu : i = n + u
        · subst hiu
          have hfu : f j (n + u) = sigma j := by simp [hf]
          have hs : sigma j < n + j := by
            have := hfread j hj (n + u) hi
            simpa [hfu] using this
          rw [hfu, ih (sigma j) hs]
          exact hyp j hj (hreader j hj hi)
        · have hfi : f j i = i := by simp [hf, hiu]
          rw [hfi]
          exact ih i (hRB' j hj i hi)
    apply List.ext_getElem (by rw [hW'len, hWlen])
    intro i h1 h2
    have := key i
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    exact this
