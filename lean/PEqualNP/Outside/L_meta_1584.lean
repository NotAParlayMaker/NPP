import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1584_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Le (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true

theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (u v : List Bool)
    (h : ∀ i, u.getD i false = true → v.getD i false = true)
    (hu : g.op.eval (g.inputs.map fun i => u.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at hu ⊢ <;> simp only [GateOp.eval] at hu ⊢
  · simp only [List.all_eq_true, List.mem_map, id] at hu ⊢
    rintro x ⟨i, hi, rfl⟩
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · simp only [List.any_eq_true, List.mem_map, id] at hu ⊢
    obtain ⟨x, ⟨i, hi, rfl⟩, hx⟩ := hu
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem step_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (u v : List Bool)
    (h : Le u v) : Le (step u g) (step v g) := by
  obtain ⟨hl, h⟩ := h
  refine ⟨by simp [step, hl], fun i hi => ?_⟩
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append] at hi ⊢
  by_cases hlt : i < u.length
  · have hlt' : i < v.length := hl ▸ hlt
    simp only [hlt, hlt', ite_true] at hi ⊢
    have := h i
    simp only [List.getD_eq_getElem?_getD] at this
    exact this hi
  · have hlt' : ¬ i < v.length := hl ▸ hlt
    simp only [hlt, hlt', ite_false] at hi ⊢
    rw [← hl]
    rcases Nat.lt_or_ge (i - u.length) 1 with h1 | h1
    · have h0 : i - u.length = 0 := by omega
      rw [h0] at hi ⊢
      simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact gate_mono g hg u v h hi
    · simp [List.getElem?_eq_none (show [_].length ≤ i - u.length by simpa using h1)] at hi

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ u v : List Bool, Le u v → Le (gs.foldl step u) (gs.foldl step v) := by
  induction gs with
  | nil => intro u v h; exact h
  | cons g gs ih =>
    intro u v h
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_le g (hgs g (List.mem_cons_self ..)) u v h)

theorem ofFn_le {N : ℕ} (f f' : Fin N → Bool) (h : ∀ v, f v = true → f' v = true) :
    Le (List.ofFn f) (List.ofFn f') := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  by_cases hi' : i < N
  · simp only [hi', dite_true, Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [hi'] at hi

theorem eval_mono (gates : List Gate) (o : ℕ)
    (hgs : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (u v : List Bool) (h : Le u v)
    (hu : Circuit.eval ⟨gates, o⟩ u = true) : Circuit.eval ⟨gates, o⟩ v = true := by
  have key := fold_le gates hgs u v h
  exact key.2 o hu

end PEqualNP.Outside.L_meta_1584_aux

open PEqualNP.Outside.L_meta_1584_aux in
theorem PEqualNP.Outside.L_meta_1584 :
    ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 2 ≤ m → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (a b : Fin N),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    a ∈ T0 → b ∈ T0 → a ≠ b → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = b))) = true →
    ∀ s : Fin N, s ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L s))) = true := by
  intro q m N L i0 T0 hq hm hN hcard hinter hcover hT0 hT0c gates g a b hgates ha hb hab hea heb s hs
  have hops : ∀ x ∈ gates, x.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      x.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun x hx => (hgates x hx).1
  have hoff : a ∉ L s ∨ b ∉ L s := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨c, hc⟩ := Finset.card_eq_one.1 (hinter s i0 hs)
    have haa : a ∈ L s ∩ L i0 := Finset.mem_inter.2 ⟨hcon.1, hT0 ha⟩
    have hbb : b ∈ L s ∩ L i0 := Finset.mem_inter.2 ⟨hcon.2, hT0 hb⟩
    rw [hc, Finset.mem_singleton] at haa hbb
    exact hab (haa.trans hbb.symm)
  rcases hoff with h | h
  · refine eval_mono gates g hops _ _ (ofFn_le _ _ ?_) hea
    intro v hv
    simp only [decide_eq_true_eq] at hv ⊢
    exact hv ▸ h
  · refine eval_mono gates g hops _ _ (ofFn_le _ _ ?_) heb
    intro v hv
    simp only [decide_eq_true_eq] at hv ⊢
    exact hv ▸ h
