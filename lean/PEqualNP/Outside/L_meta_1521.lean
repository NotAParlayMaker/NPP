import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1521_aux

open PEqualNP.CircuitLowerBounds

theorem wires_snoc (gs : List Gate) (g : Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ l = Circuit.wires ⟨gs, o2⟩ l ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o2⟩ l).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (l : List Bool) :
    (Circuit.wires ⟨gs, o⟩ l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc gs g o o, List.length_append, ih]
    simp
    omega

theorem all_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).all id = true) : (l.map f2).all id = true := by
  simp only [List.all_eq_true, List.mem_map] at *
  rintro b ⟨a, ha, rfl⟩
  exact h a (h1 _ ⟨a, ha, rfl⟩)

theorem any_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).any id = true) : (l.map f2).any id = true := by
  simp only [List.any_eq_true, List.mem_map] at *
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h1
  exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩

theorem mono (n : ℕ) (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (gs rest : List Gate), gates = gs ++ rest →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v : Fin n, x v = true → y v = true) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro rest _ w x y hxy h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · simp [List.getD_eq_getElem?_getD, hw] at h ⊢
      exact hxy _ h
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro rest hg w x y hxy h
    have ih' := ih (g :: rest) (by simp [hg])
    have hlen : ∀ z : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = n + gs.length := by
      intro z
      rw [wires_length]
      simp
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [wires_snoc gs g 0 0] at h ⊢
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hw)] at h ⊢
      exact ih' w x y hxy h
    · have hgm : g ∈ gates := by rw [hg]; simp
      have hval : ∀ z : Fin n → Bool,
          (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD w false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
        intro z
        rw [wires_snoc gs g 0 0, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, hw]
        simp
      rcases hops g hgm with ho | ho
      · rw [hval, ho] at h ⊢
        exact all_mono _ _ (fun i hi => ih' i x y hxy hi) _ h
      · rw [hval, ho] at h ⊢
        exact any_mono _ _ (fun i hi => ih' i x y hxy hi) _ h
    · rw [wires_snoc gs g 0 0] at h
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen] at h
      have : w - (n + gs.length) ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk] at h
      simp at h

theorem fin_fact : ∀ s : Fin 13, s ≠ 0 →
    ((0 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) ∨ (1 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13))) ∧
    ((0 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) ∨ (3 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13))) ∧
    ((1 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13)) ∨ (3 : Fin 13) ∉ ({s, s + 1, s + 3, s + 9} : Finset (Fin 13))) := by
  decide

end PEqualNP.Outside.L_meta_1521_aux

theorem PEqualNP.Outside.L_meta_1521 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (a b : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    a ∈ ({0, 1, 3} : Finset (Fin 13)) → b ∈ ({0, 1, 3} : Finset (Fin 13)) → a ≠ b →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = a))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = b))) = true →
    ∀ s : Fin 13, s ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L s))) = true := by
  intro L hL gates g a b hops ha hb hab hea heb s hs
  have hm : ∀ c : Fin 13, c ∉ L s →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = c))) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L s))) = true := by
    intro c hc he
    exact PEqualNP.Outside.L_meta_1521_aux.mono 13 gates (fun x hx => (hops x hx).1) gates [] (by simp) g _ _
      (by
        intro v hv
        simp only [decide_eq_true_eq] at hv ⊢
        rw [hv]
        exact hc) he
  have hf := PEqualNP.Outside.L_meta_1521_aux.fin_fact s hs
  rw [← hL s] at hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | (rcases hf with ⟨h1, h2, h3⟩
       first
        | (rcases h1 with h | h
           · exact hm _ h hea
           · exact hm _ h heb)
        | (rcases h2 with h | h
           · exact hm _ h hea
           · exact hm _ h heb)
        | (rcases h3 with h | h
           · exact hm _ h hea
           · exact hm _ h heb)
        | (rcases h1 with h | h
           · exact hm _ h heb
           · exact hm _ h hea)
        | (rcases h2 with h | h
           · exact hm _ h heb
           · exact hm _ h hea)
        | (rcases h3 with h | h
           · exact hm _ h heb
           · exact hm _ h hea))
