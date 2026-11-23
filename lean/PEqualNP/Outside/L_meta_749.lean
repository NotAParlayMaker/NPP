import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

lemma wires_take_succ (L : List Gate) (x : List Bool) (t : ℕ) (h : t < L.length) :
    Circuit.wires ⟨L.take (t + 1), 0⟩ x =
      Circuit.wires ⟨L.take t, 0⟩ x ++
        [L[t].op.eval (L[t].inputs.map fun i => (Circuit.wires ⟨L.take t, 0⟩ x).getD i false)] := by
  simp only [Circuit.wires]
  rw [← List.take_append_getElem h, List.foldl_append]
  rfl

lemma getD_mono (a b : List Bool) (h : List.Forall₂ (fun p q : Bool => p = true → q = true) a b)
    (i : ℕ) : a.getD i false = true → b.getD i false = true := by
  rw [List.forall₂_iff_get] at h
  obtain ⟨hl, hg⟩ := h
  by_cases hi : i < a.length
  · have hi' : i < b.length := hl ▸ hi
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
    exact hg i hi hi'
  · intro h0
    rw [List.getD_eq_default _ _ (by omega)] at h0
    exact absurd h0 (by simp)

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : ∀ i : ℕ, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  obtain ⟨op, ins⟩ := g
  rcases hg with hg | hg
  · have hg' : op = GateOp.and := hg
    subst hg'
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    rintro h1 v ⟨i, hi, rfl⟩
    exact h i (h1 _ ⟨i, hi, rfl⟩)
  · have hg' : op = GateOp.or := hg
    subst hg'
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hv⟩

lemma wires_mono (L : List Gate) (hL : ∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, List.Forall₂ (fun p q : Bool => p = true → q = true) a b →
      List.Forall₂ (fun p q : Bool => p = true → q = true)
        (Circuit.wires ⟨L, 0⟩ a) (Circuit.wires ⟨L, 0⟩ b) := by
  induction L with
  | nil => intro a b h; exact h
  | cons g L ih =>
    intro a b h
    simp only [Circuit.wires, List.foldl_cons]
    apply ih (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg'))
    apply List.rel_append h
    exact List.Forall₂.cons
      (gate_mono g (hL g List.mem_cons_self) a b (getD_mono a b h)) List.Forall₂.nil

lemma ofFn_mono (n : ℕ) (y x : Fin n → Bool) (h : ∀ p : Fin n, y p = true → x p = true) :
    List.Forall₂ (fun p q : Bool => p = true → q = true) (List.ofFn y) (List.ofFn x) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i h1 h2
  simp only [List.get_eq_getElem, List.getElem_ofFn]
  exact h _

lemma main (n : ℕ) (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (hC : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hy : y ∈ X) (hle : ∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true)
    (hN : ∀ (j1 : ℕ) (g1 : Gate), C[j1]? = some g1 → g1.op = GateOp.not →
      ((g1.inputs.map (fun i1 => (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD
        false) = false →
      ∀ z ∈ X, ((g1.inputs.map (fun i2 =>
        (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false)
    (hlen : C'.length = C.length)
    (hR : ∀ (j2 : ℕ) (g2 : Gate), C[j2]? = some g2 →
      (g2.op = GateOp.not →
        (((g2.inputs.map (fun i3 =>
            (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true →
          C'[j2]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (((g2.inputs.map (fun i4 =>
            (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false →
          C'[j2]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g2.op ≠ GateOp.not → C'[j2]? = some g2)) :
    ∀ t : ℕ, t ≤ C.length → ∀ x ∈ X,
      Circuit.wires ⟨C'.take t, 0⟩ (List.ofFn x) = Circuit.wires ⟨C.take t, 0⟩ (List.ofFn x) := by
  have hC' : ∀ g ∈ C', g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hj' : j < C.length := hlen ▸ hj
    have hCj : C[j]? = some C[j] := List.getElem?_eq_getElem hj'
    have h1 := hR j C[j] hCj
    have hsome : ∀ g0 : Gate, C'[j]? = some g0 → C'[j] = g0 := by
      intro g0 h0
      rw [List.getElem?_eq_getElem hj] at h0
      exact Option.some.inj h0
    by_cases hnot : C[j].op = GateOp.not
    · cases hv : ((C[j].inputs.map (fun i3 =>
          (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i3 false)).headD false)
      · rw [hsome _ ((h1.1 hnot).2 hv)]
        exact Or.inl rfl
      · rw [hsome _ ((h1.1 hnot).1 hv)]
        exact Or.inr rfl
    · rw [hsome _ (h1.2 hnot)]
      rcases (hC _ (List.getElem_mem hj')).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hnot
  intro t
  induction t with
  | zero => intro _ x _; simp [Circuit.wires]
  | succ t ih =>
    intro ht x hx
    have htC : t < C.length := ht
    have htC' : t < C'.length := hlen ▸ htC
    have ihx := ih (le_of_lt htC) x hx
    have ihy := ih (le_of_lt htC) y hy
    rw [wires_take_succ C' _ t htC', wires_take_succ C _ t htC, ihx]
    congr 2
    have hCt : C[t]? = some C[t] := List.getElem?_eq_getElem htC
    have h1 := hR t C[t] hCt
    have hsome : ∀ g0 : Gate, C'[t]? = some g0 → C'[t] = g0 := by
      intro g0 h0
      rw [List.getElem?_eq_getElem htC'] at h0
      exact Option.some.inj h0
    by_cases hnot : C[t].op = GateOp.not
    · rw [hnot]
      cases hv : ((C[t].inputs.map (fun i3 =>
          (Circuit.wires ⟨C.take t, 0⟩ (List.ofFn y)).getD i3 false)).headD false)
      · rw [hsome _ ((h1.1 hnot).2 hv)]
        have hz := hN t C[t] hCt hnot hv x hx
        simp only [GateOp.eval, hz]
        rfl
      · rw [hsome _ ((h1.1 hnot).1 hv)]
        have hmono := getD_mono _ _ (wires_mono (C'.take t)
          (fun g hg => hC' g (List.mem_of_mem_take hg)) _ _
          (ofFn_mono n y x (hle x hx)))
        rw [ihx, ihy] at hmono
        have hz : ((C[t].inputs.map (fun i3 =>
            (Circuit.wires ⟨C.take t, 0⟩ (List.ofFn x)).getD i3 false)).headD false) = true := by
          cases hin : C[t].inputs with
          | nil => rw [hin] at hv; simp at hv
          | cons i l =>
            rw [hin] at hv
            simp only [List.map_cons, List.headD_cons] at hv ⊢
            exact hmono i hv
        simp only [GateOp.eval, hz]
        rfl
    · rw [hsome _ (h1.2 hnot)]

end PEqualNP.Outside.L_meta_749

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hC hy hle hN hlen hR x hx w
  have h := PEqualNP.Outside.L_meta_749.main n C C' X y hC hy hle hN hlen hR C.length le_rfl x hx
  rw [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at h
  rw [h]
