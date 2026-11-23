import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

def Le (a b : List Bool) : Prop := ∀ i : ℕ, a.getD i false = true → b.getD i false = true

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x = Circuit.wires ⟨gs, 0⟩ x ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc, List.length_append, ih]
    simp
    omega

theorem le_snoc (A B : List Bool) (u v : Bool) (hl : A.length = B.length) (h : Le A B)
    (huv : u = true → v = true) : Le (A ++ [u]) (B ++ [v]) := by
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  rcases Nat.lt_or_ge i A.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (hl ▸ hlt)]
    have := h i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    exact this hi
  · rw [List.getElem?_append_right hge] at hi
    rw [List.getElem?_append_right (hl ▸ hge), ← hl]
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · subst heq
      simp at hi ⊢
      exact huv hi
    · have h1 : i - A.length ≠ 0 := by omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h1
      rw [hm] at hi
      simp at hi

theorem gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : Le a b) (he : g.op.eval (g.inputs.map fun i => a.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop] at he ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at he ⊢
    rintro v ⟨i, hi, rfl⟩
    exact h i (he _ ⟨i, hi, rfl⟩)
  · rw [hop] at he ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at he ⊢
    obtain ⟨v, ⟨i, hi, rfl⟩, hv⟩ := he
    exact ⟨_, ⟨i, hi, rfl⟩, h i hv⟩

theorem wires_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : List Bool) (hl : x.length = x'.length) (h : Le x x') :
    Le (Circuit.wires ⟨gs, 0⟩ x) (Circuit.wires ⟨gs, 0⟩ x') := by
  induction gs using List.reverseRecOn with
  | nil => simpa [Circuit.wires] using h
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
    rw [wires_snoc, wires_snoc]
    apply le_snoc _ _ _ _ (by rw [wires_length, wires_length, hl]) ih'
    exact gate_mono g (hgs g (List.mem_append_right _ (List.mem_singleton_self g))) _ _ ih'

theorem le_ofFn {n : ℕ} (y x : Fin n → Bool) (h : ∀ p : Fin n, y p = true → x p = true) :
    Le (List.ofFn y) (List.ofFn x) := by
  intro i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
  by_cases hn : i < n
  · simp only [hn, dite_true, Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [hn] at hi

theorem take_succ_of {α : Type} (l : List α) (k : ℕ) (a : α) (h : l[k]? = some a) :
    l.take (k + 1) = l.take k ++ [a] := by
  rw [List.take_add_one, h]
  rfl

end PEqualNP.Outside.L_meta_749

open PEqualNP.Outside.L_meta_749 in
theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hC hy hmin hnot hlen hC' x hx w
  have hgates' : ∀ g ∈ C', g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    obtain ⟨j, hj⟩ := List.getElem_of_mem hg
    obtain ⟨hjl, rfl⟩ := hj
    have hjC : j < C.length := hlen ▸ hjl
    have hc : C[j]? = some C[j] := List.getElem?_eq_getElem hjC
    have hc' : C'[j]? = some C'[j] := List.getElem?_eq_getElem hjl
    obtain ⟨hn1, hn2⟩ := hC' j C[j] hc
    by_cases hop : C[j].op = PEqualNP.CircuitLowerBounds.GateOp.not
    · cases hb : ((C[j].inputs.map (fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i false)).headD false)
      · have := hn1 hop |>.2 hb
        rw [hc'] at this
        rw [Option.some.inj this]
        exact Or.inl rfl
      · have := hn1 hop |>.1 hb
        rw [hc'] at this
        rw [Option.some.inj this]
        exact Or.inr rfl
    · have := hn2 hop
      rw [hc'] at this
      rw [Option.some.inj this]
      rcases (hC C[j] (List.getElem_mem hjC)).1 with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h1 hop
  have key : ∀ k, k ≤ C.length → ∀ z ∈ X,
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C'.take k, 0⟩ (List.ofFn z) =
        PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take k, 0⟩ (List.ofFn z) := by
    intro k
    induction k with
    | zero => intro _ z _; simp
    | succ k ih =>
      intro hk z hz
      have hkC : k < C.length := by omega
      have hc : C[k]? = some C[k] := List.getElem?_eq_getElem hkC
      have hc' : C'[k]? = some C'[k] := List.getElem?_eq_getElem (hlen ▸ hkC)
      rw [take_succ_of C k _ hc, take_succ_of C' k _ hc', wires_snoc, wires_snoc, ih (by omega) z hz]
      congr 2
      obtain ⟨hn1, hn2⟩ := hC' k C[k] hc
      by_cases hop : C[k].op = PEqualNP.CircuitLowerBounds.GateOp.not
      · rw [hop]
        cases hb : ((C[k].inputs.map (fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take k, 0⟩ (List.ofFn y)).getD i false)).headD false)
        · have h1 := hn1 hop |>.2 hb
          rw [hc'] at h1
          rw [Option.some.inj h1]
          have h2 := hnot k C[k] hc hop hb z hz
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, h2]
          rfl
        · have h1 := hn1 hop |>.1 hb
          rw [hc'] at h1
          rw [Option.some.inj h1]
          have hmono := wires_mono (C'.take k) (fun g hg => hgates' g (List.mem_of_mem_take hg))
            (List.ofFn y) (List.ofFn z) (by simp) (le_ofFn y z (hmin z hz))
          rw [ih (by omega) y hy, ih (by omega) z hz] at hmono
          have h3 : ((C[k].inputs.map (fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take k, 0⟩ (List.ofFn z)).getD i false)).headD false) = true := by
            revert hb
            cases C[k].inputs with
            | nil => simp
            | cons i t => simpa using hmono i
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, h3]
          rfl
      · have h1 := hn2 hop
        rw [hc'] at h1
        rw [Option.some.inj h1]
  have e := key C.length le_rfl x hx
  rw [List.take_length, List.take_of_length_le (le_of_eq hlen)] at e
  rw [e]
