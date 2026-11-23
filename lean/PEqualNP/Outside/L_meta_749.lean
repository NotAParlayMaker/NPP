import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

def Rb (u v : Bool) : Prop := u = true → v = true

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (l : List Gate) (v : List Bool) :
    Circuit.wires ⟨l, 0⟩ v = l.foldl stepF v := rfl

lemma f2_getD {a b : List Bool} (h : List.Forall₂ Rb a b) :
    ∀ i, a.getD i false = true → b.getD i false = true := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hab _ ih =>
    intro i hi
    cases i with
    | zero => exact hab (by simpa using hi)
    | succ i => simpa using ih i (by simpa using hi)

lemma f2_snoc {a b : List Bool} {u v : Bool} (h : List.Forall₂ Rb a b) (huv : Rb u v) :
    List.Forall₂ Rb (a ++ [u]) (b ++ [v]) := by
  induction h with
  | nil => exact List.Forall₂.cons huv List.Forall₂.nil
  | cons h1 _ ih => exact List.Forall₂.cons h1 ih

lemma f2_ofFn : ∀ (n : ℕ) (y x : Fin n → Bool), (∀ p, y p = true → x p = true) →
    List.Forall₂ Rb (List.ofFn y) (List.ofFn x)
  | 0, y, x, _ => by
    rw [List.ofFn_zero, List.ofFn_zero]
    exact List.Forall₂.nil
  | n + 1, y, x, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (f2_ofFn n _ _ (fun p hp => h p.succ hp))

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {w1 w2 : List Bool}
    (h : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    Rb (g.op.eval (g.inputs.map fun i => w1.getD i false))
      (g.op.eval (g.inputs.map fun i => w2.getD i false)) := by
  intro h1
  rcases hop with hop | hop
  · rw [hop] at h1 ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map] at h1 ⊢
    rintro b ⟨i, hi, rfl⟩
    exact h i (h1 _ ⟨i, hi, rfl⟩)
  · rw [hop] at h1 ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map] at h1 ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := h1
    exact ⟨_, ⟨i, hi, rfl⟩, h i hb⟩

lemma fold_mono (D : List Gate) (hD : ∀ g ∈ D, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, List.Forall₂ Rb w1 w2 →
      List.Forall₂ Rb (D.foldl stepF w1) (D.foldl stepF w2) := by
  induction D with
  | nil => intro w1 w2 h; exact h
  | cons g D ih =>
    intro w1 w2 h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hD g' (List.mem_cons_of_mem g hg'))
    exact f2_snoc h (gate_mono g (hD g List.mem_cons_self) (f2_getD h))

lemma wires_take_succ (l : List Gate) (j : ℕ) (g : Gate) (hg : l[j]? = some g)
    (v : List Bool) :
    Circuit.wires ⟨l.take (j + 1), 0⟩ v =
      stepF (Circuit.wires ⟨l.take j, 0⟩ v) g := by
  rw [wires_eq, wires_eq, List.take_add_one, hg]
  simp [List.foldl_append]

lemma mono_of_spec (C C' : List Gate) (V : ℕ → Gate → Bool)
    (h1 : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hlen : C'.length = C.length)
    (hrep : ∀ (k : ℕ) (g : Gate), C[k]? = some g →
      (g.op = GateOp.not →
        (V k g = true → C'[k]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (V k g = false → C'[k]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g.op ≠ GateOp.not → C'[k]? = some g)) :
    ∀ g' ∈ C', g'.op = GateOp.and ∨ g'.op = GateOp.or := by
  intro g' hg'
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg'
  have hkl : k < C.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hk).1
  have hC : C[k]? = some C[k] := List.getElem?_eq_getElem hkl
  obtain ⟨hn, ho⟩ := hrep k C[k] hC
  by_cases hop : C[k].op = GateOp.not
  · cases hv : V k C[k] with
    | true =>
      have h := (hn hop).1 hv
      rw [hk] at h
      cases Option.some.inj h
      exact Or.inr rfl
    | false =>
      have h := (hn hop).2 hv
      rw [hk] at h
      cases Option.some.inj h
      exact Or.inl rfl
  · have h := ho hop
    rw [hk] at h
    cases Option.some.inj h
    rcases (h1 C[k] (List.getElem_mem hkl)).1 with h2 | h2 | h2
    · exact Or.inl h2
    · exact Or.inr h2
    · exact absurd h2 hop

lemma headD_map_mono (ins : List ℕ) {w1 w2 : List Bool}
    (h : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    (ins.map fun i => w1.getD i false).headD false = true →
      (ins.map fun i => w2.getD i false).headD false = true := by
  cases ins with
  | nil => intro h0; simp at h0
  | cons i ins => intro h0; simpa using h i (by simpa using h0)

lemma main (n : ℕ) (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (h1 : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hy : y ∈ X) (hmin : ∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true)
    (hfalse : ∀ (j1 : ℕ) (g1 : Gate), C[j1]? = some g1 → g1.op = GateOp.not →
      ((g1.inputs.map (fun i1 => (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD
        false) = false →
      ∀ z ∈ X, ((g1.inputs.map (fun i2 =>
        (Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false)
    (hlen : C'.length = C.length)
    (hrep : ∀ (j2 : ℕ) (g2 : Gate), C[j2]? = some g2 →
      (g2.op = GateOp.not →
        (((g2.inputs.map (fun i3 =>
          (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true →
            C'[j2]? = some ({ op := GateOp.or, inputs := [] } : Gate)) ∧
        (((g2.inputs.map (fun i4 =>
          (Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false →
            C'[j2]? = some ({ op := GateOp.and, inputs := [] } : Gate))) ∧
      (g2.op ≠ GateOp.not → C'[j2]? = some g2)) :
    ∀ j, j ≤ C.length → ∀ x ∈ X,
      Circuit.wires ⟨C'.take j, 0⟩ (List.ofFn x) = Circuit.wires ⟨C.take j, 0⟩ (List.ofFn x) := by
  have hmono := mono_of_spec C C'
    (fun j g => (g.inputs.map (fun i =>
      (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i false)).headD false) h1 hlen hrep
  intro j
  induction j with
  | zero => intro _ x _; rfl
  | succ j ih =>
    intro hj x hx
    have hjl : j < C.length := hj
    have hC : C[j]? = some C[j] := List.getElem?_eq_getElem hjl
    have hjl' : j < C'.length := by rw [hlen]; exact hjl
    have hC' : C'[j]? = some C'[j] := List.getElem?_eq_getElem hjl'
    rw [wires_take_succ C j C[j] hC, wires_take_succ C' j C'[j] hC', ih (le_of_lt hjl) x hx]
    unfold stepF
    congr 2
    obtain ⟨hn, ho⟩ := hrep j C[j] hC
    by_cases hop : C[j].op = GateOp.not
    · cases hv : (C[j].inputs.map (fun i =>
          (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y)).getD i false)).headD false with
      | true =>
        have h := (hn hop).1 hv
        rw [hC'] at h
        rw [Option.some.inj h, hop]
        have hle : List.Forall₂ Rb (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn y))
            (Circuit.wires ⟨C.take j, 0⟩ (List.ofFn x)) := by
          rw [← ih (le_of_lt hjl) y hy, ← ih (le_of_lt hjl) x hx, wires_eq, wires_eq]
          exact fold_mono _ (fun g hg => hmono g (List.mem_of_mem_take hg)) _ _
            (f2_ofFn n y x (hmin x hx))
        have hx1 := headD_map_mono C[j].inputs (f2_getD hle) hv
        simp only [GateOp.eval]
        rw [hx1]
        rfl
      | false =>
        have h := (hn hop).2 hv
        rw [hC'] at h
        rw [Option.some.inj h, hop]
        have hx0 := hfalse j C[j] hC hop hv x hx
        simp only [GateOp.eval]
        rw [hx0]
        rfl
    · have h := ho hop
      rw [hC'] at h
      rw [Option.some.inj h]

end PEqualNP.Outside.L_meta_749

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y h1 hy hmin hfalse hlen hrep x hx w
  have key := PEqualNP.Outside.L_meta_749.main n C C' X y h1 hy hmin hfalse hlen hrep
    C.length le_rfl x hx
  rw [List.take_of_length_le (le_of_eq hlen), List.take_of_length_le le_rfl] at key
  rw [key]
