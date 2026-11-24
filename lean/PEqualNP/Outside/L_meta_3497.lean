import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3497

open PEqualNP.CircuitLowerBounds

-- One evaluation step: the wires so far, then the value of the next gate.
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g t ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hi

-- The value of gate j, written with the final wires, when the gate reads earlier wires only.
lemma gate_value (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (gs.foldl stepW x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (gs.foldl stepW x).getD i false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g t ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hback ⊢
      rw [foldl_getD_lt t (stepW x g) x.length (by simp [stepW])]
      have hval : (stepW x g).getD x.length false =
          g.op.eval (g.inputs.map fun i => x.getD i false) := by
        simp [stepW]
      rw [hval]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [foldl_getD_lt t (stepW x g) i (by simp [stepW]; have := hback i hi; omega)]
      exact (List.getD_append _ _ _ _ (hback i hi)).symm
    | succ k =>
      simp only [List.getElem_cons_succ] at hback ⊢
      have hlen : (stepW x g).length = x.length + 1 := by simp [stepW]
      have hk : k < t.length := by simpa using hj
      have e : x.length + (k + 1) = (stepW x g).length + k := by omega
      rw [e]
      exact ih (stepW x g) k hk (by intro i hi; have := hback i hi; omega)

-- The clause sets: wire w is true exactly when every clause of K w holds a true variable.
def K (n : ℕ) (gs : List Gate) (w : ℕ) : Finset (Finset (Fin n)) :=
  if h : w < n then {{⟨w, h⟩}}
  else if hg : w - n < gs.length then
    if hab : gs[w - n].inputs.getD 0 0 < w ∧ gs[w - n].inputs.getD 1 0 < w then
      if gs[w - n].op.eval [false, true] = true then
        (K n gs (gs[w - n].inputs.getD 0 0)).biUnion fun X =>
          (K n gs (gs[w - n].inputs.getD 1 0)).image fun Y => X ∪ Y
      else K n gs (gs[w - n].inputs.getD 0 0) ∪ K n gs (gs[w - n].inputs.getD 1 0)
    else {∅}
  else {∅}
termination_by w
decreasing_by
  all_goals first | exact hab.1 | exact hab.2

lemma K_input (n : ℕ) (gs : List Gate) (v : Fin n) : K n gs (v : ℕ) = {{v}} := by
  rw [K]
  simp [v.isLt]

lemma K_gate (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
    (hin : gs[j].inputs = [a, b]) (ha : a < n + j) (hb : b < n + j) :
    K n gs (n + j) =
      if gs[j].op.eval [false, true] = true then
        (K n gs a).biUnion fun X => (K n gs b).image fun Y => X ∪ Y
      else K n gs a ∪ K n gs b := by
  rw [K]
  have h1 : ¬ (n + j < n) := by omega
  have e : n + j - n = j := by omega
  simp [h1, e, hj, hin, ha, hb]

lemma K_out (n : ℕ) (gs : List Gate) (w : ℕ) (hw : n + gs.length ≤ w) : K n gs w = {∅} := by
  rw [K]
  have h1 : ¬ (w < n) := by omega
  have h2 : ¬ (w - n < gs.length) := by omega
  simp [h1, h2]

def Sat {n : ℕ} (x : List Bool) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ S ∈ F, ∃ v ∈ S, x.getD (v : ℕ) false = true

lemma sat_union {n : ℕ} (x : List Bool) (A B : Finset (Finset (Fin n))) :
    Sat x (A ∪ B) ↔ Sat x A ∧ Sat x B := by
  unfold Sat
  constructor
  · intro h
    exact ⟨fun S hS => h S (Finset.mem_union_left _ hS), fun S hS => h S (Finset.mem_union_right _ hS)⟩
  · rintro ⟨hA, hB⟩ S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact hA S h
    · exact hB S h

lemma sat_cross {n : ℕ} (x : List Bool) (A B : Finset (Finset (Fin n))) :
    Sat x (A.biUnion fun X => B.image fun Y => X ∪ Y) ↔ Sat x A ∨ Sat x B := by
  unfold Sat
  constructor
  · intro h
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hA, hB⟩ := hcon
    have hA' : ∃ X ∈ A, ∀ v ∈ X, ¬ x.getD (v : ℕ) false = true := by
      by_contra hc
      apply hA
      intro S hS
      by_contra hn
      exact hc ⟨S, hS, fun v hv hvt => hn ⟨v, hv, hvt⟩⟩
    have hB' : ∃ Y ∈ B, ∀ v ∈ Y, ¬ x.getD (v : ℕ) false = true := by
      by_contra hc
      apply hB
      intro S hS
      by_contra hn
      exact hc ⟨S, hS, fun v hv hvt => hn ⟨v, hv, hvt⟩⟩
    obtain ⟨X, hX, hXf⟩ := hA'
    obtain ⟨Y, hY, hYf⟩ := hB'
    have hmem : X ∪ Y ∈ A.biUnion fun X => B.image fun Y => X ∪ Y :=
      Finset.mem_biUnion.mpr ⟨X, hX, Finset.mem_image.mpr ⟨Y, hY, rfl⟩⟩
    obtain ⟨v, hv, hvt⟩ := h _ hmem
    rcases Finset.mem_union.mp hv with hvX | hvY
    · exact hXf v hvX hvt
    · exact hYf v hvY hvt
  · intro h S hS
    obtain ⟨X, hX, hS'⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hS'
    rcases h with hA | hB
    · obtain ⟨v, hv, hvt⟩ := hA X hX
      exact ⟨v, Finset.mem_union_left _ hv, hvt⟩
    · obtain ⟨v, hv, hvt⟩ := hB Y hY
      exact ⟨v, Finset.mem_union_right _ hv, hvt⟩

lemma semantics (n : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hback : ∀ (j : ℕ) (hj : j < gs.length), ∃ a b : ℕ, gs[j].inputs = [a, b] ∧ a < b ∧ b < n + j)
    (w : ℕ) : (gs.foldl stepW x).getD w false = true ↔ Sat x (K n gs w) := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n
    · rw [foldl_getD_lt gs x w (by omega)]
      have hK := K_input n gs ⟨w, h1⟩
      simp only at hK
      rw [hK]
      simp [Sat]
    · by_cases h2 : w - n < gs.length
      · obtain ⟨a, b, hin, hab, hb⟩ := hback (w - n) h2
        have hw : w = n + (w - n) := by omega
        have ha' : a < n + (w - n) := by omega
        have hval := gate_value gs x (w - n) h2 (by
          intro i hi
          rw [hin] at hi
          simp at hi
          omega)
        rw [hx, ← hw, hin] at hval
        simp only [List.map_cons, List.map_nil] at hval
        have hK := K_gate n gs (w - n) h2 a b hin ha' hb
        rw [← hw] at hK
        have iha := ih a (by omega)
        have ihb := ih b (by omega)
        rw [hval, hK]
        rcases hop _ (List.getElem_mem h2) with hand | hor
        · rw [hand]
          simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
            Bool.false_eq_true, ite_false]
          rw [sat_union, ← iha, ← ihb]
          simp
        · rw [hor]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.false_or,
            ite_true]
          rw [sat_cross, ← iha, ← ihb]
          simp
      · have hlen : (gs.foldl stepW x).length ≤ w := by
          rw [foldl_length]
          omega
        rw [List.getD_eq_default _ _ hlen, K_out n gs w (by omega)]
        simp [Sat]

end PEqualNP.Outside.L_meta_3497

theorem PEqualNP.Outside.L_meta_3497 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x4]? = Option.some x5 → ∃ (x7 : ℕ) (x8 : ℕ), x5.inputs = [x7, x8] ∧ x7 < x8 ∧ x8 < x1 + x4) → ∃ (x5 : ℕ → Finset (Finset (Fin x1))), (∀ (x6 : Fin x1), x5 ↑x6 = {{x6}}) ∧ (∀ (x6 : ℕ) (x7 : x6 < x2.size), ∃ (x8 : ℕ) (x9 : ℕ), x2.gates[x6].inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x6 ∧ x5 (x1 + x6) = if x2.gates[x6].op.eval [Bool.false, Bool.true] = Bool.true then (x5 x8).biUnion fun (x10 : Finset (Fin x1)) => Finset.image (fun (x11 : Finset (Fin x1)) => x10 ∪ x11) (x5 x9) else x5 x8 ∪ x5 x9) ∧ ∀ (x6 : List Bool), x6.length = x1 → ∀ (x8 : ℕ), (x2.wires x6).getD x8 Bool.false = Bool.true ↔ ∀ x9 ∈ x5 x8, ∃ x11 ∈ x9, x6.getD (↑x11) Bool.false = Bool.true := by
  intro n C hmono hback
  have hop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    simpa using (hmono g hg).1
  have hback' : ∀ (j : ℕ) (hj : j < C.gates.length), ∃ a b : ℕ,
      C.gates[j].inputs = [a, b] ∧ a < b ∧ b < n + j := by
    intro j hj
    exact hback j C.gates[j] (List.getElem?_eq_getElem hj)
  refine ⟨PEqualNP.Outside.L_meta_3497.K n C.gates, ?_, ?_, ?_⟩
  · intro v
    exact PEqualNP.Outside.L_meta_3497.K_input n C.gates v
  · intro j hj
    obtain ⟨a, b, hin, hab, hb⟩ := hback' j hj
    exact ⟨a, b, hin, hab, hb,
      PEqualNP.Outside.L_meta_3497.K_gate n C.gates j hj a b hin (by omega) hb⟩
  · intro x hx w
    exact PEqualNP.Outside.L_meta_3497.semantics n C.gates x hx hop hback' w
