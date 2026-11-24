import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4620

open PEqualNP.CircuitLowerBounds

def P (a b : ℕ) (i j : ℕ) : Prop := j = i + 1 ∨ j = 0 ∧ (i = a ∨ i = b)

def enc (o : Option Bool) (q : ℕ × Bool × Bool) : ℕ :=
  o.elim q.1 fun c => bif (bif c then q.2.2 else q.2.1) then 0 else q.1 + 1

theorem inputs_core (a0 b0 a1 b1 : ℕ) : ∀ (is ins0 ins1 : List ℕ),
    List.Forall₂ (P a0 b0) is ins0 → List.Forall₂ (P a1 b1) is ins1 →
    ∃ qs : List (ℕ × Bool × Bool), qs.map (enc none) = is.map (min 18) ∧
      qs.map (enc (some false)) = ins0.map (min 19) ∧
      qs.map (enc (some true)) = ins1.map (min 19) ∧
      ∀ q ∈ qs, (q.2.1 = true → q.1 = min 18 a0 ∨ q.1 = min 18 b0) ∧
        (q.2.2 = true → q.1 = min 18 a1 ∨ q.1 = min 18 b1)
  | [], [], [], _, _ => ⟨[], by simp⟩
  | i :: is, j0 :: ins0, j1 :: ins1, H0, H1 => by
    rcases List.forall₂_cons.1 H0 with ⟨p0, H0'⟩
    rcases List.forall₂_cons.1 H1 with ⟨p1, H1'⟩
    obtain ⟨qs, e1, e2, e3, e4⟩ := inputs_core a0 b0 a1 b1 is ins0 ins1 H0' H1'
    refine ⟨(min 18 i, decide (j0 = 0), decide (j1 = 0)) :: qs, ?_, ?_, ?_, ?_⟩
    · simp [e1, enc]
    · simp only [List.map_cons, e2, List.cons.injEq, and_true]
      unfold enc
      rcases p0 with h | ⟨h, _⟩ <;> subst h <;> simp <;> omega
    · simp only [List.map_cons, e3, List.cons.injEq, and_true]
      unfold enc
      rcases p1 with h | ⟨h, _⟩ <;> subst h <;> simp <;> omega
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · refine ⟨?_, ?_⟩
        · intro h
          simp only [decide_eq_true_eq] at h
          rcases p0 with h' | ⟨_, h' | h'⟩
          · omega
          · exact Or.inl (by rw [h'])
          · exact Or.inr (by rw [h'])
        · intro h
          simp only [decide_eq_true_eq] at h
          rcases p1 with h' | ⟨_, h' | h'⟩
          · omega
          · exact Or.inl (by rw [h'])
          · exact Or.inr (by rw [h'])
      · exact e4 q hq
  | [], _ :: _, _, H0, _ => by simp at H0
  | [], [], _ :: _, _, H1 => by simp at H1
  | _ :: _, [], _, H0, _ => by simp at H0
  | _ :: _, _ :: _, [], _, H1 => by simp at H1

def R (a b : ℕ) (g h : Gate) : Prop := g.op = h.op ∧ List.Forall₂ (P a b) g.inputs h.inputs

def E (o : Option Bool) (e : GateOp × List (ℕ × Bool × Bool)) : Gate :=
  { op := e.1, inputs := e.2.map (enc o) }

def clip (m : ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (min m) }

theorem gates_core (a0 b0 a1 b1 : ℕ) : ∀ (gs h0 h1 : List Gate),
    List.Forall₂ (R a0 b0) gs h0 → List.Forall₂ (R a1 b1) gs h1 →
    ∃ L : List (GateOp × List (ℕ × Bool × Bool)), L.map (E none) = gs.map (clip 18) ∧
      L.map (E (some false)) = h0.map (clip 19) ∧ L.map (E (some true)) = h1.map (clip 19) ∧
      ∀ e ∈ L, ∀ q ∈ e.2, (q.2.1 = true → q.1 = min 18 a0 ∨ q.1 = min 18 b0) ∧
        (q.2.2 = true → q.1 = min 18 a1 ∨ q.1 = min 18 b1)
  | [], [], [], _, _ => ⟨[], by simp⟩
  | g :: gs, k0 :: h0, k1 :: h1, H0, H1 => by
    rcases List.forall₂_cons.1 H0 with ⟨⟨o0, p0⟩, H0'⟩
    rcases List.forall₂_cons.1 H1 with ⟨⟨o1, p1⟩, H1'⟩
    obtain ⟨L, e1, e2, e3, e4⟩ := gates_core a0 b0 a1 b1 gs h0 h1 H0' H1'
    obtain ⟨qs, f1, f2, f3, f4⟩ := inputs_core a0 b0 a1 b1 _ _ _ p0 p1
    refine ⟨(g.op, qs) :: L, ?_, ?_, ?_, ?_⟩
    · simp [e1, E, clip, f1]
    · simp [e2, E, clip, f2, o0]
    · simp [e3, E, clip, f3, o1]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact f4
      · exact e4 e he
  | [], _ :: _, _, H0, _ => by simp at H0
  | [], [], _ :: _, _, H1 => by simp at H1
  | _ :: _, [], _, H0, _ => by simp at H0
  | _ :: _, _ :: _, [], _, H1 => by simp at H1

end PEqualNP.Outside.L_meta_4620

theorem PEqualNP.Outside.L_meta_4620 : have x1 : ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 x2 : ℕ) (x3 x4 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = x4.op ∧ List.Forall₂ (fun (x5 x6 : ℕ) => x6 = x5 + (1 : ℕ) ∨ x6 = (0 : ℕ) ∧ (x5 = x1 ∨ x5 = x2)) x3.inputs x4.inputs; have x2 : Option Bool → PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool) → PEqualNP.CircuitLowerBounds.Gate := fun (x2 : Option Bool) (x3 : PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool)) => { op := x3.1, inputs := List.map (fun (x4 : ℕ × Bool × Bool) => x2.elim x4.1 fun (x5 : Bool) => bif bif x5 then x4.2.2 else x4.2.1 then (0 : ℕ) else x4.1 + (1 : ℕ)) x3.2 : PEqualNP.CircuitLowerBounds.Gate }; ∀ (x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : Bool → List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : Bool → ℕ), (∀ (x7 : Bool), List.Forall₂ (x1 (x5 x7) (x6 x7)) x3 (x4 x7)) → ∃ (x8 : List (PEqualNP.CircuitLowerBounds.GateOp × List (ℕ × Bool × Bool))), List.map (x2 Option.none) x8 = List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map (Min.min (18 : ℕ)) x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x3 ∧ (∀ (x9 : Bool), List.map (x2 (Option.some x9)) x8 = List.map (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => { op := x10.op, inputs := List.map (Min.min (19 : ℕ)) x10.inputs : PEqualNP.CircuitLowerBounds.Gate }) (x4 x9)) ∧ ∀ (x9 : Bool), ∀ x10 ∈ x8, ∀ x12 ∈ x10.2, (bif x9 then x12.2.2 else x12.2.1) = Bool.true → x12.1 = Min.min (18 : ℕ) (x5 x9) ∨ x12.1 = Min.min (18 : ℕ) (x6 x9) := by
  intro R0 E0 gs hs a b H
  obtain ⟨L, e1, e2, e3, e4⟩ := PEqualNP.Outside.L_meta_4620.gates_core (a false) (b false)
    (a true) (b true) gs (hs false) (hs true) (H false) (H true)
  refine ⟨L, e1, ?_, ?_⟩
  · intro c
    cases c
    · exact e2
    · exact e3
  · intro c e he q hq hc
    cases c
    · exact (e4 e he q hq).1 hc
    · exact (e4 e he q hq).2 hc
