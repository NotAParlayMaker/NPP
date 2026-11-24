import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2619_461
    (monotone : ∀ C : Circuit, IsAO2 26 C → Monotone (fun x : Fin 26 → Bool => C.eval (List.ofFn x)))
    (extremal : ∃ (C : Circuit) (k a b : ℕ),
      C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      C.output = 26 + k ∧ C.gates[k]? = some ⟨.and, [a, b]⟩ ∧
      (∀ (p l : Fin 13), (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) →
        C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p)) (fun j => decide (j = l)))) = true) ∧
      (∀ p : Fin 13 → Bool, C.eval (List.ofFn (Fin.addCases p (fun j => !(p j || p (j+1) || p (j+3) || p (j+9))))) = false) ∧
      (∀ s : Bool,
        let w := C.wires (List.ofFn (fun i : Fin 26 => decide (i.val = if s = true then 13 else 0)))
        w.getD a false = false ∧ w.getD b false = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (∀ (x2 x3 : Fin (13 : ℕ) → Bool), x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)), x3 x4 = Bool.true ∧ (x2 x4 || x2 (x4 + (1 : Fin (13 : ℕ))) || x2 (x4 + (3 : Fin (13 : ℕ))) || x2 (x4 + (9 : Fin (13 : ℕ)))) = Bool.true) ∧           ∃ (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),             x1.output = (26 : ℕ) + x2 ∧               x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧                 ∀ (x5 : Bool),                   have x6 : List Bool := x1.wires (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                   x6.getD x3 Bool.false = Bool.false ∧ x6.getD x4 Bool.false = Bool.false := by
  obtain ⟨C,k,a,b,hsize,hshape,hnodup,hout,hgate,hpos,hneg,hcold⟩ := extremal
  refine ⟨C,hsize,hshape,hnodup,?_,k,a,b,hout,hgate,hcold⟩
  have mono := monotone C hshape
  intro p l
  let join (p l : Fin 13 → Bool) (i : Fin 26) := Fin.addCases (motive := fun _ => Bool) p l i
  let hits (j : Fin 13) := p j || p (j+1) || p (j+3) || p (j+9)
  change C.eval (List.ofFn (Fin.addCases p l)) = true ↔ ∃ j : Fin 13, l j = true ∧ hits j = true
  constructor
  · intro yes
    by_contra none
    let off (j : Fin 13) := !(hits j)
    have hle : join p l ≤ join p off := by
      intro i
      refine Fin.addCases (m := 13) (n := 13) (motive := fun i => join p l i ≤ join p off i) ?_ ?_ i
      · intro j
        simp [join]
      · intro j
        simp only [join, Fin.addCases_right]
        cases hl : l j with
        | false => exact Bool.false_le _
        | true =>
          have hd : hits j = false := Bool.eq_false_iff.mpr (fun hn => none ⟨j,hl,hn⟩)
          simp [off, hd]
    have impossible := mono hle
    change C.eval (List.ofFn (Fin.addCases p l)) ≤ C.eval (List.ofFn (Fin.addCases p off)) at impossible
    rw [yes, show C.eval (List.ofFn (Fin.addCases p off)) = false from hneg p] at impossible
    exact absurd impossible (by decide)
  · rintro ⟨j,hj,hp⟩
    have fromPair (i : Fin 13) (pi : p i = true)
        (edge : i = j ∨ i = j+1 ∨ i = j+3 ∨ i = j+9) :
        C.eval (List.ofFn (Fin.addCases p l)) = true := by
      let row := join (fun q => decide (q = i)) (fun r => decide (r = j))
      have hle : row ≤ join p l := by
        intro q
        refine Fin.addCases (m := 13) (n := 13) (motive := fun q => row q ≤ join p l q) ?_ ?_ q
        · intro u
          simp only [row, join, Fin.addCases_left]
          by_cases hu : u = i
          · simp [hu, pi]
          · simp [hu]
        · intro v
          simp only [row, join, Fin.addCases_right]
          by_cases hv : v = j
          · simp [hv, hj]
          · simp [hv]
      have forced := mono hle
      change C.eval (List.ofFn row) ≤ C.eval (List.ofFn (Fin.addCases p l)) at forced
      rw [show C.eval (List.ofFn row) = true from hpos i j edge] at forced
      exact Bool.eq_true_of_true_le forced
    simp only [hits, Bool.or_eq_true] at hp
    rcases hp with ((h0 | h1) | h3) | h9
    · exact fromPair j h0 (Or.inl rfl)
    · exact fromPair (j+1) h1 (Or.inr (Or.inl rfl))
    · exact fromPair (j+3) h3 (Or.inr (Or.inr (Or.inl rfl)))
    · exact fromPair (j+9) h9 (Or.inr (Or.inr (Or.inr rfl)))
