import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3773_1
 (synth : let T := Fin 26 → Bool
  let R := Set T × Set T
  let lit : Fin 26 → R := fun v => ({x | x v=true},{x | x v=false})
  let ok := fun ns : List R => ∀ (j : Nat) (r : R), ns[j]?=some r →
    let prev := List.ofFn lit ++ ns.take j
    ∃ s ∈ prev, ∃ t ∈ prev, ∀ x∈r.1, ∀ y∈r.2, (x∈s.1 ∧ y∈s.2) ∨ (x∈t.1 ∧ y∈t.2)
  let A : Finset (Fin 13) := {0,1,3,9}
  let edge := fun x : Fin 26 → Bool => ∃ p l : Fin 13, p+l∈A ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
  ∃ ns : List R, ns.length≤63 ∧ ok ns ∧ (({x|edge x},{x|¬edge x}) : R)∈ns)
 (compile : let T := Fin 26 → Bool
  let R := Set T × Set T
  let lit : Fin 26 → R := fun v => ({x | x v=true},{x | x v=false})
  let ok := fun ns : List R => ∀ (j : Nat) (r : R), ns[j]?=some r →
    let prev := List.ofFn lit ++ ns.take j
    ∃ s ∈ prev, ∃ t ∈ prev, ∀ x∈r.1, ∀ y∈r.2, (x∈s.1 ∧ y∈s.2) ∨ (x∈t.1 ∧ y∈t.2)
  ∀ ns : List R, ok ns → ∀ r∈ns, ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size≤ns.length ∧
    (∀ x∈r.1, C.eval (List.ofFn x)=true) ∧ (∀ x∈r.2, C.eval (List.ofFn x)=false))
 (norm : let A : Finset (Fin 13) := {0,1,3,9}
  let exact := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13, p+l∈A ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size≤63 → exact C → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size≤C.size ∧ (∃ g, D.gates.head?=some g ∧ g.op=.or ∧ g.inputs∈[[0,1],[0,13],[2,13]]) ∧ exact D) :
 have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  classical
  obtain ⟨ns,size,ok,rmem⟩ := synth
  obtain ⟨C,cm,cs,pos,neg⟩ := compile ns ok _ rmem
  obtain ⟨D,dm,ds,⟨g,gh,go,gi⟩,exactD⟩ := norm C cm (cs.trans size) (by
    intro x; constructor
    · intro h; by_contra hn; exact Bool.noConfusion (h.symm.trans (neg x hn))
    · exact pos x)
  refine ⟨D,dm,ds.trans (cs.trans size),⟨g,gh,Or.inr ⟨go,gi⟩⟩,?_,?_⟩
  · intro p l e; apply (exactD _).mpr
    exact ⟨p,l,e,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
  · intro S _; constructor <;> apply Bool.eq_false_iff.mpr <;> intro h
    · obtain ⟨p,l,e,hp,hl⟩ := (exactD _).mp h
      simp only [Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq] at hp hl
      exact hl p hp e
    · obtain ⟨p,l,e,hp,hl⟩ := (exactD _).mp h
      simp only [Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq] at hp hl
      exact hp l hl e
