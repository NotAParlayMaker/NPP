import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- A gate whose operands are comparable on all required inputs can be replaced by one operand.
-- The finite lower bound therefore needs only gates with tests witnessing both differences.
theorem PEqualNP.Outside.R_meta_2343_83
    (prune : ∀ (n : ℕ) (C : Circuit) (T : List Bool → Prop), Monotone2 C →
      (∀ x, T x → x.length = n) → (∀ b : Bool, ∃ x, T x ∧ C.eval x = b) →
      ∃ B : Circuit, IsAO2 n B ∧ B.size ≤ C.size ∧ (∀ x, T x → B.eval x = C.eval x) ∧
        ∀ g ∈ B.gates, ∃ i j : ℕ, g.inputs = [i,j] ∧ i < j ∧
          ∀ b : Bool, ∃ x, T x ∧ (B.wires x).getD i false = b ∧ (B.wires x).getD j false = !b)
    (count : ∀ (B : Circuit) (s : List ℕ), s.length ≤ 2 → IsAO2 27 B →
      let D : Finset (Fin 13) := {0,1,3,9}
      let extend := fun (x : List Bool) => x ++ [s.any fun i => x.getD i false]
      let P := fun (x : List Bool) => ∃ p l : Fin 13, p-l ∈ D ∧ x = extend
        (List.ofFn (fun j : Fin 13 => decide (j=p)) ++ List.ofFn (fun j : Fin 13 => decide (j=l)))
      let M := fun (x : List Bool) => ∃ Q : Finset (Fin 13), Q.card = 4 ∧
        (∀ l, (Q.filter (fun p => p-l ∈ D)).card ≤ 2) ∧ x = extend
        (List.ofFn (fun j : Fin 13 => decide (j∈Q)) ++ List.ofFn (fun j : Fin 13 => decide (∀ p∈Q, p-j ∉ D)))
      (∀ x, P x → B.eval x = true) → (∀ x, M x → B.eval x = false) →
      (∀ g ∈ B.gates, ∃ i j : ℕ, g.inputs = [i,j] ∧ i < j ∧ ∀ b : Bool,
        ∃ x, (P x ∨ M x) ∧ (B.wires x).getD i false = b ∧ (B.wires x).getD j false = !b) →
      63 ≤ B.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C s arity mono _
  let D : Finset (Fin 13) := {0,1,3,9}
  let pair (p l : Fin 13) := List.ofFn (fun j : Fin 13 => decide (j=p)) ++
    List.ofFn (fun j : Fin 13 => decide (j=l))
  let quad (Q : Finset (Fin 13)) := List.ofFn (fun j : Fin 13 => decide (j ∈ Q)) ++
    List.ofFn (fun j : Fin 13 => decide (∀ p ∈ Q, p-j ∉ D))
  let good (Q : Finset (Fin 13)) := Q.card = 4 ∧ ∀ l, (Q.filter (fun p => p-l ∈ D)).card ≤ 2
  let extend (x : List Bool) := x ++ [s.any fun i => x.getD i false]
  let P (x : List Bool) := ∃ p l, p-l ∈ D ∧ x = extend (pair p l)
  let M (x : List Bool) := ∃ Q, good Q ∧ x = extend (quad Q)
  change (∀ p l : Fin 13, p-l ∈ D → C.eval (extend (pair p l)) = true) →
    (∀ Q, good Q → C.eval (extend (quad Q)) = false) → 63 ≤ C.size
  intro pos neg
  have hp (x) (hx : P x) : C.eval x = true := by
    obtain ⟨p,l,inc,rfl⟩ := hx
    exact pos p l inc
  have hm (x) (hx : M x) : C.eval x = false := by
    obtain ⟨Q,h,rfl⟩ := hx
    exact neg Q h
  have len (x) (hx : P x ∨ M x) : List.length x = 27 := by
    rcases hx with ⟨p,l,_,rfl⟩ | ⟨Q,_,rfl⟩ <;> simp [extend,pair,quad]
  have both (b : Bool) : ∃ x, (P x ∨ M x) ∧ C.eval x = b := by
    cases b with
    | false =>
      let Q : Finset (Fin 13) := {0,1,2,5}
      have hQ : good Q := by decide
      exact ⟨_, Or.inr ⟨Q,hQ,rfl⟩, neg Q hQ⟩
    | true =>
      have h : (0:Fin 13) - 0 ∈ D := by decide
      exact ⟨_, Or.inl ⟨0,0,h,rfl⟩, pos 0 0 h⟩
  obtain ⟨B,ao,le,eq,witness⟩ := prune 27 C (fun x => P x ∨ M x) mono len both
  apply le_trans _ le
  apply count B s arity ao
  · intro x hx
    exact (eq x (Or.inl hx)).trans (hp x hx)
  · intro x hx
    obtain ⟨Q,a,b,e⟩ := hx
    have hxM : M x := ⟨Q,⟨a,b⟩,e⟩
    exact (eq x (Or.inr hxM)).trans (hm x hxM)
  · intro g hg
    obtain ⟨i,j,row,lt,sp⟩ := witness g hg
    refine ⟨i,j,row,lt,fun b => ?_⟩
    obtain ⟨x,h,u,v⟩ := sp b
    refine ⟨x,?_,u,v⟩
    rcases h with h|⟨Q,⟨a,k⟩,e⟩
    · exact Or.inl h
    · exact Or.inr ⟨Q,a,k,e⟩
