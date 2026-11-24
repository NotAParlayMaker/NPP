import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket
theorem PEqualNP.Outside.R_meta_5234_472
    (compile : let X := Fin 10 → Bool
    let S := Set X
    let T := Bool × S
    let W := fun (x : X) => List.ofFn x ++ [x 0 || x 2]
    let K := fun (L : List T) => ({Set.univ} ∪ Set.range (fun i : Nat => {x : X | (W x).getD i false=true}) : Set S) ∪ {s | ∃ p∈L, p.2=s}
    let valid := fun (L : List T) => ∀ (pre : List T) (p : T) (post : List T), L=pre++p::post →
    p.2 ∉ K pre ∧ (if p.1 then p.2ᶜ ∈ K pre else ∃ a∈K pre, ∃ b∈K pre, p.2=a∩b ∨ p.2=a∪b)
    ∀ C : Circuit, FanInTwo C → ∃ L : List T, valid L ∧ L.length≤C.size ∧
    L.countP Prod.fst ≤ notCount C ∧ L.countP (fun p => !p.1) ≤ C.size-notCount C ∧ {x | C.eval (W x)=true}∈K L)
    (windows : let X := Fin 10 → Bool
    let S := Set X
    let T := Bool × S
    let W := fun (x : X) => List.ofFn x ++ [x 0 || x 2]
    let K := fun (L : List T) => ({Set.univ} ∪ Set.range (fun i : Nat => {x : X | (W x).getD i false=true}) : Set S) ∪ {s | ∃ p∈L, p.2=s}
    let valid := fun (L : List T) => ∀ (pre : List T) (p : T) (post : List T), L=pre++p::post →
    p.2 ∉ K pre ∧ (if p.1 then p.2ᶜ ∈ K pre else ∃ a∈K pre, ∃ b∈K pre, p.2=a∩b ∨ p.2=a∪b)
    ∀ L : List T, valid L → L.countP Prod.fst≤2 → (fun (L : List T) => ∀ (pre : List T) (p : T) (post : List T), L=pre++p::post → (fun (pre : List T) (p : T) => if p.1 then (fun _ => true)∈p.2 → (fun _ => false)∈p.2
    else pre.countP Prod.fst < 2 → (fun _ => false)∈p.2 → (fun _ => true)∈p.2) pre p) L)
    (obstruction : let X := Fin 10 → Bool
    let S := Set X
    let T := Bool × S
    let W := fun (x : X) => List.ofFn x ++ [x 0 || x 2]
    let K := fun (L : List T) => ({Set.univ} ∪ Set.range (fun i : Nat => {x : X | (W x).getD i false=true}) : Set S) ∪ {s | ∃ p∈L, p.2=s}
    let valid := fun (L : List T) => ∀ (pre : List T) (p : T) (post : List T), L=pre++p::post →
    p.2 ∉ K pre ∧ (if p.1 then p.2ᶜ ∈ K pre else ∃ a∈K pre, ∃ b∈K pre, p.2=a∩b ∨ p.2=a∪b)
    ∀ L : List T, valid L → L.length≤18 → L.countP Prod.fst≤2 → L.countP (fun p => !p.1)≤17 →
    (fun (L : List T) => ∀ (pre : List T) (p : T) (post : List T), L=pre++p::post → (fun (pre : List T) (p : T) => if p.1 then (fun _ => true)∈p.2 → (fun _ => false)∈p.2
    else pre.countP Prod.fst < 2 → (fun _ => false)∈p.2 → (fun _ => true)∈p.2) pre p) L → {x : X | ∃ i j : Fin 10, (79267452898694397750816084002 : Nat).testBit (10*i.val+j.val)=true ∧ x i=true ∧ x j=true}∉ K L) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  classical
  intro C fan _ size _ _ one two
  by_contra! correct
  let X := Fin 10 → Bool
  let W := fun (x : X) => List.ofFn x ++ [x 0 || x 2]
  let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  have encode : ∀ (i j : Fin 10), (79267452898694397750816084002 : Nat).testBit (10*i.val+j.val)=true ↔ (i,j)∈E := by decide
  have table : {x : X | C.eval (W x)=true} = {x : X | ∃ i j : Fin 10, (79267452898694397750816084002 : Nat).testBit (10*i.val+j.val)=true ∧ x i=true ∧ x j=true} := by
    ext x
    change C.eval (W x)=true ↔ _
    rw [show C.eval (W x)=_ from correct x]
    change _ ↔ ∃ i j : Fin 10, _ ∧ x i=true ∧ x j=true
    simp_rw [encode]
    have pairs : (∃ i j : Fin 10, (i,j)∈E ∧ x i=true ∧ x j=true) ↔ E.any (fun p => x p.1 && x p.2) = true := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨i,j,ij,a,b⟩; exact ⟨(i,j),ij,by simp [a,b]⟩
      · rintro ⟨⟨i,j⟩,ij,h⟩; simp only [Bool.and_eq_true] at h; exact ⟨i,j,ij,h.1,h.2⟩
    rw [pairs]
    simp [E,Bool.or_assoc]
  obtain ⟨L,valid,len,ns,bs,out⟩ := compile C fan
  exact obstruction L valid (len.trans size) (ns.trans two) (by omega) (windows L valid (ns.trans two)) (table ▸ out)
