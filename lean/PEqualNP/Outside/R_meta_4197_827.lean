import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_4197_827
    (seeds : let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
    let Z := fun X : Finset (Fin 21) => Finset.univ.filter (fun l : Fin 21 => Disjoint X (S l))
    let W := fun Y : Finset (Fin 21) => Finset.univ \ Y.biUnion S
    ∀ X, X = W (Z X) → X.card ≤ 5 ∨ ∃ T : Finset (Fin 21), T.card ≤ 5 ∧ X = W T)
    (attach : let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
    ∀ C : Circuit, Monotone2 C → C.size ≤ 82 → C.output < 42+C.size →
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 124 ∧ ∀ X Y : Finset (Fin 21),
    D.eval (incidenceInput X Y) = (C.eval (incidenceInput X Y) ||
      decide (∃ p ∈ X, p.val % 3 = 0 ∧ ∃ l ∈ Y, p ∈ S l)))
    (exterior : let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
    let Z := fun X : Finset (Fin 21) => Finset.univ.filter (fun l : Fin 21 => Disjoint X (S l))
    let W := fun Y : Finset (Fin 21) => Finset.univ \ Y.biUnion S
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 82 ∧ C.output < 42+C.size ∧
      (∀ p l : Fin 21, p.val % 3 ≠ 0 → p ∈ S l → C.eval (incidenceInput {p} {l}) = true) ∧
      ∀ T : Finset (Fin 21), T.card ≤ 5 → C.eval (incidenceInput T (Z T)) = false ∧
        C.eval (incidenceInput (W T) (Z (W T))) = false) :
    have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : (Fin (21 : ℕ) → Bool) → Fin (21 : ℕ) → Bool := fun (x2 : Fin (21 : ℕ) → Bool) (x3 : Fin (21 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (21 : ℕ))) || x2 (x3 + (4 : Fin (21 : ℕ))) || x2 (x3 + (14 : Fin (21 : ℕ))) || x2 (x3 + (16 : Fin (21 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (124 : ℕ) ∧ (∀ (x4 x5 : Fin (21 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (21 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧ ∀ (x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (21 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((21 : ℕ) + (21 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false := by
  classical
  let S := fun l : Fin 21 => ({l,l+1,l+4,l+14,l+16} : Finset (Fin 21))
  let Z := fun X : Finset (Fin 21) => Finset.univ.filter (fun l : Fin 21 => Disjoint X (S l))
  let W := fun Y : Finset (Fin 21) => Finset.univ \ Y.biUnion S
  let edge (p l : Fin 21) := p=l ∨ p=l+1 ∨ p=l+4 ∨ p=l+14 ∨ p=l+16
  have memS (p l : Fin 21) : p ∈ S l ↔ edge p l := by simp [S,edge]
  let raw (x y : Fin 21 → Bool) := List.ofFn (Fin.append x y)
  have tape (X Y : Finset (Fin 21)) :
      raw (fun i => decide (i∈X)) (fun i => decide (i∈Y)) = incidenceInput X Y := by
    exact List.ofFn_fin_append _ _
  obtain ⟨C,mc,sc,valid,pos,neg⟩ := exterior
  obtain ⟨D,md,sd,eqD⟩ := attach C mc sc valid
  refine ⟨D,md,sd,?_,?_⟩
  · intro p l hp
    have ok := (memS p l).mpr hp
    change D.eval (raw (fun i => decide (i=p)) (fun i => decide (i=l))) = true
    have rx : (fun i : Fin 21 => decide (i=p)) = (fun i => decide (i∈({p}:Finset _))) := by ext i; simp
    have ry : (fun i : Fin 21 => decide (i=l)) = (fun i => decide (i∈({l}:Finset _))) := by ext i; simp
    rw [rx,ry,tape,eqD]
    by_cases special : p.val%3=0
    · rw [Bool.or_eq_true]
      exact Or.inr (decide_eq_true ⟨p,by simp,special,l,by simp,ok⟩)
    · rw [Bool.or_eq_true]
      exact Or.inl (pos p l special ok)
  · intro x closed
    let X := Finset.univ.filter (fun i : Fin 21 => x i = true)
    let y := fun l : Fin 21 => !(x l || x (l+1) || x (l+4) || x (l+14) || x (l+16))
    have mx (i : Fin 21) : i∈X ↔ x i=true := by simp [X]
    have mz (l : Fin 21) : l∈Z X ↔ y l=true := by
      simp only [Z,Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
      constructor
      · intro h
        have z (p : Fin 21) (hp : p∈S l) : x p=false := by
          cases e : x p with
          | false => rfl
          | true => exact False.elim (h ((mx p).mpr e) hp)
        simp [y,z l (by simp [S]),z (l+1) (by simp [S]),z (l+4) (by simp [S]),
          z (l+14) (by simp [S]),z (l+16) (by simp [S])]
      · intro h p px pe
        have one := (mx p).mp px
        rcases (memS p l).mp pe with rfl|rfl|rfl|rfl|rfl <;> simp [y,one] at h
    have fixed : X = W (Z X) := by
      ext p
      simp only [W,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_biUnion,not_exists]
      constructor
      · intro hp l hpair
        exact (Finset.disjoint_left.mp (Finset.mem_filter.mp hpair.1).2) hp hpair.2
      · intro h
        by_contra hn
        have no : x p=false := Bool.eq_false_iff.mpr (fun yes => hn ((mx p).mpr yes))
        obtain ⟨l,pe,hl⟩ := closed p no
        exact h l ⟨(mz l).mpr hl,(memS p l).mpr pe⟩
    have zero : C.eval (incidenceInput X (Z X)) = false := by
      rcases seeds X fixed with h|⟨T,ht,eq⟩
      · exact (neg X h).1
      · rw [eq]
        exact (neg T ht).2
    have dis : ¬ ∃ p ∈ X, p.val % 3 = 0 ∧ ∃ l ∈ Z X, p ∈ S l := by
      rintro ⟨p,px,_,l,hl,pe⟩
      exact (Finset.disjoint_left.mp (Finset.mem_filter.mp hl).2) px pe
    have ex : x=(fun p => decide (p∈X)) := by funext p; exact Bool.eq_iff_iff.mpr (by simpa using (mx p).symm)
    have ey : y=(fun l => decide (l∈Z X)) := by funext l; exact Bool.eq_iff_iff.mpr (by simpa using (mz l).symm)
    change D.eval (raw x y)=false
    rw [ex,ey,tape,eqD,zero]
    change (false || decide (∃ p ∈ X, p.val % 3 = 0 ∧ ∃ l ∈ Z X, p ∈ S l)) = false
    rw [decide_eq_false dis]; rfl
