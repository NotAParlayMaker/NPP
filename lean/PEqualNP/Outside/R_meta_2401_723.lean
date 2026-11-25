import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2401_723
    (embed : ∀ (m : ℕ) (e : Fin m ↪ Fin 13), (∀ j, e j ≠ 0) → ∀ (C : Circuit),
      Monotone2 C → ReadsBack (13+m) C → C.output < 13+m+C.size → ∃ D : Circuit,
      Monotone2 D ∧ ReadsBack 27 D ∧ D.output < 27+D.size ∧ D.size = C.size ∧
      ∀ x : Fin 27 → Bool, circuitFun 27 D x =
        circuitFun (13+m) C (Fin.append (fun p : Fin 13 => x (Fin.ofNat 27 p.val))
          (fun j => x (Fin.ofNat 27 (13+(e j).val)))))
    (complete : have B : Finset (Fin 13) := {0,1,3,9}
      let E := fun (p l : Fin 13) => ∃ d ∈ B, p = l+d
      ∀ (m : ℕ) (e : Fin m ↪ Fin 13), (∀ j, e j ≠ 0) → ∀ C : Circuit,
      Monotone2 C → ReadsBack 27 C → C.output < 27+C.size →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 27 D ∧ D.size+m*5 ≤ C.size+64 ∧
      ∀ x : Fin 26 → Bool, have y : Fin (26+1) → Bool := Fin.snoc (α := fun _ : Fin (26+1) => Bool) x (x 0 || x 1)
      circuitFun 27 D y = (circuitFun 27 C y ||
        decide (∃ p l, l ∉ Set.range e ∧ E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)))
    (search : have B : Finset (Fin 13) := {0,1,3,9}
      have E := fun (p l : Fin 13) => ∃ d ∈ B, p = l+d
      ∃ (m : ℕ) (e : Fin m ↪ Fin 13) (C : Circuit), (∀ j, e j ≠ 0) ∧
      Monotone2 C ∧ ReadsBack (13+m) C ∧ C.output < 13+m+C.size ∧ C.size+2 ≤ 5*m ∧
      (∀ (p : Fin 13) (j : Fin m), E p (e j) →
        circuitFun (13+m) C (Fin.append (fun i => decide (i=p)) (fun h => decide (h=j))) = true) ∧
      ∀ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, ¬E p l) →
        (¬∃ l, ∀ p ∈ P, E p l) → (¬∃ p, ∀ l ∈ L, E p l) →
        circuitFun (13+m) C (Fin.append (fun i => decide (i ∈ P)) (fun j => decide (e j ∈ L))) = false) :
    ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  classical
  let E := fun (p l : Fin 13) => ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l+d
  obtain ⟨m,e,C,nz,mono,back,bound,budget,yes,no⟩ := search
  obtain ⟨A,ma,ba,oa,sa,runA⟩ := embed m e nz C mono back bound
  obtain ⟨D,md,bd,sd,runD⟩ := complete m e nz A ma ba oa
  refine ⟨1,D,md,bd,by omega,?_⟩
  let seed : (Fin 26 → Bool) → Fin 27 → Bool := fun x => Fin.snoc x (x 0 || x 1)
  let cut := fun (x : Fin 26 → Bool) => Fin.append (fun p : Fin 13 => x (Fin.castAdd 13 p)) (fun j : Fin m => x (Fin.natAdd 13 (e j)))
  have ra (x : Fin 26 → Bool) : circuitFun 27 A (seed x) = circuitFun (13+m) C (cut x) := by
    rw [runA]
    congr 1
    apply congrArg₂ Fin.append
    · funext p
      have h : Fin.ofNat 27 p.val = (Fin.castAdd 13 p).castSucc := Fin.ext (Nat.mod_eq_of_lt (by have := p.isLt; omega))
      rw [h]; exact Fin.snoc_castSucc _ _ _
    · funext j
      have h : Fin.ofNat 27 (13+(e j).val) = (Fin.natAdd 13 (e j)).castSucc := by
        apply Fin.ext
        change (13+(e j).val)%27 = 13+(e j).val
        exact Nat.mod_eq_of_lt (by have := (e j).isLt; omega)
      rw [h]; exact Fin.snoc_castSucc _ _ _
  let flag := fun (p l : Fin 13) (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  have cross (i j : Fin 13) : Fin.castAdd 13 i ≠ Fin.natAdd 13 j := by
    intro eq
    have h := congrArg Fin.val eq
    simp at h
    omega
  have pp : ∀ a b : Fin 13, Fin.castAdd 13 a = Fin.castAdd 13 b ↔ a=b := by decide
  have ll : ∀ a b : Fin 13, Fin.natAdd 13 a = Fin.natAdd 13 b ↔ a=b := by decide
  have rev (a b : Fin 13) := Ne.symm (cross b a)
  have goalSeed (x : Fin 26 → Bool) : (fun i : Fin 27 => Fin.lastCases (x 0 || x 1) x i) = seed x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [seed,Fin.lastCases_last,Fin.snoc_last]
    · simp only [seed,Fin.lastCases_castSucc,Fin.snoc_castSucc]
  change (∀ p l, E p l → circuitFun 27 D (fun i => Fin.lastCases ((flag p l 0) || flag p l 1) (flag p l) i) = true) ∧ _
  constructor
  · intro p l inc
    rw [goalSeed,runD,ra,Bool.or_eq_true]
    by_cases inside : l ∈ Set.range e
    · obtain ⟨j,rfl⟩ := inside
      left
      have eq : cut (flag p (e j)) = Fin.append (fun i => decide (i=p)) (fun h => decide (h=j)) := by
        apply congrArg₂ Fin.append
        · funext i; simp only [flag,pp,cross,or_false]
        · funext h; simp only [flag,rev,ll,e.injective.eq_iff,false_or]
      rw [eq]; exact yes p j inc
    · right; apply decide_eq_true
      exact ⟨p,l,inside,inc,by simp [flag],by simp [flag]⟩
  · intro P
    let L := Finset.univ.filter (fun l => ∀ p ∈ P, ¬E p l)
    intro _ _ geom x bits
    change circuitFun 27 D (fun i => Fin.lastCases (x 0 || x 1) x i) = false
    rw [goalSeed,runD,ra,Bool.or_eq_false_iff]
    have atP (p : Fin 13) : x (Fin.castAdd 13 p) = true ↔ p ∈ P := by
      rw [bits]; simp only [pp,cross,false_and,exists_false,or_false]; simp
    have atL (l : Fin 13) : x (Fin.natAdd 13 l) = true ↔ l ∈ L := by
      rw [bits]; simp only [ll,rev,and_false,exists_false,false_or,exists_eq_left']; simp only [L,Finset.mem_filter,Finset.mem_univ,true_and]; rfl
    have miss : ∀ p ∈ P, ∀ l ∈ L, ¬E p l := by
      intro p hp l hl; exact (Finset.mem_filter.mp hl).2 p hp
    constructor
    · have eq : cut x = Fin.append (fun i => decide (i ∈ P)) (fun j => decide (e j ∈ L)) := by
        apply congrArg₂ Fin.append
        · funext i; apply Bool.eq_iff_iff.mpr; simpa using atP i
        · funext j; apply Bool.eq_iff_iff.mpr; simpa using atL (e j)
      rw [eq]; apply no P L miss geom.1
      intro witness
      obtain ⟨p,hp⟩ := witness
      exact geom.2 ⟨p,fun l hl => hp l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩)⟩
    · apply decide_eq_false
      rintro ⟨p,l,_,edge,a,b⟩
      exact miss p ((atP p).mp a) l ((atL l).mp b) edge
