import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32000 in
theorem PEqualNP.Outside.R_meta_2056_652
    (orbit : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 31 ∧ D.output < 19 + D.size ∧
      ∀ x : Fin 19 → Bool, circuitFun 19 D x =
        decide (∃ e ∈ ([(0, 7), (0, 9), (1, 7), (1, 8), (1, 14), (1, 18), (2, 7), (2, 12), (2, 16), (2, 17), (3, 11), (3, 15), (3, 16), (3, 18), (4, 10), (4, 14), (4, 15), (4, 17), (5, 8), (5, 12), (5, 13), (5, 15), (6, 7), (6, 10), (6, 11), (6, 13)] : List (Fin 19 × Fin 19)), x e.1=true ∧ x e.2=true))
    (combine : ∀ (n m : ℕ) (D : Circuit) (a b : Fin m → Fin n), Monotone2 D →
      D.output < m+D.size → ∃ C : Circuit, Monotone2 C ∧ C.size≤2*D.size+1 ∧
        ∀ x : Fin n → Bool, circuitFun n C x =
          (circuitFun m D (x ∘ a) || circuitFun m D (x ∘ b))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  let E : List (Fin 19 × Fin 19) := [(0, 7), (0, 9), (1, 7), (1, 8), (1, 14), (1, 18), (2, 7), (2, 12), (2, 16), (2, 17), (3, 11), (3, 15), (3, 16), (3, 18), (4, 10), (4, 14), (4, 15), (4, 17), (5, 8), (5, 12), (5, 13), (5, 15), (6, 7), (6, 10), (6, 11), (6, 13)]
  let a (i : Fin 19) : Fin 26 := ([0, 1, 3, 4, 5, 7, 9, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] : List (Fin 26)).getD i.val 0
  let b (i : Fin 19) : Fin 26 := ([0, 2, 12, 10, 11, 6, 8, 14, 20, 22, 18, 19, 23, 21, 24, 16, 17, 15, 25] : List (Fin 26)).getD i.val 0
  let lift (f : Fin 19 → Fin 26) := E.map (fun e => (f e.1,f e.2))
  let X := lift a ++ lift b
  let near (p l : Fin 13) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
  have sides : ∀ e∈X,e.1.val<13 ∧ 13≤e.2.val := by decide +kernel
  have table : ∀ p l : Fin 13, (Fin.castAdd 13 p,Fin.natAdd 13 l)∈X ↔ near p l := by decide +kernel
  obtain ⟨D,mo,sz,valid,ev⟩ := orbit
  obtain ⟨C,mc,size,merge⟩ := combine 26 19 D a b mo valid
  have edge (x : Fin 26 → Bool) : circuitFun 26 C x=true ↔ ∃ e∈X,x e.1=true ∧ x e.2=true := by
    rw [merge,Bool.or_eq_true,ev,ev,decide_eq_true_iff,decide_eq_true_iff]
    change (∃ e∈E, x (a e.1)=true ∧ x (a e.2)=true) ∨ (∃ e∈E,x (b e.1)=true ∧ x (b e.2)=true) ↔ _
    simp only [X,lift,List.mem_append,List.mem_map]
    constructor
    · rintro (⟨e,he,h,k⟩|⟨e,he,h,k⟩)
      · exact ⟨_,Or.inl ⟨e,he,rfl⟩,h,k⟩
      · exact ⟨_,Or.inr ⟨e,he,rfl⟩,h,k⟩
    · rintro ⟨_,⟨e,he,rfl⟩|⟨e,he,rfl⟩,h,k⟩
      · exact Or.inl ⟨e,he,h,k⟩
      · exact Or.inr ⟨e,he,h,k⟩
  let inp (s t : Finset (Fin 13)) (i : Fin 26) :=
    if i.val<13 then decide (Fin.ofNat 13 i.val∈s) else decide (Fin.ofNat 13 i.val∈t)
  let off (s : Finset (Fin 13)) := Finset.univ.filter (fun l => ∀ p∈s,¬near p l)
  have left (s t : Finset (Fin 13)) (p : Fin 13) : inp s t (Fin.castAdd 13 p)=decide (p∈s) := by
    change (if p.val<13 then decide (Fin.ofNat 13 p.val∈s) else _)=_
    rw [if_pos p.isLt,show Fin.ofNat 13 p.val=p from Fin.ext (Nat.mod_eq_of_lt p.isLt)]
  have right (s t : Finset (Fin 13)) (l : Fin 13) : inp s t (Fin.natAdd 13 l)=decide (l∈t) := by
    change (if 13+l.val<13 then _ else decide (Fin.ofNat 13 (13+l.val)∈t))=_
    rw [if_neg (by omega),show Fin.ofNat 13 (13+l.val)=l from Fin.ext (by change (13+l.val)%13=l.val; simp [Nat.add_mod,Nat.mod_eq_of_lt l.isLt])]
  have full (s t : Finset (Fin 13)) : C.eval (List.ofFn (inp s t))=true ↔ ∃ p∈s,∃ l∈t,near p l := by
    change circuitFun 26 C _=true ↔ _
    rw [edge]
    constructor
    · rintro ⟨⟨u,v⟩,he,hu,hv⟩
      obtain ⟨lo,hi⟩ := sides _ he
      let p : Fin 13 := ⟨u.val,lo⟩
      let l : Fin 13 := ⟨v.val-13,by have := v.isLt; change 13≤v.val at hi; omega⟩
      have pu : Fin.castAdd 13 p=u := Fin.ext rfl
      have lv : Fin.natAdd 13 l=v := Fin.ext (by change 13+(v.val-13)=v.val; change 13≤v.val at hi; omega)
      change inp s t u=true at hu
      change inp s t v=true at hv
      rw [←pu,left,decide_eq_true_iff] at hu
      rw [←lv,right,decide_eq_true_iff] at hv
      exact ⟨p,hu,l,hv,(table p l).mp (by simpa only [pu,lv] using he)⟩
    · rintro ⟨p,hp,l,hl,il⟩
      exact ⟨_,(table p l).mpr il,by simpa only [left,decide_eq_true_eq] using hp,by simpa only [right,decide_eq_true_eq] using hl⟩
  refine ⟨C,mc,by omega,?_⟩
  constructor
  · intro p l hit; exact (full _ _).mpr ⟨p,by simp,l,by simp,hit⟩
  · intro s _
    change C.eval (List.ofFn (inp s (off s)))=false ∧ C.eval (List.ofFn (inp (off s) s))=false
    constructor
    · apply Bool.eq_false_iff.mpr; intro on
      obtain ⟨p,hp,l,hl,il⟩ := (full _ _).mp on
      exact (Finset.mem_filter.mp hl).2 p hp il
    · apply Bool.eq_false_iff.mpr; intro on
      obtain ⟨p,hp,l,hl,il⟩ := (full _ _).mp on
      exact (Finset.mem_filter.mp hp).2 l hl (by simpa only [near,Nat.add_comm] using il)
