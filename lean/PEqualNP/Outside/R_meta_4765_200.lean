import PEqualNP.Defs
open PEqualNP.SplitCount

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_4765_200
  (charge : ∀(q N : Nat) (I : Fin N→Fin N→Prop) , 0<q → (∀p,∃l,I p l) → (∀l,∃p,I p l) → ∀(s o : Nat) (W : Nat→Set ((Fin N→Bool)×(Fin N→Bool))) (G : Nat→Nat×Nat),
  let k:=N+N
  let z:=fun _ : Fin N=>false
  let T:=fun (b : Bool) (w : Nat)=>{i : Fin N | (if b then (unitInput i,z) else (z,unitInput i))∈W w}
  let E:=Set.ncard {j : Fin s | ∃ b : Bool,(T b (G j.val).1 ∩ T b (G j.val).2).Nonempty}
  o<k+s →
  (∀i : Fin N,W i.val={x|x.1 i=true} ∧ W (N+i.val)={x|x.2 i=true}) →
  (∀j<s, let a:=(G j).1;let b:=(G j).2; max a b<k+j ∧ W (k+j)∈[W a∪W b,W a,∅,W a∩W b]) →
  (∀x : (Fin N→Bool)×(Fin N→Bool),Fintype.card {l // x.2 l=true}≤q →
    (x∈W o ↔ ∃p l,I p l ∧ x.1 p=true ∧ x.2 l=true)) →
  k+E≤s+1)
  (sparse : ∀(q N : Nat) (I : Fin N→Fin N→Prop) [DecidableRel I], 200<q → N=q^2+q+1 →
  (∀l,Fintype.card {p//I p l}=q+1) → (∀p r,p≠r→∃!l,I p l ∧ I r l) →
  ∀(s o : Nat) (W : Nat→Set ((Fin N→Bool)×(Fin N→Bool))) (G : Nat→Nat×Nat),
  let k:=N+N
  let z:=fun _ : Fin N=>false
  let T:=fun (b : Bool) (w : Nat)=>{i : Fin N | (if b then (unitInput i,z) else (z,unitInput i))∈W w}
  let E:=Set.ncard {j : Fin s | ∃ b : Bool,(T b (G j.val).1 ∩ T b (G j.val).2).Nonempty}
  o<k+s →
  (∀i : Fin N,W i.val={x|x.1 i=true} ∧ W (N+i.val)={x|x.2 i=true}) →
  (∀j<s, let a:=(G j).1;let b:=(G j).2; max a b<k+j ∧ W (k+j)∈[W a∪W b,W a,∅,W a∩W b]) →
  (∀x : (Fin N→Bool)×(Fin N→Bool),Fintype.card {l // x.2 l=true}≤q →
    (x∈W o ↔ ∃p l,I p l ∧ x.1 p=true ∧ x.2 l=true)) →
  (∃j : Fin s,∃b:Bool,let v:=k+j.val; (T b v).Nonempty ∧ ¬∃a<v,∃d<v,T b v=T b a∪T b d) →
  0<E → 100*(k+E-1)<N*q → N*q≤100*s) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           (∀ (x9 : Finset (Fin x2)), ∀ x10 ∈ x9, x1 + (2 : ℕ) ≤ x9.card + Fintype.card { x12 : Fin x2 // x3 x12 x10 ∧ ∀ x13 ∈ x9.erase x10, ¬x3 x12 x13 }) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               have x15 : Bool → ℕ → Set (Fin x2) := fun (x15 : Bool) (x16 : ℕ) => {x17 : Fin x2 | (if x15 = Bool.true then (x14 x17, fun (_x18 : Fin x2) => Bool.false) else (fun (_x18 : Fin x2) => Bool.false, x14 x17)) ∈ x12 x16};               x11 < x13 + x10 → (∀ (x17 : Fin x2), x12 ↑x17 = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.1 x17 = Bool.true} ∧ x12 (x2 + ↑x17) = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.2 x17 = Bool.true}) → (∀ x18 < x10, ∃ (x20 : ℕ) (x21 : ℕ), Max.max x20 x21 < x13 + x18 ∧ x12 (x13 + x18) ∈ [x12 x20 ∪ x12 x21, x12 x20, ∅, x12 x20 ∩ x12 x21]) → (∀ (x19 : (Fin x2 → Bool) × (Fin x2 → Bool)), Fintype.card { x20 : Fin x2 // x19.2 x20 = Bool.true } ≤ x1 → (x19 ∈ x12 x11 ↔ ∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19.1 x21 = Bool.true ∧ x19.2 x22 = Bool.true)) → (∃ x20 < x10, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x15 x21 (x13 + x20) ∧ x23 ∈ x15 x21 (x13 + x20) ∧ ¬∃ x24 < x13 + x20, ∃ x25 < x13 + x20, x15 x21 (x13 + x20) = x15 x21 x24 ∪ x15 x21 x25) → x2 * x1 ≤ (100 : ℕ) * x10 := by
  intro q N I inst hq size deg pu _ s o W
  dsimp only
  intro out raw gates corr novel
  classical
  choose getA getB hb using gates
  let G : Nat→Nat×Nat:=fun j=>if h:j<s then (getA j h,getB j h) else (0,0)
  have pair (j : Nat) (hj:j<s) : max (G j).1 (G j).2<N+N+j ∧
      W (N+N+j)∈[W (G j).1∪W (G j).2,W (G j).1,∅,W (G j).1∩W (G j).2]:=by simpa only [G,dite_eq_left hj] using hb j hj
  let T := fun (b : Bool) (w : Nat)=> {i : Fin N | (if b then (unitInput i,fun _=>false) else (fun _=>false,unitInput i))∈W w}
  let E := Set.ncard {j : Fin s | ∃ b : Bool,(T b (G j.val).1 ∩ T b (G j.val).2).Nonempty}
  have n : 1<N:=by omega
  let : Nontrivial (Fin N):=Fin.nontrivial_iff_two_le.mpr n
  have points (p : Fin N) : ∃l,I p l := by
    obtain ⟨r,rp⟩:=exists_ne p
    obtain ⟨l,hi,_⟩:=pu p r (Ne.symm rp)
    exact ⟨l,hi.1⟩
  have lines (l : Fin N) : ∃p,I p l:=by
    have ne:Nonempty {p // I p l}:=Fintype.card_pos_iff.mp (by rw [deg];omega)
    obtain ⟨⟨p,hp⟩⟩:=ne;exact ⟨p,hp⟩
  have price : N+N+E≤s+1:=charge q N I (by omega) points lines s o W G out raw pair corr
  obtain ⟨j,js,b,i,_,_,hi,_,hn⟩:=novel
  have no : ¬∃a<N+N+j,∃d<N+N+j,T b (N+N+j)=T b a∪T b d := hn
  have hi' : i∈T b (N+N+j):=hi
  have hot : 0<E:=by
    apply (Set.ncard_pos (Set.toFinite _)).mpr
    refine ⟨⟨j,js⟩,b,?_⟩
    change (T b (G j).1 ∩ T b (G j).2).Nonempty
    obtain ⟨lt,row⟩:=pair j js
    simp only [List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with eq|eq|eq|eq
    · exact (no ⟨(G j).1,by omega,(G j).2,by omega,by ext;simp [T,eq]⟩).elim
    · exact (no ⟨(G j).1,by omega,(G j).1,by omega,by ext;simp [T,eq]⟩).elim
    · simp [T,eq] at hi'
    · refine ⟨i,?_⟩;simpa [T,eq] using hi'
  by_cases low : q≤200
  · exact (Nat.mul_le_mul_left N low).trans (by omega)
  by_cases budget : 100*(N+N+E-1)<N*q
  · exact sparse q N I (by omega) size deg pu s o W G out raw pair corr ⟨⟨j,js⟩,b,⟨i,hi'⟩,no⟩ hot budget
  · omega
