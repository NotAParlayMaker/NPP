import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3515_572
(protocol : ∃ k≤14, ∃ (P : ℕ → Finset (ℕ×ℕ)) (B : ℕ → Finset (List ℕ)),
  (∀ i<10,(∀ e∈P i,e.1=i ∨ e.2=i) ∧ (∀ c∈B i,i∈c)) ∧
  (∀ j<k,∃ a b : ℕ,a<b ∧ b<10+j ∧
    ((P (10+j)⊆P a∪P b ∧ B (10+j)⊆B a∩B b) ∨
     (P (10+j)⊆P a∩P b ∧ B (10+j)⊆B a∪B b))) ∧
  (∀ e∈([(0,6),(0,7),(1,6),(1,8),(2,7),(2,9),(3,6),(3,9),(4,8),(4,9),(5,7),(5,8)] : List (ℕ×ℕ)),e∈P (9+k)) ∧
  (∀ c∈([[6,7,8,9],[0,1,3,7,8,9],[0,2,5,6,8,9],[0,1,2,3,5,8,9],[1,4,5,6,7,9],[0,1,3,4,5,7,9],[0,1,2,4,5,6,9],[2,3,4,6,7,8],[0,1,2,3,4,7,8],[0,2,3,4,5,6,8],[1,2,3,4,5,6,7],[0,1,2,3,4,5]] : List (List ℕ)),c∈B (9+k)))
(duality : ∀ x : Fin 10 → Bool,
  (∀ c∈([[6,7,8,9],[0,1,3,7,8,9],[0,2,5,6,8,9],[0,1,2,3,5,8,9],[1,4,5,6,7,9],[0,1,3,4,5,7,9],[0,1,2,4,5,6,9],[2,3,4,6,7,8],[0,1,2,3,4,7,8],[0,2,3,4,5,6,8],[1,2,3,4,5,6,7],[0,1,2,3,4,5]] : List (List ℕ)),∃ i : Fin 10,i.val∈c ∧ x i=true) ↔
  ∃ p q : Fin 10,(p.val,q.val)∈([(0,6),(0,7),(1,6),(1,8),(2,7),(2,9),(3,6),(3,9),(4,8),(4,9),(5,7),(5,8)] : List (ℕ×ℕ)) ∧ x p=true ∧ x q=true) : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ x1.size ≤ (14 : ℕ) ∧ ∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (10 : ℕ)) (x4 : Fin (10 : ℕ)), (↑x3, ↑x4) ∈ [((0 : ℕ), (6 : ℕ)), ((0 : ℕ), (7 : ℕ)), ((1 : ℕ), (6 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (7 : ℕ)), ((2 : ℕ), (9 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (9 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (9 : ℕ)), ((5 : ℕ), (7 : ℕ)), ((5 : ℕ), (8 : ℕ))] ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  classical
  obtain ⟨k,sz,P,B,leaf,steps,lastP,lastB⟩ := protocol
  let OR (j : Fin k) (a b : ℕ) := P (10+j.val)⊆P a∪P b ∧ B (10+j.val)⊆B a∩B b
  let AND (j : Fin k) (a b : ℕ) := P (10+j.val)⊆P a∩P b ∧ B (10+j.val)⊆B a∪B b
  have split (j : Fin k) : ∃ a b : ℕ,a<b ∧ b<10+j.val ∧ (OR j a b ∨ AND j a b) := steps j j.isLt
  choose a b h using split
  let g (j : Fin k) : Gate := ⟨if OR j (a j) (b j) then .or else .and,[a j,b j]⟩
  let C : Circuit := ⟨List.ofFn g,9+k⟩
  have shape (j : Fin k) : (g j).op=.and ∨ (g j).op=.or := by by_cases v : OR j (a j) (b j) <;> simp [g,v]
  have atj (j : Fin k) : gateAt C j.val=g j := by
    unfold gateAt
    change (List.ofFn g).getD j.val _=_
    rw [List.getD_eq_getElem _ _ (by simpa using j.isLt)]
    simp
  have memg (t : Gate) (m : t∈C.gates) : ∃ j,g j=t := List.mem_ofFn.mp m
  have ao : IsAO2 10 C := by
    refine ⟨fun t ht => ?_,?_,fun t ht => ?_⟩
    · obtain ⟨j,rfl⟩ := memg t ht
      exact shape j
    · intro j hj v hv
      have lt : j<k := by simpa [C] using hj
      let r : Fin k := ⟨j,lt⟩
      change v∈(gateAt C r.val).inputs at hv
      rw [atj] at hv
      change v∈[a r,b r] at hv
      have ab := (h r).1
      have bj := (h r).2.1
      rcases List.mem_cons.mp hv with rfl|hh
      · exact ab.trans bj
      · exact List.mem_singleton.mp hh ▸ bj
    · obtain ⟨j,rfl⟩ := memg t ht
      rfl
  refine ⟨C,ao,?_,by change (List.ofFn g).length≤14;simpa using sz,?_⟩
  · intro t ht
    obtain ⟨j,rfl⟩ := memg t ht
    simp [g,(h j).1.ne]
  intro x
  let W := C.wires (List.ofFn x)
  let tick (v : ℕ) := W.getD v false
  let step (ws : List Bool) (t : Gate) := ws++[t.op.eval (t.inputs.map fun u => ws.getD u false)]
  have length (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length=xs.length+gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons hd tl ih => rw [List.foldl_cons,ih];simp [step];omega
  have prefixValue (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i<xs.length) : (gs.foldl step xs).getD i false=xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons hd tl ih =>
      rw [List.foldl_cons,ih _ (by simp [step];omega)]
      exact List.getD_append _ _ _ _ hi
  have raw (i : Fin 10) : tick i.val=x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false=_
    rw [prefixValue _ _ _ (by simpa using i.isLt),List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    exact List.getElem_ofFn ..
  have gate (j : Fin k) : tick (10+j.val)=(g j).op.eval [tick (a j),tick (b j)] := by
    let V := (C.gates.take j.val).foldl step (List.ofFn x)
    have len : V.length=10+j.val := by simp [V,length,C,Nat.min_eq_left j.isLt.le]
    have dec : W=(g j::C.gates.drop (j.val+1)).foldl step V := by
      have row : C.gates[j.val]'(by simpa [C] using j.isLt)=g j := by simp [C]
      change C.gates.foldl step (List.ofFn x)=_
      simp only [V,←row,←List.foldl_append,←List.drop_eq_getElem_cons,List.take_append_drop]
    have read (i) (lt : i<10+j.val) : tick i=V.getD i false := by
      unfold tick
      rw [dec,prefixValue _ _ _ (len ▸ lt)]
    rw [read _ ((h j).1.trans (h j).2.1),read _ (h j).2.1]
    unfold tick
    rw [dec,List.foldl_cons,prefixValue _ _ _ (by simp [step,len])]
    rw [show step V (g j)=V++[(g j).op.eval [V.getD (a j) false,V.getD (b j) false]] by rfl,
      List.getD_append_right _ _ _ _ len.le]
    simp [len]
  let Good (w : ℕ) := (∀ p q : Fin 10,(p.val,q.val)∈P w → x p=true → x q=true → tick w=true) ∧
    ∀ c∈B w,(∀ i : Fin 10,i.val∈c → x i=false) → tick w=false
  have inv (w : ℕ) : w<10+k → Good w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro lt
      by_cases low : w<10
      · let i : Fin 10 := ⟨w,low⟩
        have val : tick w=x i := raw i
        constructor
        · intro p q ep hp hq
          rcases (leaf w low).1 _ ep with left|right
          · exact val.trans ((show p=i from Fin.ext left) ▸ hp)
          · exact val.trans ((show q=i from Fin.ext right) ▸ hq)
        · intro c hc off
          exact val.trans (off i ((leaf w low).2 c hc))
      · obtain ⟨j,rfl⟩ : ∃ j : Fin k,w=10+j.val := ⟨⟨w-10,by omega⟩,by simp;omega⟩
        have al := (h j).1.trans (h j).2.1
        have bl := (h j).2.1
        obtain ⟨ap,an⟩ := ih _ al (al.trans lt)
        obtain ⟨bp,bn⟩ := ih _ bl (bl.trans lt)
        by_cases cond : OR j (a j) (b j)
        · have ev : tick (10+j.val)=(tick (a j)||tick (b j)) := by
            rw [gate j]
            simp only [g,cond,ite_true,ite_false]
            cases tick (a j) <;> cases tick (b j) <;> rfl
          constructor
          · intro p q m hp hq
            rcases Finset.mem_union.mp (cond.1 m) with ha|hb
            · simp [ev,ap p q ha hp hq]
            · simp [ev,bp p q hb hp hq]
          · intro c m off
            obtain ⟨m1,m2⟩ := Finset.mem_inter.mp (cond.2 m)
            simp [ev,an _ m1 off,bn _ m2 off]
        · have af := (h j).2.2.resolve_left cond
          have ev : tick (10+j.val)=(tick (a j)&&tick (b j)) := by
            rw [gate j]
            simp only [g,cond,ite_true,ite_false]
            cases tick (a j) <;> cases tick (b j) <;> rfl
          constructor
          · intro p q m hp hq
            obtain ⟨m1,m2⟩ := Finset.mem_inter.mp (af.1 m)
            simp [ev,ap p q m1 hp hq,bp p q m2 hp hq]
          · intro c m off
            rcases Finset.mem_union.mp (af.2 m) with m1|m2
            · simp [ev,an _ m1 off]
            · simp [ev,bn _ m2 off]
  obtain ⟨pos,neg⟩ := inv (9+k) (by omega)
  constructor
  · intro yes
    apply (duality x).mp
    intro c hc
    by_contra! off
    have no := neg c (lastB c hc) (fun i hi => Bool.eq_false_iff.mpr (off i hi))
    change tick (9+k)=true at yes
    simp [no] at yes
  · rintro ⟨p,q,e,hp,hq⟩
    exact pos p q (lastP _ e) hp hq
