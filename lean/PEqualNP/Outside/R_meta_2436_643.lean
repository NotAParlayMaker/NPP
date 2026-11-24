import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 65000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_2436_643
 (front : ∃ (A : Circuit) (port : Fin 36 → Nat), Monotone2 A ∧ ReadsBack 44 A ∧
  A.size ≤ 87 ∧ A.output < 44+A.size ∧ (∀ i, port i < 44+A.size) ∧
  (∀ i : Nat, i ∈ [0,1,16] → ∃ g ∈ A.gates, i ∈ g.inputs) ∧
  ∀ x : Fin 42 → Bool, let y : Fin 21 → Bool := fun i => x (Fin.ofNat 42 (([22,23,26,29,36,38,2,5,1,15,17,6,3,16,18,9,19,0,8,12,10] : List Nat).getD i.val 0))

  (A.eval ((List.ofFn x) ++ [x 0 || x 1, x 16 || (x 0 || x 1)]) = true ↔ ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ v.val ∉ [22,23,26,29,36,38] ∧ (v.val+21-u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∧ x u=true ∧ x v=true) ∧
  List.ofFn (fun i => (A.wires ((List.ofFn x) ++ [x 0 || x 1, x 16 || (x 0 || x 1)])).getD (port i) false) = ((List.ofFn y) ++ List.ofFn (fun i : Fin 15 =>
      let w := ([1835,2660,3201,3666,3248,3728,3681,3411,3441,3156,2435,2420,2690,3488,2915] : List Nat).getD i.val 0
      (y (Fin.ofNat 21 (6+w % 16)) || y (Fin.ofNat 21 (6+w/16 % 16))) || y (Fin.ofNat 21 (6+w/256)))))
 (graft : ∀ (n k : Nat) (A B : Circuit) (port : Fin k → Nat),
  Monotone2 A → ReadsBack n A → A.output < n+A.size →
  Monotone2 B → ReadsBack k B → B.output < k+B.size → (∀ i, port i<n+A.size) →
  ∃ C : Circuit, Monotone2 C ∧ ReadsBack n C ∧ C.size ≤ A.size+B.size+1 ∧
  (∀ g ∈ A.gates, g ∈ C.gates) ∧
  ∀ x : List Bool, x.length=n →
  C.eval x = (A.eval x || B.eval (List.ofFn fun i => (A.wires x).getD (port i) false)))
 (core : ∃ B : Circuit, Monotone2 B ∧ ReadsBack 36 B ∧ B.output<36+B.size ∧ B.size≤34 ∧
  ∀ y : Fin 21 → Bool, B.eval ((List.ofFn y) ++ List.ofFn (fun i : Fin 15 =>
      let w := ([1835,2660,3201,3666,3248,3728,3681,3411,3441,3156,2435,2420,2690,3488,2915] : List Nat).getD i.val 0
      (y (Fin.ofNat 21 (6+w % 16)) || y (Fin.ofNat 21 (6+w/16 % 16))) || y (Fin.ofNat 21 (6+w/256)))) = true ↔ ∃ (a : Fin 6) (e : Fin 15), (([3,5,9,17,33,6,10,18,34,12,20,36,24,40,48] : List Nat).getD e.val 0).testBit a.val = true ∧ y (Fin.ofNat 21 a.val)=true ∧ y (Fin.ofNat 21 (6+e.val))=true) :
∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     x2 < x3 ∧       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) ∧         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) ∧           (∀ (x5 : Fin (42 : ℕ)), List.count ↑x5 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x7 ∈ x4.gates, ↑x5 ∈ x7.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x4 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧                 x4.size ≤ (122 : ℕ) ∧                   ∀ (x5 : Fin (42 : ℕ) → Bool),                     have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;                     x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  have geom : ∀ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val+21-u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ↔ (u.val < 21 ∧ 21 ≤ v.val ∧ v.val ∉ [22,23,26,29,36,38] ∧ (v.val+21-u.val) % 21 ∈ ([0,5,7,17,20] : List Nat)) ∨
    ∃ (a : Fin 6) (e : Fin 15), (([3,5,9,17,33,6,10,18,34,12,20,36,24,40,48] : List Nat).getD e.val 0).testBit a.val = true ∧ u=Fin.ofNat 42 (([22,23,26,29,36,38,2,5,1,15,17,6,3,16,18,9,19,0,8,12,10] : List Nat).getD ((Fin.ofNat 21 (6+e.val)).val) 0) ∧ v=Fin.ofNat 42 (([22,23,26,29,36,38,2,5,1,15,17,6,3,16,18,9,19,0,8,12,10] : List Nat).getD ((Fin.ofNat 21 a.val).val) 0) := by decide +kernel
  obtain ⟨A,port,ha,ar,asz,ao,pv,rd,front⟩ := front
  obtain ⟨B,hb,br,bo,bs,core⟩ := core
  obtain ⟨C,hc,cr,cs,sub,ev⟩ := graft 44 36 A B port ha ar ao hb br bo pv
  refine ⟨1,16,42, C, Or.inl rfl, by decide, by decide, by decide, ?_,hc,cr, by omega, ?_⟩
  · intro i hi
    have step : ∀ j : Fin 42, List.count j.val [0,1,16,42]=1 → j.val ∈ ([0,1,16] : List Nat) := by decide +kernel
    obtain ⟨g,hg,hin⟩ := rd i.val (step i hi)
    exact ⟨g,sub g hg,hin⟩
  · intro x
    let y : Fin 21 → Bool := fun i => x (Fin.ofNat 42 (([22,23,26,29,36,38,2,5,1,15,17,6,3,16,18,9,19,0,8,12,10] : List Nat).getD (i.val) 0))
    let z := ((List.ofFn x) ++ [x 0 || x 1, x 16 || (x 0 || x 1)])
    let v43 : Fin 43 → Bool := Fin.lastCases (x 0 || x 1) x
    have eq43 : List.ofFn v43 = (List.ofFn x)++[x 0 || x 1] := by
      rw [List.ofFn_succ']; rfl
    have eq44 : List.ofFn (Fin.lastCases (v43 16 || v43 42) v43) = z := by
      rw [List.ofFn_succ']
      have reduce : (fun i : Fin 43 => Fin.lastCases (v43 16 || v43 42) v43 i.castSucc) = v43 := by
        funext i; simp
      rw [reduce,eq43]
      change ((List.ofFn x)++[_])++[_] = (List.ofFn x)++[_,_]
      rw [List.append_assoc]
      rfl
    change C.eval (List.ofFn (Fin.lastCases (v43 16 || v43 42) v43))=true ↔ _
    obtain ⟨outside,ports⟩ := front x
    rw [eq44,ev z (by simp [z]),show List.ofFn (fun i => (A.wires z).getD (port i) false) = _ from ports,Bool.or_eq_true,core y,outside]
    constructor
    · rintro (⟨u,v,geo,hu,hv⟩|⟨a,e,h,ha,he⟩)
      · exact ⟨u,v,(geom u v).mpr (Or.inl geo),hu,hv⟩
      · refine ⟨_,_,(geom _ _).mpr (Or.inr ⟨a,e,h,rfl,rfl⟩),?_,?_⟩
        · exact he
        · exact ha
    · rintro ⟨u,v,geo,hu,hv⟩
      rcases (geom u v).mp geo with h | ⟨a,e,h,rfl,rfl⟩
      · exact Or.inl ⟨u,v,h,hu,hv⟩
      · exact Or.inr ⟨a,e,h,hv,hu⟩
