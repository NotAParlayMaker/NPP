import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1963_1
    (h1 : ∀ (n : ℕ) (C : Circuit) (i j a b : ℕ), Monotone2 C → ReadsBack n C →
  (∀ g ∈ C.gates, g.inputs.length = 2) → i < j → j < C.size → a < n → b < n →
  (∃ L : List Bool, L.length = n ∧ C.eval L = true) →
  ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size+1=C.size ∧
    ∀ (L : List Bool) (s : Bool), L.length=n → C.eval L=s →
      (((C.wires L).getD (n+i) false = s ∨ (C.wires L).getD (n+j) false = s) →
        (L.getD a false && L.getD b false) = s) → D.eval L=s)
    (h2 : let S : Finset (Fin 13) := {0,1,3,9}
let X := fun p l : Fin 13 => (List.ofFn fun u : Fin 13 => decide (u=p)) ++ List.ofFn fun u : Fin 13 => decide (u=l)
let good := fun C : Circuit =>
  (∀ p l, p-l ∈ S → C.eval (X p l)=true) ∧
   ∀ Q : Finset (Fin 13), Q.card=4 → (∀ l, (Q.filter fun p => p-l ∈ S).card ≤ 2) →
     C.eval ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++ List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ S))=false
∀ C : Circuit, Monotone2 C → ReadsBack 26 C → good C → C.size<64 →
  (∀ g ∈ C.gates, g.inputs.length=2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
  2 ≤ PEqualNP.TopForm.andPairs 26 C →
  (∀ i j : ℕ, i < j → j < C.size → ∀ p l : Fin 13, p-l ∈ S →
    ∃ u v : Fin 13, u-v ∈ S ∧ (u ≠ p ∨ v ≠ l) ∧
      ((C.wires (X u v)).getD (26+i) false = true ∨ (C.wires (X u v)).getD (26+j) false = true)) →
  ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ good D ∧ D.size < C.size) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  classical
  let S : Finset (Fin 13) := {0,1,3,9}
  let X := fun p l : Fin 13 => (List.ofFn fun u : Fin 13 => decide (u=p)) ++ List.ofFn fun u : Fin 13 => decide (u=l)
  let Y := fun Q : Finset (Fin 13) => (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
    List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ S)
  refine fun C hm hr hfit hs _ hbin hpairs => ?_
  apply Classical.byContradiction
  intro noSmall
  apply noSmall
  apply h2 C hm hr hfit hs hbin hpairs
  intro i j hij hj p l hpl
  by_contra! hthin
  have hzero : (0 : Fin 13)-0 ∈ S := by decide +kernel
  obtain ⟨D,hmD,hrD,hsize,hrow⟩ := h1 26 C i j p.val (13+l.val) hm hr (fun g hg => (hbin g hg).1)
    hij hj (by omega) (by omega) ⟨X 0 0, by simp [X], hfit.1 0 0 hzero⟩
  have leftCoord {m : ℕ} (f g : Fin m → Bool) (u : Fin m) :
      (List.ofFn f ++ List.ofFn g).getD u.val false = f u := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp)]
    simp
  have rightCoord {m : ℕ} (f g : Fin m → Bool) (u : Fin m) :
      (List.ofFn f ++ List.ofFn g).getD (m+u.val) false = g u := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
    simp
  apply noSmall
  refine ⟨D,hmD,hrD,⟨?_,?_⟩,by omega⟩
  · intro u v huv
    apply hrow (X u v) true (by simp [X]) (hfit.1 u v huv)
    intro h
    have hsame : u=p ∧ v=l := by
      by_contra! hn
      have hn' : u ≠ p ∨ v ≠ l := by
        by_cases hp : u=p
        · exact Or.inr (hn hp)
        · exact Or.inl hp
      obtain ⟨hni,hnj⟩ := hthin u v huv hn'
      rcases h with hi | hj'
      · rw [show (C.wires (X u v)).getD (26+i) false = true from hi] at hni
        simp at hni
      · rw [show (C.wires (X u v)).getD (26+j) false = true from hj'] at hnj
        simp at hnj
    rcases hsame with ⟨rfl,rfl⟩
    change ((List.ofFn _ ++ List.ofFn _).getD u.val false &&
      (List.ofFn _ ++ List.ofFn _).getD (13+v.val) false)=true
    rw [leftCoord,rightCoord]
    simp
  · intro Q h4 hQ
    apply hrow (Y Q) false (by simp [Y]) (hfit.2 Q h4 hQ)
    intro _
    change ((List.ofFn _ ++ List.ofFn _).getD p.val false &&
      (List.ofFn _ ++ List.ofFn _).getD (13+l.val) false)=false
    rw [leftCoord,rightCoord]
    by_cases hin : p ∈ Q
    · have hout : ¬ ∀ t ∈ Q, t-l ∉ S := fun h => h p hin hpl
      rw [decide_eq_false hout]
      exact Bool.and_false _
    · rw [decide_eq_false hin]
      rfl
