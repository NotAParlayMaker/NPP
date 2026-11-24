import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1774_527
    (shape : ∀ (n : ℕ) (C : Circuit) (j : ℕ), Monotone2 C →
      (∃ u v p q : Fin n, Owns n C j u v ∧ Owns n C j p q ∧
        u≠p ∧ u≠q ∧ v≠p ∧ v≠q) →
      (∀ w ∈ (gateAt C j).inputs, n≤w ∧ w<n+j) ∧
      ((∀ u : Fin n, gateVal n C j (pairInput u u) = false) →
        ∃ a b, (gateAt C j).inputs = [n+a,n+b] ∧ a<j ∧ b<j ∧ a≠b ∧
        (have role : Fin n → Bool × Bool := fun u =>
          (gateVal n C a (pairInput u u),gateVal n C b (pairInput u u));
         (∀ u v : Fin n, Owns n C j u v →
            (role u=(true,false) ∧ role v=(false,true)) ∨
            (role u=(false,true) ∧ role v=(true,false))) ∧
         ∀ u v : Fin n, role u=(true,false) → role v=(false,true) →
           gateVal n C j (pairInput u v)=true)))
    (repairActive :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      have useful : Circuit → Prop := fun C => ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v;
      have bad : Circuit → Set ℕ := fun C => {j | ∃ u v p q : Fin n,
        G.Adj u v ∧ G.Adj p q ∧ Owns n C j u v ∧ Owns n C j p q ∧ u≠p ∧ u≠q ∧ v≠p ∧ v≠q};
      ∀ (C : Circuit) (j : ℕ), IsMinimalMonoCircuit n C →
        circuitFun n C=graphFun G ∅ → useful C → j∈bad C →
        (∀ i<j, i∉bad C) →

        (∀ w∈(gateAt C j).inputs, n≤w ∧ w<n+j) →
        (∃ u : Fin n, gateVal n C j (pairInput u u)=true) →

        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size≤C.size ∧
          useful D ∧ (bad D).ncard < (bad C).ncard)
    (repairAlternating :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      have useful : Circuit → Prop := fun C => ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v;
      have bad : Circuit → Set ℕ := fun C => {j | ∃ u v p q : Fin n,
        G.Adj u v ∧ G.Adj p q ∧ Owns n C j u v ∧ Owns n C j p q ∧ u≠p ∧ u≠q ∧ v≠p ∧ v≠q};
      ∀ (C : Circuit) (j : ℕ), IsMinimalMonoCircuit n C →
        circuitFun n C=graphFun G ∅ → useful C → j∈bad C →
        (∀ i<j, i∉bad C) →

        (∀ u : Fin n, gateVal n C j (pairInput u u)=false) →
        (∃ a b, (gateAt C j).inputs=[n+a,n+b] ∧ a<j ∧ b<j ∧ a≠b ∧
          ∀ k ∈ [a,b], ∀ u v : Fin n, Owns n C j u v →
            gateVal n C k (pairInput u u) ≠ gateVal n C k (pairInput v v)) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size≤C.size ∧
          useful D ∧ (bad D).ncard < (bad C).ncard) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  classical
  intro n G decI htri hfour useful cost C hmin heval huse hpos
  let B : Circuit → Set ℕ := fun D => {j | ∃ u v p q : Fin n,
    G.Adj u v ∧ G.Adj p q ∧ Owns n D j u v ∧ Owns n D j p q ∧ u≠p ∧ u≠q ∧ v≠p ∧ v≠q}
  have existsBad : ∃ j, j∈B C := by
    by_contra hnone
    have hempty : B C=∅ := by
      ext j
      simp only [Set.mem_empty_iff_false,iff_false]
      intro hj
      exact hnone ⟨j,hj⟩
    change 0 < (B C).ncard at hpos
    rw [hempty,Set.ncard_empty] at hpos
    omega
  let j := Nat.find existsBad
  have badj : j∈B C := Nat.find_spec existsBad
  have firstBad : ∀ i<j, i∉B C := by
    intro i hi
    exact Nat.find_min existsBad hi
  have witnesses := badj
  obtain ⟨u,v,p,q,_h1,_h2,huv,hpq,hup,huq,hvp,hvq⟩ := witnesses
  obtain ⟨readBounds,roles⟩ := shape n C j hmin.1 ⟨u,v,p,q,huv,hpq,hup,huq,hvp,hvq⟩
  by_cases off : ∀ w : Fin n, gateVal n C j (pairInput w w)=false
  · obtain ⟨a,b,hin,ha,hb,hne,orient,_cross⟩ := roles off
    apply repairAlternating n G htri hfour C j hmin heval huse badj firstBad off
    refine ⟨a,b,hin,ha,hb,hne,?_⟩
    intro k hk s t hown
    have pair := orient s t hown
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with e | e <;> subst k <;> rcases pair with ⟨e1,e2⟩ | ⟨e1,e2⟩
    · have h1 := congrArg Prod.fst e1
      have h2 := congrArg Prod.fst e2
      change gateVal n C a (pairInput s s) = _ at h1
      change gateVal n C a (pairInput t t) = _ at h2
      rw [h1,h2]
      decide
    · have h1 := congrArg Prod.fst e1
      have h2 := congrArg Prod.fst e2
      change gateVal n C a (pairInput s s) = _ at h1
      change gateVal n C a (pairInput t t) = _ at h2
      rw [h1,h2]
      decide
    · have h1 := congrArg Prod.snd e1
      have h2 := congrArg Prod.snd e2
      change gateVal n C b (pairInput s s) = _ at h1
      change gateVal n C b (pairInput t t) = _ at h2
      rw [h1,h2]
      decide
    · have h1 := congrArg Prod.snd e1
      have h2 := congrArg Prod.snd e2
      change gateVal n C b (pairInput s s) = _ at h1
      change gateVal n C b (pairInput t t) = _ at h2
      rw [h1,h2]
      decide
  · push Not at off
    obtain ⟨w,hw⟩ := off
    have active : ∃ w : Fin n, gateVal n C j (pairInput w w)=true := ⟨w,by simpa using hw⟩
    exact repairActive n G htri hfour C j hmin heval huse badj firstBad readBounds active
