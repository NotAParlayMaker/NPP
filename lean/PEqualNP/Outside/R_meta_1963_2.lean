import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover

theorem PEqualNP.Outside.R_meta_1963_2
    (erase : ∀ (n : ℕ) (C : Circuit) (j w : ℕ), Monotone2 C → ReadsBack n C → j<C.size →
    (w<n+j ∨ w=n+C.size) → ∃ D, Monotone2 D ∧ ReadsBack n D ∧ D.size<C.size ∧
      ∀ (x : List Bool) (b : Bool), x.length=n → C.eval x=b →
        ((C.wires x).getD (n+j) false=b → (C.wires x).getD w false=b) → D.eval x=b)
    (normalize : let bits := fun (S : Finset (Fin 13)) => List.ofFn (fun v => decide (v∈S))
    let req := fun (g : List Bool → Bool → Prop) =>
      (∀ p l, p∈singerLines3 l → g (bits {p} ++ bits {l}) true) ∧
      ∀ Q∈quadrangles singerLines3, g (bits Q ++ bits (missLines singerLines3 Q)) false
    let model := fun (C : Circuit) => IsAO2 26 C ∧
      (∀ g∈C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) ∧ 2≤andPairs 26 C ∧
      req (fun x b => C.eval x=b)
    ∀ C, model C → ∃ D, model D ∧ D.size=C.size ∧
    let s := (gateAt D 0).inputs.toFinset
    s={0,1} ∨ s={13,14} ∨ s={0,13} ∨ s={0,14})
    (lower : let bits := fun (S : Finset (Fin 13)) => List.ofFn (fun v => decide (v∈S))
    let req := fun (g : List Bool → Bool → Prop) =>
      (∀ p l, p∈singerLines3 l → g (bits {p} ++ bits {l}) true) ∧
      ∀ Q∈quadrangles singerLines3, g (bits Q ++ bits (missLines singerLines3 Q)) false
    let model := fun (C : Circuit) => IsAO2 26 C ∧
      (∀ g∈C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) ∧ 2≤andPairs 26 C ∧
      req (fun x b => C.eval x=b)
    ∀ D, model D → (let s := (gateAt D 0).inputs.toFinset
    s={0,1} ∨ s={13,14} ∨ s={0,13} ∨ s={0,14}) →
    (∀ j < D.size, ∀ w : ℕ, (w<26+j ∨ w=26+D.size) →
      ¬req (fun x b => (D.wires x).getD (26+j) false=b → (D.wires x).getD w false=b)) → 64≤D.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro Delta Correct Nested C mono back tests short nested strict pairs
  let bits := fun (S : Finset (Fin 13)) => List.ofFn (fun v => decide (v∈S))
  let req := fun (g : List Bool → Bool → Prop) =>
    (∀ p l, p∈singerLines3 l → g (bits {p} ++ bits {l}) true) ∧
    ∀ Q∈quadrangles singerLines3, g (bits Q ++ bits (missLines singerLines3 Q)) false
  have inc : ∀ p l : Fin 13, p-l∈Delta ↔ p∈singerLines3 l := by decide
  have quad (Q : Finset (Fin 13)) : Q∈quadrangles singerLines3 ↔
      Q.card=4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u-k∈Delta)).card≤2 := by
    have eq (k : Fin 13) : Q∩singerLines3 k=Q.filter (fun u=>u-k∈Delta) := by ext u;simp [inc u k]
    simp only [quadrangles,Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and,eq]
  have tail (Q : Finset (Fin 13)) : bits (missLines singerLines3 Q)=
      List.ofFn (fun v : Fin 13 => decide (∀ u∈Q, u-v∉Delta)) := by
    apply congrArg List.ofFn
    funext v
    apply decide_eq_decide.mpr
    simp only [missLines,Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,←inc]
    exact ⟨fun h u hu e => h e hu,fun h u e hu => h u hu e⟩
  have corr (B : Circuit) : Correct B ↔ req (fun x b => B.eval x=b) := by
    constructor
    · rintro ⟨pos,neg⟩
      exact ⟨fun p l e => by simpa [bits] using pos p l ((inc p l).mpr e),
        fun Q hQ => by rw [tail];exact neg Q ((quad Q).mp hQ).1 ((quad Q).mp hQ).2⟩
    · rintro ⟨pos,neg⟩
      exact ⟨fun p l e => by simpa [bits] using pos p l ((inc p l).mp e),
        fun Q c h => by have z:=neg Q ((quad Q).mpr ⟨c,h⟩);rw [tail] at z;exact z⟩
  have ao : IsAO2 26 C := ⟨fun g hg => by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono g hg).1,
    back,fun g hg => (strict g hg).1⟩
  obtain ⟨D,⟨dao,ddist,dpairs,dtests⟩,sz,form⟩ := normalize C ⟨ao,fun g hg => (strict g hg).2,pairs,(corr C).mp tests⟩
  have dm : Monotone2 D := fun g hg => ⟨by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using dao.1 g hg, (dao.2.2 g hg).le⟩
  by_contra fail
  have separate : ∀ j < D.size, ∀ w : ℕ, (w<26+j ∨ w=26+D.size) →
      ¬req (fun x b => (D.wires x).getD (26+j) false=b → (D.wires x).getD w false=b) := by
    intro j hj w hw better
    obtain ⟨E,em,eb,lt,rel⟩ := erase 26 D j w dm dao.2.1 hj hw
    apply fail
    refine ⟨E,em,eb,(corr E).mpr ⟨?_,?_⟩,lt.trans_eq sz⟩
    · intro p l e
      exact rel _ true (by simp [bits]) (dtests.1 p l e) (better.1 p l e)
    · intro Q hQ
      exact rel _ false (by simp [bits]) (dtests.2 Q hQ) (better.2 Q hQ)
  have h := lower D ⟨dao,ddist,dpairs,dtests⟩ form separate
  omega
