import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover PEqualNP.LowMerge
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo Finset
open scoped Classical

-- A local witness is two sets of active variables. Simple point/line conditions
-- characterize exactly when these sets can be completed to a quadrangle test.
set_option maxHeartbeats 1400000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_5278_418
    (completion : ∀ P L : Finset (Fin 13),
      (∀ l, (P ∩ singerLines3 l).card≤2) → L⊆missLines singerLines3 P → L.card≤3 →
      (∀ p, (L.filter (fun l => p∈singerLines3 l)).card≤2) →
      ∃ Q∈quadrangles singerLines3, P⊆Q ∧ L⊆missLines singerLines3 Q)
    (witness :
      let S := singerLines3
      let W (P L : Finset (Fin 13)) := (List.ofFn fun i : Fin 13 => decide (i∈P)) ++ List.ofFn fun i : Fin 13 => decide (i∈L)
      ∀ (C : Circuit) (T : Finset ℕ),
      let g := gateAt C
      let v := wireVal C
      IsAO2 26 C → 38≤C.size → C.size<64 → 8≤nAnd C ∧ 18≤nOr C →
      (∀ a∈C.gates, a.inputs.getD 0 0≠a.inputs.getD 1 0) → 2≤andPairs 26 C →
      (∀ i<C.size, (g i).op=.and → ∀ j∈(g i).inputs, ∃ Q∈quadrangles S,
        v (W Q (missLines S Q)) (26+i)≠v (W Q (missLines S Q)) j) →
      (∀ i∈T, i<C.size ∧ (g i).op=.and) → 2*T.card≤C.size+1 →
      (∀ x : List Bool, x.length=26 → (C.eval x=true ↔ ∃ i∈T, v x (26+i)=true)) →
      (∀ p l, p∈S l → ∃ i∈T, v (pointLineInput 13 13 p l) (26+i)=true) →
      ∃ P L : Finset (Fin 13), (∀ l, (P ∩ S l).card≤2) ∧ L⊆missLines S P ∧ L.card≤3 ∧
        (∀ p, (L.filter (fun l => p∈S l)).card≤2) ∧ C.eval (W P L)=true) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;   have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 → (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) → (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) → (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) → (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) → (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) → False := by
  classical
  let word (P L : Finset (Fin 13)) :=
    (List.ofFn fun i : Fin 13 => decide (i∈P)) ++ List.ofFn fun i : Fin 13 => decide (i∈L)
  have word_mono {P L P' L' : Finset (Fin 13)} (p : P⊆P') (l : L⊆L') (i : ℕ) :
      (word P L).getD i false=true → (word P' L').getD i false=true := by
    have side {n : ℕ} (S T : Finset (Fin n)) (sub : S⊆T) (k : ℕ) :
        (List.ofFn fun j => decide (j∈S)).getD k false=true →
        (List.ofFn fun j => decide (j∈T)).getD k false=true := by
      by_cases hk : k<n
      · have val (U : Finset (Fin n)) :
            (List.ofFn fun j => decide (j∈U)).getD k false=decide ((⟨k,hk⟩ : Fin n)∈U) := by
          rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hk)]
          simp only [Option.getD_some,List.getElem_ofFn]
        rw [val,val];simp only [decide_eq_true_eq];exact fun h => sub h
      · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn];omega)]
        simp
    unfold word
    by_cases lt : i<13
    · rw [List.getD_append _ _ _ _ (by simpa using lt),List.getD_append _ _ _ _ (by simpa using lt)]
      exact side _ _ p _
    · rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      exact side _ _ l _

  have push_mono (gs : List Gate) (X Y : List Bool) (len : X.length=Y.length)
      (le : ∀ i, X.getD i false=true → Y.getD i false=true)
      (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or) :
      ∀ i, (Circuit.mk gs i).eval X=true → (Circuit.mk gs i).eval Y=true := by
    induction gs generalizing X Y with
    | nil => exact le
    | cons g gs ih =>
      let bit (Z : List Bool) := g.op.eval (g.inputs.map fun i => Z.getD i false)
      have lift : bit X=true → bit Y=true := by
        rcases ops g (by simp) with ha|ho
        · simp only [bit,ha]
          change (g.inputs.map (fun i => X.getD i false)).all id=true →
            (g.inputs.map (fun i => Y.getD i false)).all id=true
          simp only [List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
          intro h b i hi eq; subst b
          exact le _ (h _ _ hi rfl)
        · intro h
          dsimp only [bit] at h
          rw [ho] at h
          obtain ⟨_,hm,on⟩ := List.any_eq_true.mp h
          obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
          change g.op.eval _=true
          rw [ho]; apply List.any_eq_true.mpr
          exact ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,le _ on⟩
      have inc : ∀ i, (X++[bit X]).getD i false=true → (Y++[bit Y]).getD i false=true := by
        intro i; by_cases small : i<X.length
        · rw [List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)];exact le i
        · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),← len]
          cases i-X.length with
          | zero => exact lift
          | succ j => simp [List.getD_eq_getElem?_getD]
      exact ih _ _ (by simp [len]) inc (fun a ha => ops a (by simp [ha]))
  intro quadword quadfamily C T gate wire shape lo hi counts diff pairs essential terminals few output accepts
  obtain ⟨P,L,arc,free,bound,dual,on⟩ := witness C T shape lo hi counts diff pairs essential
    (fun i h => ⟨(terminals i h).1,(terminals i h).2.1⟩) few output accepts
  obtain ⟨Q,hQ,ps,ls⟩ := completion P L arc free bound dual
  have fires : C.eval (word Q (missLines singerLines3 Q))=true :=
    push_mono C.gates (word P L) (word Q (missLines singerLines3 Q))
      (by simp [word]) (word_mono ps ls) shape.1 C.output on
  obtain ⟨j,hj,one⟩ := (output (word Q (missLines singerLines3 Q)) (by simp [word])).mp fires
  exact Bool.noConfusion (one.symm.trans ((terminals j hj).2.2 Q hQ))
