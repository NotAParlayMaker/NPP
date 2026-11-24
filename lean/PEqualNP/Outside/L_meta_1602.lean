import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1602_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev wire {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false

lemma length_wires (gs : List Gate) (bs : List Bool) :
    ((Circuit.mk gs 0).wires bs).length = bs.length + gs.length := by
  induction gs generalizing bs with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (bs ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wire_append {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    wire (gs ++ [g]) x i = if i < n + gs.length then wire gs x i else
      if i = n + gs.length then g.op.eval (g.inputs.map (wire gs x)) else false := by
  have h : (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
      (Circuit.mk gs 0).wires (List.ofFn x) ++ [g.op.eval (g.inputs.map (wire gs x))] := by
    rw [Circuit.wires, List.foldl_append]
    rfl
  have hl : ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + gs.length := by
    simp [length_wires]
  change ((Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x)).getD i false = _
  rw [h]
  split_ifs with h₁ h₂
  · exact List.getD_append _ _ _ _ (hl ▸ h₁)
  · rw [← hl] at h₂
    simp [h₂]
  · rw [List.getD_eq_default]
    simp only [List.length_append, List.length_singleton, hl]
    omega

lemma empty_wire {n : ℕ} (x : Fin n → Bool) (j : ℕ) (h : j < n) :
    wire [] x j = x ⟨j,h⟩ := by
  simp [wire, Circuit.wires, h]

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (X Y : ℕ → Bool) (hXY : ∀ j, X j = true → Y j = true) :
    g.op.eval (g.inputs.map X) = true → g.op.eval (g.inputs.map Y) = true := by
  rcases hop with e | e
  · simp only [e,GateOp.eval,List.all_eq_true,id_eq,List.mem_map,forall_exists_index, and_imp]
    intro h b j hj hb
    rw [← hb]
    exact hXY _ (h _ _ hj rfl)
  · simp only [e,GateOp.eval,List.any_eq_true,id_eq,List.mem_map]
    rintro ⟨b,⟨j,hj,rfl⟩,h⟩
    exact ⟨Y j,⟨j,hj,rfl⟩, hXY j h⟩

lemma wire_mono {n : ℕ} (gs : List Gate)
    (hOp : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ i, wire gs x i = true → wire gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    by_cases h : i < n
    · rw [empty_wire x i h] at hi
      rw [empty_wire y i h]
      exact hxy _ hi
    · have hf : wire [] x i = false := by
        apply List.getD_eq_default
        simpa [Circuit.wires] using Nat.le_of_not_gt h
      rw [hf] at hi
      contradiction
  | append_singleton gs g ih =>
    intro i hi
    have hpre : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hOp g' (List.mem_append_left _ hg')
    rw [wire_append] at hi ⊢
    split_ifs at hi ⊢ with h₁ h₂
    · exact ih hpre _ hi
    · exact gate_mono g (hOp g (by simp)) (wire gs x) (wire gs y) (ih hpre) hi

abbrev PairTest {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].op = GateOp.and →
    ∀ a b, ¬ G.Adj a b → wire gs (pairInput a b) (n+j) = false

lemma witness {n : ℕ} (a₀ : Fin n) (G : SimpleGraph (Fin n)) (gs : List Gate)
    (hMono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hPair : PairTest G gs) (x : Fin n → Bool)
    (hx : ∀ a b, x a = true → x b = true → ¬ G.Adj a b) :
    ∀ i, wire gs x i = true → ∃ a, x a = true ∧ wire gs (pairInput a a) i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    by_cases h : i < n
    · rw [empty_wire x i h] at hi
      refine ⟨⟨i,h⟩,hi,?_⟩
      rw [empty_wire _ i h]
      simp [pairInput]
    · have hf : wire [] x i = false := by
        apply List.getD_eq_default
        simpa [Circuit.wires] using Nat.le_of_not_gt h
      rw [hf] at hi
      contradiction
  | append_singleton gs g ih =>
    have hpre : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun w hw => hMono w (List.mem_append_left _ hw)
    have hprePair : PairTest G gs := by
      intro j hj hAnd a b hab
      have hjs : j < (gs ++ [g]).length := by simp; omega
      have hv := hPair j hjs (by rwa [List.getElem_append_left hj]) a b hab
      rwa [wire_append, ite_eq_left (by omega)] at hv
    have single := ih hpre hprePair
    have hg := hMono g (by simp)
    intro i hi
    by_cases hbefore : i < n + gs.length
    · rw [wire_append, ite_eq_left hbefore] at hi
      obtain ⟨a,hxa,ha⟩ := single i hi
      exact ⟨a,hxa,by rwa [wire_append, ite_eq_left hbefore]⟩
    by_cases hit : i = n + gs.length
    · subst i
      rw [wire_append, ite_eq_right (by omega), ite_eq_left rfl] at hi
      rcases hg.1 with hAnd | hOr
      · exfalso
        have no (a b : Fin n) (hab : ¬ G.Adj a b) :
            g.op.eval (g.inputs.map (wire gs (pairInput a b))) = false := by
          have hbad := hPair gs.length (by simp)
            (by simpa only [List.getElem_concat_length] using hAnd) a b hab
          rwa [wire_append, ite_eq_right (by omega), ite_eq_left rfl] at hbad
        cases e : g.inputs with
        | nil =>
          have h := no a₀ a₀ G.irrefl
          simp [e,hAnd,GateOp.eval] at h
        | cons i rest =>
          cases rest with
          | nil =>
            have htrue : wire gs x i = true := by simpa [e,hAnd,GateOp.eval] using hi
            obtain ⟨a,_,ha⟩ := single i htrue
            have h := no a a G.irrefl
            simp only [e,hAnd,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
              id_eq,ha,Bool.and_true] at h
            exact Bool.noConfusion h
          | cons j rest =>
            cases rest with
            | nil =>
              simp only [e,hAnd,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,
                List.all_nil,Bool.and_true,id_eq,Bool.and_eq_true] at hi
              obtain ⟨a,hxa,ha⟩ := single i hi.1
              obtain ⟨b,hxb,hb⟩ := single j hi.2
              have hma : wire gs (pairInput a b) i = true :=
                wire_mono gs (fun w hw => (hpre w hw).1) _ _ (by
                  intro r hr
                  simp only [pairInput,or_self,decide_eq_true_eq] at hr
                  simp [pairInput,hr]) _ ha
              have hmb : wire gs (pairInput a b) j = true :=
                wire_mono gs (fun w hw => (hpre w hw).1) _ _ (by
                  intro r hr
                  simp only [pairInput,or_self,decide_eq_true_eq] at hr
                  simp [pairInput,hr]) _ hb
              have h := no a b (hx a b hxa hxb)
              simp only [e,hAnd,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
                id_eq,hma,hmb,Bool.and_true] at h
              exact Bool.noConfusion h
            | cons k rest =>
              have hh := hg.2
              simp [e] at hh
      · simp only [hOr,GateOp.eval,List.any_eq_true,id_eq,List.mem_map] at hi
        obtain ⟨_,⟨j,hj,rfl⟩,hjt⟩ := hi
        obtain ⟨a,hxa,hat⟩ := single j hjt
        refine ⟨a,hxa,?_⟩
        rw [wire_append, ite_eq_right (by omega), ite_eq_left rfl]
        simp only [hOr,GateOp.eval,List.any_eq_true,id_eq,List.mem_map]
        exact ⟨_,⟨j,hj,rfl⟩,hat⟩
    · rw [wire_append, ite_eq_right hbefore, ite_eq_right hit] at hi
      contradiction

lemma clean {n : ℕ} (a₀ : Fin n) (G : SimpleGraph (Fin n)) (D : Circuit)
    (hMono : Monotone2 D)
    (hPair : ∀ k : ℕ, k < D.gates.length → (gateAt D k).op = GateOp.and →
      ∀ e w : Fin n, ¬ G.Adj e w → gateVal n D k (pairInput e w) = false)
    (j : Fin D.gates.length) (x : Fin n → Bool) (hAnd : (D.gates.get j).op = GateOp.and)
    (hw : wire D.gates x (n + (j : ℕ)) = true) :
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  by_contra h
  have hx : ∀ u v, x u = true → x v = true → ¬ G.Adj u v :=
    fun u v hu hv huv => h ⟨u,v,huv,hu,hv⟩
  have hP : PairTest G D.gates := by
    intro k hk hka a b hab
    have ht : (gateAt D k).op = GateOp.and := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hk]
      exact hka
    exact hPair k hk ht a b hab
  have hm : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    simpa [Monotone2] using hMono
  obtain ⟨a,_,ha⟩ := witness a₀ G D.gates hm hP x hx _ hw
  have hb := hP j j.isLt hAnd a a G.irrefl
  rw [hb] at ha
  contradiction

lemma zero_bound (H : SimpleGraph (Fin 0)) [DecidableRel H.Adj] (D : Circuit) :
    ∃ S : Finset (Fin 0), (∀ y z, H.Adj y z → y ∈ S ∨ z ∈ S) ∧
      H.edgeFinset.card + S.card ≤ D.size + 1 := by
  have hEdge : H.edgeFinset = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p
    refine Sym2.inductionOn p ?_
    intro u _
    exact Fin.elim0 u
  refine ⟨∅, fun y => Fin.elim0 y, ?_⟩
  simp [hEdge]

end PEqualNP.Outside.L_meta_1602_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_1602 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro coverBound m H _ squareFree D mono correct pairClean
  by_cases hm : 0 < m
  · have shape : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      simpa only [Monotone2, Set.mem_insert_iff, Set.mem_singleton_iff] using mono
    have semantics (x : Fin m → Bool) :
        D.eval (List.ofFn x) = decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
      simpa [circuitFun, NestedCover.graphFun] using congrFun correct x
    exact coverBound m H squareFree D.gates D.output shape semantics
      (PEqualNP.Outside.L_meta_1602_aux.clean ⟨0,hm⟩ H D mono pairClean)
  · have hm0 : m = 0 := by omega
    subst m
    exact PEqualNP.Outside.L_meta_1602_aux.zero_bound H D
