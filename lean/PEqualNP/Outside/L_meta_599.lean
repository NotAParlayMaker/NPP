import Mathlib
import PEqualNP.Defs

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def evalGate (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def runPrefix {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) : List Bool :=
  (C.gates.take j).foldl (fun w g => w ++ [evalGate g w]) (List.ofFn x)

def readAt {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (runPrefix C j x).getD i false

def wireAt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  readAt C C.gates.length x i

theorem circuit_eval_eq {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = wireAt C x C.output := by
  simp [wireAt, readAt, runPrefix, Circuit.eval, Circuit.wires, evalGate]

theorem runPrefix_succ {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (g : Gate)
    (hg : C.gates[j]? = some g) :
    runPrefix C (j+1) x = runPrefix C j x ++ [evalGate g (runPrefix C j x)] := by
  obtain ⟨hj,he⟩ := List.getElem?_eq_some_iff.mp hg
  simp [runPrefix,List.take_succ_eq_append_getElem hj,List.foldl_append,he]

private theorem runTail (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, gs.foldl (fun acc g => acc ++ [evalGate g acc]) w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (w ++ [evalGate g w])
    exact ⟨evalGate g w::t,by simpa [List.foldl_cons,List.append_assoc] using ht,by simp [hl]⟩

theorem runPrefix_length {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    (runPrefix C j x).length = n + min j C.gates.length := by
  obtain ⟨t,ht,hl⟩ := runTail (C.gates.take j) (List.ofFn x)
  simp [runPrefix,ht,hl]

theorem readAt_new {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (g : Gate)
    (hg : C.gates[j]? = some g) :
    readAt C (j+1) x (n+j) = g.op.eval (g.inputs.map (readAt C j x)) := by
  obtain ⟨hj,-⟩ := List.getElem?_eq_some_iff.mp hg
  have hlen := runPrefix_length C j x
  rw [Nat.min_eq_left (by omega)] at hlen
  unfold readAt
  rw [runPrefix_succ C j x g hg,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega), hlen]
  simp [evalGate]

theorem readAt_old {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (g : Gate)
    (hg : C.gates[j]? = some g) (i : ℕ) (hi : i < n+j) :
    readAt C (j+1) x i = readAt C j x i := by
  obtain ⟨hj,-⟩ := List.getElem?_eq_some_iff.mp hg
  unfold readAt
  rw [runPrefix_succ C j x g hg,List.getD_append]
  simpa [runPrefix_length,Nat.min_eq_left (Nat.le_of_lt hj)] using hi

theorem readAt_input {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (i : Fin n) :
    readAt C j x i.val = x i := by
  obtain ⟨t,ht,-⟩ := runTail (C.gates.take j) (List.ofFn x)
  unfold readAt runPrefix
  rw [ht,List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

def restrictInputs {n : ℕ} (r : Option (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  match r with
  | none => x
  | some i => Function.update x i false

def repValue {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (v : Bool ⊕ ℕ) : Bool :=
  match v with
  | .inl b => b
  | .inr i => readAt C j x i

def AliasAt {n : ℕ} (C : Circuit) (r : Option (Fin n)) (j : ℕ) (v : Bool ⊕ ℕ) : Prop :=
  ∀ x : Fin n → Bool, readAt C (j+1) (restrictInputs r x) (n+j) = repValue C j (restrictInputs r x) v

private def renameRead {n : ℕ} (r : Option (Fin n)) (bad : ℕ) (i : ℕ) : ℕ :=
  if r.map Fin.val = some i then bad else i

private theorem alignedRead {n : ℕ} (r : Option (Fin n)) (x : Fin n → Bool)
    (aux : List Bool) (bad : ℕ) (hbad : n+aux.length ≤ bad) (i : ℕ) :
    (List.ofFn x ++ aux).getD (renameRead r bad i) false =
      (List.ofFn (restrictInputs r x) ++ aux).getD i false := by
  cases r with
  | none => simp [restrictInputs,renameRead]
  | some k =>
    by_cases eq : k.val=i
    · subst i
      rw [show renameRead (some k) bad k.val = bad by simp [renameRead],List.getD_eq_default _ _ (by simpa using hbad),
        List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD,restrictInputs]
    · have identity : renameRead (some k) bad i = i := by simp [renameRead,eq]
      rw [identity]
      by_cases hi : i<n
      · let z : Fin n := ⟨i,hi⟩
        have hz : z≠k := by intro h; exact eq (congrArg Fin.val h).symm
        rw [List.getD_append _ _ _ _ (by simpa using hi),List.getD_append _ _ _ _ (by simpa using hi)]
        simp [List.getD_eq_getElem?_getD,hi,restrictInputs,Function.update_of_ne hz,z] at *
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi),
          List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi)]
        simp

private def changed (rename : ℕ → ℕ) (bad : ℕ) (v : Bool ⊕ ℕ) : Gate :=
  match v with
  | .inl true => ⟨.and,[]⟩
  | .inl false => ⟨.and,[bad]⟩
  | .inr i => ⟨.and,[rename i]⟩

private theorem changed_or (ren : ℕ → ℕ) (bad : ℕ) (v : Bool ⊕ ℕ) :
    (changed ren bad v).op = .and ∧ (changed ren bad v).inputs.length ≤ 2 := by
  rcases v with b | k
  · cases b <;> simp [changed]
  · simp [changed]

theorem rewrite_paid {n : ℕ} (C : Circuit) (r : Option (Fin n)) (A P : Finset ℕ)
    (hm : Monotone2 C)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = .or → j ∈ A)
    (hrep : ∀ j ∈ P, ∃ v : Bool ⊕ ℕ, AliasAt C r j v) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (restrictInputs r x))) ∧
      ∀ j g, D.gates[j]? = some g → g.op = .or → j ∈ A \ P := by
  classical
  let bad := n+C.gates.length
  let ren := renameRead r bad
  let representative (j : ℕ) : Bool ⊕ ℕ := if hj : j∈P then (hrep j hj).choose else .inl false
  have halias (j : ℕ) (hj : j∈P) : AliasAt C r j (representative j) := by
    simpa [representative,hj] using (hrep j hj).choose_spec
  let changeGate (j : ℕ) (g : Gate) : Gate :=
    if j∈P then changed ren bad (representative j) else ⟨g.op,g.inputs.map ren⟩
  let D : Circuit := ⟨C.gates.mapIdx changeGate, ren C.output⟩
  have lengthD : D.gates.length=C.gates.length := by simp [D]
  have obtainOld (j : ℕ) (g : Gate) (h : D.gates[j]?=some g) :
      ∃ old, C.gates[j]?=some old ∧ g=changeGate j old := by
    cases hh : C.gates[j]? with
    | none => simp [D,List.getElem?_mapIdx,hh] at h
    | some old => exact ⟨old,rfl,(by simpa [D,List.getElem?_mapIdx,hh] using h.symm)⟩
  refine ⟨D,?_,?_,?_⟩
  · intro g hg
    obtain ⟨j,hj⟩ := List.getElem?_of_mem hg
    obtain ⟨old,hold,rfl⟩ := obtainOld j g hj
    by_cases h : j∈P
    · obtain ⟨ho,hl⟩ := changed_or ren bad (representative j)
      simp [changeGate,h,ho,hl]
    · obtain ⟨ho,hl⟩ := hm old (List.mem_of_getElem? hold)
      simpa [changeGate,h] using And.intro ho hl
  · intro x
    let y := restrictInputs r x
    have alignedPrefix (j : ℕ) (hj : j ≤ C.gates.length) : ∃ u : List Bool, u.length=j ∧
        runPrefix D j x = List.ofFn x ++ u ∧ runPrefix C j y = List.ofFn y ++ u := by
      induction j with
      | zero => exact ⟨[],rfl,by simp [runPrefix],by simp [runPrefix]⟩
      | succ j ih =>
        obtain ⟨u,hu,hd,hc⟩ := ih (by omega)
        let old := C.gates[j]'(by omega)
        have hold : C.gates[j]?=some old := List.getElem?_eq_getElem (by omega)
        have hnew : D.gates[j]?=some (changeGate j old) := by simp [D,List.getElem?_mapIdx,hold]
        have hbad : n+u.length ≤ bad := by dsimp [bad]; omega
        have align (i : ℕ) : readAt D j x (ren i) = readAt C j y i := by
          unfold readAt
          rw [hd,hc]
          exact alignedRead r x u bad hbad i
        have badVal : readAt D j x bad = false := by
          unfold readAt
          rw [hd,List.getD_eq_default _ _ (by simpa using hbad)]
        have eq : evalGate (changeGate j old) (runPrefix D j x) = evalGate old (runPrefix C j y) := by
          by_cases pay : j∈P
          · have h := halias j pay x
            change readAt C (j+1) y (n+j) = repValue C j y (representative j) at h
            rw [readAt_new C j y old hold] at h
            change _ = old.op.eval (old.inputs.map (readAt C j y))
            rw [h]
            rcases ha : representative j with b | i
            · cases b
              · change _ = false
                simpa [evalGate,changeGate,pay,ha,changed,GateOp.eval,readAt] using badVal
              · simp [evalGate,changeGate,pay,ha,changed,GateOp.eval,repValue]
            · change _ = readAt C j y i
              simpa [evalGate,changeGate,pay,ha,changed,GateOp.eval,readAt] using align i
          · simp only [changeGate,pay,ite_false,evalGate,List.map_map]
            congr 1
            exact List.map_congr_left (fun i _ => align i)
        refine ⟨u ++ [evalGate old (runPrefix C j y)],by simp [hu],?_,?_⟩
        · rw [runPrefix_succ D j x _ hnew,eq,hd,List.append_assoc]
        · rw [runPrefix_succ C j y _ hold]
          rw [hc,List.append_assoc]
    obtain ⟨u,hu,hd,hc⟩ := alignedPrefix C.gates.length (le_refl _)
    rw [circuit_eval_eq,circuit_eval_eq]
    unfold wireAt readAt
    rw [lengthD,hd,hc]
    exact alignedRead r x u bad (by dsimp [bad]; omega) C.output
  · intro j g hj hor
    obtain ⟨old,hold,rfl⟩ := obtainOld j g hj
    by_cases pay : j∈P
    · have ho := (changed_or ren bad (representative j)).1
      simp [changeGate,pay,ho] at hor
    · exact Finset.mem_sdiff.mpr ⟨hA j old hold (by simpa [changeGate,pay] using hor),pay⟩

theorem alias_of_zero_operand {n : ℕ} (C : Circuit) (r : Option (Fin n)) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (ho : g.op = .or) (arity : g.inputs.length ≤ 2)
    (zero : ∃ i ∈ g.inputs, ∀ x : Fin n → Bool, readAt C j (restrictInputs r x) i = false) :
    ∃ v : Bool ⊕ ℕ, AliasAt C r j v := by
  obtain ⟨i,hin,hh⟩ := zero
  cases hs : g.inputs with
  | nil => simp [hs] at hin
  | cons a as =>
    cases ht : as with
    | nil =>
      refine ⟨.inr a,?_⟩
      intro x
      rw [readAt_new C j _ g hg]
      simp [repValue,hs,ht,ho,GateOp.eval]
    | cons b bs =>
      have hn : bs=[] := by simpa [hs,ht] using arity
      rw [hn] at ht
      rw [hs,ht] at hin
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
      rcases hin with rfl | rfl
      · refine ⟨.inr b,?_⟩
        intro x
        rw [readAt_new C j _ g hg]
        simp [repValue,hs,ht,ho,GateOp.eval,hh]
      · refine ⟨.inr a,?_⟩
        intro x
        rw [readAt_new C j _ g hg]
        simp [repValue,hs,ht,ho,GateOp.eval,hh]

theorem restrict_paid {n : ℕ} (C : Circuit) (r : Fin n) (A P : Finset ℕ)
    (hm : Monotone2 C)
    (hA : ∀ j g, C.gates[j]? = some g → g.op = .or → j ∈ A)
    (hp : ∀ j ∈ P, ∃ g, C.gates[j]? = some g ∧ g.op = .or ∧
      ∃ i ∈ g.inputs, ∀ x : Fin n → Bool, readAt C j (Function.update x r false) i = false) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x r false))) ∧
      ∀ j g, D.gates[j]? = some g → g.op = .or → j ∈ A \ P := by
  apply rewrite_paid C (some r) A P hm hA
  intro j hj
  obtain ⟨g,hg,ho,hz⟩ := hp j hj
  exact alias_of_zero_operand C (some r) j g hg ho (hm g (List.mem_of_getElem? hg)).2 hz

end M599

namespace M599Graph

noncomputable abbrev deg {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) := (G.neighborSet v).ncard

abbrev Sparse {n : ℕ} (G : SimpleGraph (Fin n)) :=
  ∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card

abbrev NoFour {n : ℕ} (G : SimpleGraph (Fin n)) :=
  ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4

theorem no_twins {n : ℕ} {G : SimpleGraph (Fin n)} (h : NoFour G) {u v : Fin n}
    (huv : u ≠ v) (hu : deg G u = 2) : G.neighborSet u ≠ G.neighborSet v := by
  classical
  intro eq
  obtain ⟨a,b,hab,hs⟩ := Set.ncard_eq_two.mp hu
  have hua : G.Adj u a := show a ∈ G.neighborSet u from hs ▸ (by simp)
  have hub : G.Adj u b := show b ∈ G.neighborSet u from hs ▸ (by simp)
  have hva : G.Adj v a := show a ∈ G.neighborSet v from eq ▸ hua
  have hvb : G.Adj v b := show b ∈ G.neighborSet v from eq ▸ hub
  let c : G.Walk u u := .cons hua (.cons hva.symm (.cons hvb (.cons hub.symm .nil)))
  have hc : c.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · rw [SimpleGraph.Walk.isPath_def]
      change [a,v,b,u].Nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, not_or]
      exact ⟨⟨hva.ne.symm,hab,hua.ne.symm⟩,⟨hvb.ne,huv.symm⟩,hub.ne.symm,not_false⟩
    · change 3 ≤ 4
      decide
  exact h u c hc rfl

theorem regular_of_no_leaf {n : ℕ} {G : SimpleGraph (Fin n)} (hs : Sparse G)
    (hl : ¬∃ v, deg G v = 1) : ∀ v, deg G v = 0 ∨ deg G v = 2 := by
  classical
  let F := G.support.toFinset
  have full : {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ F} = G.edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      exact he.1
    intro e he
    refine ⟨he,?_⟩
    intro v hv
    have hm := G.edgeSet_subset_sym2_iff.mpr (show G.support ⊆ G.support from le_rfl) he
    change v ∈ G.support.toFinset
    exact Set.mem_toFinset.mpr (Set.mem_sym2_iff_subset.mp hm hv)
  have count := hs F
  rw [full] at count
  have sparse_sum : (∑ v, G.degree v) ≤ 2*F.card := by
    rw [G.sum_degrees_eq_twice_card_edges]
    have eq : G.edgeFinset.card = G.edgeSet.ncard := by
      rw [G.edgeFinset_card,Set.fintypeCard_eq_ncard]
    omega
  have lower (v : Fin n) (hv : v∈F) : 2 ≤ G.degree v := by
    have pos := (G.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv)
    have ne : G.degree v ≠ 1 := fun eq => hl ⟨v,(G.ncard_neighborSet v).trans eq⟩
    omega
  have sumSupport : (∑ v ∈ F, G.degree v) = ∑ v, G.degree v :=
    Finset.sum_subset (Finset.subset_univ _) fun v _ hv => by
      have notIn : v ∉ G.support := fun x => hv (Set.mem_toFinset.mpr x)
      exact (G.degree_eq_zero_iff_notMem_support v).mpr notIn
  intro v
  simp only [deg,G.ncard_neighborSet]
  by_cases hv : v∈F
  · right
    by_contra ne
    have strict : (∑ _ ∈ F, 2) < ∑ w ∈ F, G.degree w :=
      Finset.sum_lt_sum lower ⟨v,hv,by have := lower v hv; omega⟩
    simp only [Finset.sum_const, smul_eq_mul] at strict
    rw [sumSupport] at strict
    omega
  · left
    have notIn : v ∉ G.support := fun x => hv (Set.mem_toFinset.mpr x)
    exact (G.degree_eq_zero_iff_notMem_support v).mpr notIn

theorem delete_count {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (G.deleteIncidenceSet v).edgeSet.ncard + deg G v = G.edgeSet.ncard := by
  classical
  rw [G.edgeSet_deleteIncidenceSet,deg,G.ncard_neighborSet,←G.ncard_incidenceSet]
  exact Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v)

theorem sparse_mono {n : ℕ} {G H : SimpleGraph (Fin n)} (h : H ≤ G) (hs : Sparse G) :
    Sparse H := by
  intro S
  apply le_trans _ (hs S)
  exact Set.ncard_le_ncard (fun _ p => ⟨(SimpleGraph.edgeSet_mono h) p.1,p.2⟩)

theorem noFour_mono {n : ℕ} {G H : SimpleGraph (Fin n)} (h : H ≤ G) (hn : NoFour G) :
    NoFour H := by
  intro v c hc
  simpa using hn v (c.mapLe h) (hc.mapLe h)

theorem induct_cost {n : ℕ} (Pay : SimpleGraph (Fin n) → ℕ → Prop)
    (leaf : ∀ (G : SimpleGraph (Fin n)) (a : ℕ), Pay G a → 2 ≤ G.edgeSet.ncard →
      (∃ v, deg G v = 1) →
      ∃ v b, deg G v = 1 ∧ Pay (G.deleteIncidenceSet v) b ∧ b+1 ≤ a)
    (ring : ∀ (G : SimpleGraph (Fin n)) (a : ℕ), Pay G a → 2 ≤ G.edgeSet.ncard →
      (∀ v, deg G v = 0 ∨ deg G v = 2) →
      (∀ u v, u ≠ v → deg G u = 2 → G.neighborSet u ≠ G.neighborSet v) →
      ∃ v b, deg G v = 2 ∧ Pay (G.deleteIncidenceSet v) b ∧ b+2 ≤ a)
    (G : SimpleGraph (Fin n)) (a : ℕ) (hs : Sparse G) (hn : NoFour G) (ha : Pay G a) :
    G.edgeSet.ncard ≤ a+1 := by
  induction hk : G.edgeSet.ncard using Nat.strong_induction_on generalizing G a with
  | ind k ih =>
    by_cases small : k ≤ 1
    · omega
    have ge : 2 ≤ G.edgeSet.ncard := by omega
    have recur (v : Fin n) (b d : ℕ) (hd : deg G v = d) (pos : 0 < d)
        (hp : Pay (G.deleteIncidenceSet v) b) (cut : b+d ≤ a) : k ≤ a+1 := by
      have ec := delete_count G v
      have lt : (G.deleteIncidenceSet v).edgeSet.ncard < k := by omega
      have sub := G.deleteIncidenceSet_le v
      have bound := ih _ lt (G.deleteIncidenceSet v) b (sparse_mono sub hs) (noFour_mono sub hn) hp rfl
      omega
    by_cases one : ∃ v, deg G v = 1
    · obtain ⟨v,b,hd,hp,cut⟩ := leaf G a ha ge one
      exact recur v b 1 hd (by decide) hp cut
    · obtain ⟨v,b,hd,hp,cut⟩ := ring G a ha ge (regular_of_no_leaf hs one) (fun _ _ ne d => no_twins hn ne d)
      exact recur v b 2 hd (by decide) hp cut

end M599Graph

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def RawTerm {n : ℕ} (w : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, w x = false) ∨ ∃ S : Finset (Fin n), ∀ x, w x = true ↔ ∀ i ∈ S, x i = true

private theorem raw_and {n : ℕ} {a b : (Fin n → Bool) → Bool}
    (ha : RawTerm a) (hb : RawTerm b) : RawTerm (fun x => a x && b x) := by
  rcases ha with h | ⟨S,hS⟩
  · exact Or.inl fun x => by simp [h x]
  rcases hb with h | ⟨T,hT⟩
  · exact Or.inl fun x => by simp [h x]
  right
  refine ⟨S ∪ T, fun x => ?_⟩
  simp only [Bool.and_eq_true,hS,hT,Finset.mem_union]
  exact ⟨fun ⟨hs,ht⟩ i hi => hi.elim (hs i) (ht i),
    fun h => ⟨fun i hi => h i (Or.inl hi),fun i hi => h i (Or.inr hi)⟩⟩

private theorem raw_all {n : ℕ} (ws : ℕ → (Fin n → Bool) → Bool)
    (raw : ∀ i, RawTerm (ws i)) (args : List ℕ) :
    RawTerm (fun x => (args.map (fun i => ws i x)).all id) := by
  induction args with
  | nil => exact Or.inr ⟨∅, by simp⟩
  | cons a l ih => exact raw_and (raw a) ih

private def rawStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem rawLength (l : List Gate) (v : List Bool) :
    (l.foldl rawStep v).length = v.length+l.length := by
  induction l generalizing v with
  | nil => simp
  | cons g l ih => simp [List.foldl_cons, ih,rawStep]; omega

theorem raw_before {n : ℕ} (l : List Gate) (h : ∀ g ∈ l, g.op = .and) (i : ℕ) :
    RawTerm (fun x : Fin n → Bool => (l.foldl rawStep (List.ofFn x)).getD i false) := by
  induction l using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < n
    · right
      exact ⟨{⟨i,hi⟩},fun x => by simp [hi]⟩
    · left
      exact fun x => List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)
  | append_singleton l g ih =>
    have pre : ∀ a ∈ l, a.op = .and := fun a ha => h a (by simp [ha])
    have hg : g.op = .and := h g (by simp)
    by_cases hi : i=n+l.length
    · subst i
      have newRead (x : Fin n → Bool) :
          ((l ++ [g]).foldl rawStep (List.ofFn x)).getD (n+l.length) false =
          (g.inputs.map (fun j => (l.foldl rawStep (List.ofFn x)).getD j false)).all id := by
        have len := rawLength l (List.ofFn x)
        simp only [List.length_ofFn] at len
        simp [List.foldl_append,rawStep,hg,GateOp.eval,← len]
      simp_rw [newRead]
      exact raw_all _ (fun j => ih pre j) _
    · have oldRead (x : Fin n → Bool) :
          ((l ++ [g]).foldl rawStep (List.ofFn x)).getD i false =
          (l.foldl rawStep (List.ofFn x)).getD i false := by
        have len := rawLength l (List.ofFn x)
        simp only [List.length_ofFn] at len
        simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,rawStep]
        by_cases lt : i < (l.foldl rawStep (List.ofFn x)).length
        · exact List.getD_append _ _ _ _ lt
        · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
      simp_rw [oldRead]
      exact ih pre i

end M599

namespace M599

def EdgeOn {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true

def bits {n : ℕ} (V : Finset (Fin n)) (i : Fin n) := decide (i ∈ V)

theorem edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (p q : Fin n) :
    EdgeOn G (bits {p,q}) ↔ G.Adj p q := by
  simp only [EdgeOn,bits,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨i,j,e,hi,hj⟩
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (e.ne rfl).elim
    · exact e
    · exact e.symm
    · exact (e.ne rfl).elim
  · exact fun e => ⟨p,q,e,Or.inl rfl,Or.inr rfl⟩

theorem no_edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    ¬ EdgeOn G (bits {p}) := by
  simpa using (edge_pair G p p).not.mpr (G.loopless.irrefl p)

def InArm {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) := ∀ i ∈ S, x i = true

def SplitArm {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :=
  InArm S x ∨ InArm T x

def MonomialFactors {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) : Prop :=
  ∀ (D : Finset (Fin n)), D ⊆ S ∪ T → ∀ x y : Fin n → Bool,
    (∀ i ∉ D, x i=y i) → (SplitArm S T x ↔ SplitArm S T y) →
    (EdgeOn G x ↔ EdgeOn G y)

theorem overlap_impossible {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n))
    (noniso : ∀ d ∈ S ∪ T, ∃ w, G.Adj d w)
    (both : ∀ d ∈ S, d ∈ T → ∀ x y : Fin n → Bool,
      (∀ i, i ≠ d → x i=y i) → (EdgeOn G x ↔ EdgeOn G y)) :
    Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro d hs ht
  obtain ⟨w,e⟩ := noniso d (Finset.mem_union_left _ hs)
  have eq := both d hs ht (bits {w}) (bits {d,w}) (fun i hi => by simp [bits,hi])
  exact no_edge_single G w (eq.mpr ((edge_pair G d w).mpr e))

theorem arm_unique {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n))
    (dis : Disjoint S T)
    (other : ∀ d ∈ S, ∀ z : Fin n, ∃ w, G.Adj d w ∧ w ≠ z)
    (fact : MonomialFactors G S T) :
    ∀ d ∈ S, ∀ z ∈ S, d=z := by
  intro d hd z hz
  by_contra ne
  obtain ⟨w,e,hw⟩ := other d hd z
  have sub : ({d} : Finset _) ⊆ S ∪ T := Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ hd)
  have same : ∀ i ∉ ({d} : Finset _), bits {w} i = bits {d,w} i := by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [bits,hi]
  have lf : ¬InArm S (bits {w}) := fun bad => by simpa [bits,hw.symm] using bad z hz
  have rf : ¬InArm S (bits {d,w}) := fun bad => by simpa [bits,hw.symm,Ne.symm ne] using bad z hz
  have eqT : InArm T (bits {w}) ↔ InArm T (bits {d,w}) := by
    have val (i) (hi : i ∈ T) : bits {w} i = bits {d,w} i := by
      apply same
      rintro p
      have eq := Finset.mem_singleton.mp p
      subst i
      exact Finset.disjoint_left.mp dis hd hi
    exact ⟨fun h i hi => (val i hi).symm.trans (h i hi),fun h i hi => (val i hi).trans (h i hi)⟩
  have eq := fact {d} sub _ _ same (by simpa [SplitArm,lf,rf] using eqT)
  exact no_edge_single G w (eq.mpr ((edge_pair G d w).mpr e))

theorem factors_swap {n : ℕ} {G : SimpleGraph (Fin n)} {S T : Finset (Fin n)}
    (f : MonomialFactors G S T) : MonomialFactors G T S := by
  intro D sub x y outside arms
  exact f D (by simpa only [Finset.union_comm] using sub) x y outside
    (by simpa only [SplitArm,or_comm] using arms)

theorem singleton_twins {n : ℕ} (G : SimpleGraph (Fin n)) (p q : Fin n)
    (fact : MonomialFactors G {p} {q}) : G.neighborSet p = G.neighborSet q := by
  have sub : ({p,q} : Finset _) ⊆ {p} ∪ {q} := by simp
  have noedge : ¬G.Adj p q := by
    intro e
    have eq := fact {p,q} sub (bits {p}) (bits {p,q}) (by
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      simp [bits,hi]) (by simp [SplitArm,InArm,bits])
    exact no_edge_single G p (eq.mpr ((edge_pair G p q).mpr e))
  ext w
  change G.Adj p w ↔ G.Adj q w
  by_cases wp : w=p
  · subst w
    simp [noedge, G.adj_comm]
  by_cases wq : w=q
  · subst w
    simp [noedge]
  have eq := fact {p,q} sub (bits {p,w}) (bits {q,w}) (by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    simp [bits,hi]) (by simp [SplitArm,InArm,bits])
  exact (edge_pair G p w).symm.trans (eq.trans (edge_pair G q w))

end M599

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Begin front invariant.

theorem front_eq {n : ℕ} (C : Circuit) (hm : Monotone2 C) (D : Finset (Fin n))
    (u v : Fin n → Bool) (j : ℕ) (outside : ∀ d ∉ D, u d = v d)
    (special : ∀ g : Gate, C.gates[j]? = some g →
      g.op.eval (g.inputs.map (readAt C j u)) = g.op.eval (g.inputs.map (readAt C j v)) ∨
        ∃ d ∈ D, ∀ x : Fin n → Bool, x d = false → g.op.eval (g.inputs.map (readAt C j x)) = false)
    (uncharged : ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g → g.op = .or → i ≠ j →
      ∀ w ∈ g.inputs, ∀ d ∈ D, ¬ (∀ x : Fin n → Bool, x d = false → readAt C i x w = false))
    (output : ∀ d ∈ D, ∃ x : Fin n → Bool, x d = false ∧ C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn u) = C.eval (List.ofFn v) := by
  classical
  have inv : ∀ k ≤ C.gates.length, ∀ w : ℕ,
      readAt C k u w = readAt C k v w ∨
        ∃ d ∈ D, ∀ x : Fin n → Bool, x d = false → readAt C k x w = false := by
    intro k hk
    induction k with
    | zero =>
      intro w
      by_cases hw : w < n
      · let p : Fin n := ⟨w, hw⟩
        have input (x : Fin n → Bool) : readAt C 0 x w = x p := by
          simp [readAt, runPrefix, p, hw]
        by_cases hp : p ∈ D
        · exact Or.inr ⟨p, hp, fun x hx => (input x).trans hx⟩
        · exact Or.inl ((input u).trans ((outside p hp).trans (input v).symm))
      · left
        simp [readAt, runPrefix, hw]
    | succ k ih =>
      have hk' : k < C.gates.length := hk
      let g := C.gates[k]
      have hg : C.gates[k]? = some g := List.getElem?_eq_getElem hk'
      have prev := ih (Nat.le_of_lt hk')
      intro w
      rcases Nat.lt_trichotomy w (n+k) with h | rfl | h
      · simpa only [readAt_old C k _ g hg w h] using prev w
      · simp only [readAt_new C k _ g hg]
        by_cases hkj : k = j
        · subst j; exact special g hg
        · obtain hgm | hgm := (hm g (List.getElem_mem hk')).1
          · by_cases different : ∃ i ∈ g.inputs, readAt C k u i ≠ readAt C k v i
            · obtain ⟨i, hi, hd⟩ := different
              obtain ⟨d, hD, low⟩ := (prev i).resolve_left hd
              right
              refine ⟨d, hD, fun x hx => ?_⟩
              rw [hgm, GateOp.eval, List.all_map]
              by_contra! hyp
              have z := List.all_eq_true.mp (Bool.eq_true_of_not_eq_false hyp) i hi
              simp [low x hx] at z
            · left
              congr 1
              apply List.map_congr_left
              intro i hi
              exact not_ne_iff.mp (fun h => different ⟨i,hi,h⟩)
          · left
            congr 1
            apply List.map_congr_left
            intro i hi
            rcases prev i with h | ⟨d, hd, low⟩
            · exact h
            · exact False.elim (uncharged k g hg hgm hkj i hi d hd low)
      · left
        have far (x : Fin n → Bool) : readAt C (k+1) x w = false := by
          apply List.getD_eq_default
          rw [runPrefix_length, Nat.min_eq_left hk]
          omega
        rw [far u, far v]
  have rend (x : Fin n → Bool) : readAt C C.gates.length x C.output = C.eval (List.ofFn x) := by
    simp [readAt, runPrefix, Circuit.eval, Circuit.wires, evalGate]
  rcases inv C.gates.length le_rfl C.output with h | ⟨d, hd, h⟩
  · simpa only [rend] using h
  · obtain ⟨x, hx, ho⟩ := output d hd
    have hf := h x hx
    rw [rend x, ho] at hf
    contradiction

theorem front_eq_of_low {n : ℕ} (C : Circuit) (hm : Monotone2 C) (d : Fin n)
    (u v : Fin n → Bool) (j : ℕ) (outside : ∀ p ≠ d, u p = v p)
    (special : ∀ g : Gate, C.gates[j]? = some g → ∀ x : Fin n → Bool,
      x d = false → g.op.eval (g.inputs.map (readAt C j x)) = false)
    (uncharged : ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g → g.op = .or → i ≠ j →
      ∀ w ∈ g.inputs, ¬ (∀ x : Fin n → Bool, x d = false → readAt C i x w = false))
    (output : ∃ x : Fin n → Bool, x d = false ∧ C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn u) = C.eval (List.ofFn v) := by
  classical
  apply front_eq C hm {d} u v j
  · simpa using outside
  · intro g hg
    exact Or.inr ⟨d, Finset.mem_singleton_self d, special g hg⟩
  · intro i g hg ho hij w hw e he
    have := Finset.mem_singleton.mp he
    subst e
    exact uncharged i g hg ho hij w hw
  · simpa using output




end M599

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity M599Graph

abbrev Computes {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ EdgeOn G x

abbrev Counts (C : Circuit) (A : Finset ℕ) :=
  ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .or → j ∈ A

def Pay {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) : Prop :=
  ∃ (C : Circuit) (A : Finset ℕ), Monotone2 C ∧ Computes G C ∧ Counts C A ∧ A.card ≤ a

def Charged {n : ℕ} (C : Circuit) (v : Fin n) (j : ℕ) : Prop :=
  ∃ g, C.gates[j]? = some g ∧ g.op = .or ∧
    ∃ w ∈ g.inputs, ∀ x : Fin n → Bool, x v = false → readAt C j x w = false

theorem neighbor2 {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (h : deg G v = 2) (z : Fin n) :
    ∃ w, G.Adj v w ∧ w ≠ z := by
  obtain ⟨a,b,hab,hs⟩ := Set.ncard_eq_two.mp h
  by_cases az : a=z
  · exact ⟨b,show b ∈ G.neighborSet v from hs ▸ (by simp),by grind⟩
  · exact ⟨a,show a ∈ G.neighborSet v from hs ▸ (by simp),az⟩

theorem edge_of_count {n : ℕ} (G : SimpleGraph (Fin n)) (he : 0 < G.edgeSet.ncard) :
    ∃ p q, G.Adj p q := by
  obtain ⟨e,edge⟩ := (Set.ncard_pos (Set.toFinite G.edgeSet)).mp he
  induction e using Sym2.inductionOn with
  | _ p q => exact ⟨p,q,edge⟩

theorem avoid {n : ℕ} (G : SimpleGraph (Fin n)) (ge : 2 ≤ G.edgeSet.ncard)
    (reg : ∀ v, deg G v = 0 ∨ deg G v = 2) (d : Fin n) :
    ∃ p q, G.Adj p q ∧ p ≠ d ∧ q ≠ d := by
  classical
  rcases reg d with iso | two
  · obtain ⟨p,q,e⟩ := edge_of_count G (by omega)
    have no (z : Fin n) (h : G.Adj d z) : False := by
      have pos := h.degree_pos_left
      rw [deg,G.ncard_neighborSet] at iso
      omega
    exact ⟨p,q,e,fun h => no _ (h ▸ e),fun h => no _ (h ▸ e.symm)⟩
  · obtain ⟨p,e,_⟩ := neighbor2 G d two d
    have pd : deg G p = 2 := (reg p).resolve_left (by
      have pos := e.degree_pos_right
      rw [deg,G.ncard_neighborSet]
      omega)
    obtain ⟨q,f,hq⟩ := neighbor2 G p pd d
    exact ⟨p,q,f,e.ne.symm,hq⟩

theorem restrict_edge_on {n : ℕ} (G : SimpleGraph (Fin n)) (d : Fin n) (x : Fin n → Bool) :
    EdgeOn G (Function.update x d false) ↔ EdgeOn (G.deleteIncidenceSet d) x := by
  constructor
  · rintro ⟨p,q,h,hp,hq⟩
    have pd : p ≠ d := fun eq => by subst p; simp at hp
    have qd : q ≠ d := fun eq => by subst q; simp at hq
    exact ⟨p,q,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h,pd,qd⟩,
      by simpa [Function.update_of_ne pd] using hp,by simpa [Function.update_of_ne qd] using hq⟩
  · rintro ⟨p,q,h,hp,hq⟩
    obtain ⟨he,pd,qd⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    exact ⟨p,q,he,by simpa [Function.update_of_ne pd] using hp,by simpa [Function.update_of_ne qd] using hq⟩

theorem pay_restrict {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}
    (hm : Monotone2 C) (hc : Computes G C) (hA : Counts C A) (v : Fin n) (P : Finset ℕ)
    (hP : ∀ j ∈ P, Charged C v j) : Pay (G.deleteIncidenceSet v) (A.card - P.card) := by
  classical
  have sub : P ⊆ A := by
    intro j hj
    obtain ⟨g,hg,ho,_⟩ := hP j hj
    exact hA j g hg ho
  obtain ⟨D,hD,he,hB⟩ := restrict_paid C v A P hm hA (fun j hj => by
    obtain ⟨g,hg,ho,w,hw,hz⟩ := hP j hj
    exact ⟨g,hg,ho,w,hw,fun x => hz _ (by simp)⟩)
  refine ⟨D,A \ P,hD,fun x => ?_,hB,(Finset.card_sdiff_of_subset sub).le⟩
  rw [he,hc,restrict_edge_on]

theorem charged_mem {n : ℕ} {C : Circuit} {A : Finset ℕ} (ha : Counts C A)
    {v : Fin n} {j : ℕ} (h : Charged C v j) : j ∈ A := by
  obtain ⟨g,hg,ho,_⟩ := h
  exact ha j g hg ho

theorem pay_isolated {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}
    (hm : Monotone2 C) (hc : Computes G C) (hA : Counts C A) {v : Fin n} {j : ℕ}
    (hd : deg G v = 0) (hj : Charged C v j) : Pay G (A.card-1) := by
  classical
  have de : G.deleteIncidenceSet v = G := by
    ext p q
    rw [SimpleGraph.deleteIncidenceSet_adj]
    refine ⟨fun h => h.1,fun e => ⟨e,?_,?_⟩⟩
    · intro eq
      subst p
      have pos := e.degree_pos_left
      rw [deg,G.ncard_neighborSet] at hd
      omega
    · intro eq
      subst q
      have pos := e.degree_pos_right
      rw [deg,G.ncard_neighborSet] at hd
      omega
  have h := pay_restrict hm hc hA v {j} (by simpa using hj)
  simpa [de] using h

theorem one_charge {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hm : Monotone2 C) (hc : Computes G C) (v : Fin n) (active : ∃ z, G.Adj v z)
    (remain : ∃ p q, G.Adj p q ∧ p ≠ v ∧ q ≠ v) : ∃ j, Charged C v j := by
  classical
  by_contra! never
  obtain ⟨z,e⟩ := active
  obtain ⟨p,q,f,hp,hq⟩ := remain
  have eq := front_eq C hm {v} (bits {v,z}) (bits {z}) C.gates.length
    (by intro d hd; simp only [Finset.mem_singleton] at hd; simp [bits,hd])
    (by intro g hg; simp at hg)
    (by
      intro i g hg ho _ w hw d hd hz
      obtain rfl := Finset.mem_singleton.mp hd
      exact never i ⟨g,hg,ho,w,hw,hz⟩)
    (by
      intro d hd
      obtain rfl := Finset.mem_singleton.mp hd
      exact ⟨bits {p,q},by simp [bits,hp.symm,hq.symm],(hc _).mpr ((edge_pair _ _ _).mpr f)⟩)
  have hon := (hc _).mpr ((edge_pair _ _ _).mpr e)
  exact no_edge_single G z ((hc _).mp (eq ▸ hon))

theorem leaf_step {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) (ha : Pay G a)
    (ge : 2 ≤ G.edgeSet.ncard) (h : ∃ v, deg G v = 1) :
    ∃ v b, deg G v = 1 ∧ Pay (G.deleteIncidenceSet v) b ∧ b+1 ≤ a := by
  classical
  obtain ⟨v,hv⟩ := h
  obtain ⟨C,A,hm,hc,hA,ha⟩ := ha
  have d := delete_count G v
  obtain ⟨p,q,hh⟩ := edge_of_count (G.deleteIncidenceSet v) (by omega)
  have active : ∃ z, G.Adj v z := (G.degree_pos_iff_exists_adj v).mp (by
    rw [←G.ncard_neighborSet]; change 0 < deg G v; omega)
  obtain ⟨j,hj⟩ := one_charge hm hc v active ⟨p,q,SimpleGraph.deleteIncidenceSet_adj.mp hh⟩
  have pos := Finset.card_pos.mpr ⟨j,charged_mem hA hj⟩
  have cut := pay_restrict hm hc hA v {j} (by simpa using hj)
  exact ⟨v,A.card-1,hv,by simpa using cut,by omega⟩

abbrev DoubleCharge (n : ℕ) := ∀ (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ),
  Monotone2 C → Computes G C → Counts C A → 2 ≤ G.edgeSet.ncard →
  (∀ v, deg G v = 0 ∨ deg G v = 2) →
  (∀ u v, u ≠ v → deg G u = 2 → G.neighborSet u ≠ G.neighborSet v) →
  (∀ j g, C.gates[j]?=some g → g.op=.or → ¬∃ z, AliasAt C (none : Option (Fin n)) j z) →
  (∀ v j, deg G v=0 → ¬Charged C v j) →
  ∃ v i j, deg G v=2 ∧ i≠j ∧ Charged C v i ∧ Charged C v j

theorem no_redundant_or {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}
    (hm : Monotone2 C) (hc : Computes G C) (hA : Counts C A)
    (least : ∀ b, Pay G b → A.card ≤ b)
    (j : ℕ) (g : Gate) (hg : C.gates[j]?=some g) (ho : g.op=.or) :
    ¬∃ z, AliasAt C (none : Option (Fin n)) j z := by
  classical
  intro hzAlias
  obtain ⟨D,hm',eq,cap⟩ := rewrite_paid C (none : Option (Fin n)) A {j} hm hA (by simpa using hzAlias)
  have sub : {j} ⊆ A := Finset.singleton_subset_iff.mpr (hA j g hg ho)
  have hcard := Finset.card_sdiff_of_subset sub
  have pos := Finset.card_pos.mpr ⟨j,hA j g hg ho⟩
  have le := least (A \ {j}).card ⟨D,A \ {j},hm',fun x => by rw [eq]; exact hc x,cap,le_rfl⟩
  simp only [Finset.card_singleton] at hcard
  omega

theorem ring_step {n : ℕ} (cb : DoubleCharge n) (G : SimpleGraph (Fin n)) (a : ℕ) (ha : Pay G a)
    (ge : 2 ≤ G.edgeSet.ncard) (reg : ∀ v, deg G v = 0 ∨ deg G v = 2)
    (nt : ∀ u v, u ≠ v → deg G u = 2 → G.neighborSet u ≠ G.neighborSet v) :
    ∃ v b, deg G v = 2 ∧ Pay (G.deleteIncidenceSet v) b ∧ b+2 ≤ a := by
  classical
  let witness : ∃ b, Pay G b := ⟨a,ha⟩
  obtain ⟨C,A,hm,hc,hA,hmin⟩ := Nat.find_spec witness
  have least (b : ℕ) (hb : Pay G b) : A.card ≤ b := hmin.trans (Nat.find_min' witness hb)
  have bound : A.card ≤ a := least _ ha
  obtain ⟨v,i,j,hd,ne,hi,hj⟩ := cb G C A hm hc hA ge reg nt (no_redundant_or hm hc hA least)
    (fun d k iso h => by
      have le := least _ (pay_isolated hm hc hA iso h)
      have pos := Finset.card_pos.mpr ⟨k,charged_mem hA h⟩
      omega)
  have all : ∀ k ∈ ({i,j} : Finset ℕ), Charged C v k := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    exact hk.elim (fun h => h ▸ hi) (fun h => h ▸ hj)
  have card : ({i,j} : Finset ℕ).card = 2 := by simp [ne]
  have enough : 2 ≤ A.card := by
    rw [←card]
    exact Finset.card_le_card (fun k h => charged_mem hA (all k h))
  have lowered := pay_restrict hm hc hA v {i,j} all
  rw [card] at lowered
  exact ⟨v,A.card-2,hd,lowered,by omega⟩

theorem finish (cb : ∀ n, DoubleCharge n) (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (hs : Sparse G) (hn : NoFour G) (hm : Monotone2 C) (hc : Computes G C) (hA : Counts C A) :
    G.edgeSet.ncard ≤ A.card + 1 :=
  induct_cost Pay leaf_step (ring_step (cb n)) G A.card hs hn ⟨C,A,hm,hc,hA,le_rfl⟩

end M599

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem rawRead {n : ℕ} (C : Circuit) (j : ℕ)
    (before : ∀ g ∈ C.gates.take j, g.op = .and) (a : ℕ) :
    RawTerm (fun x : Fin n → Bool => readAt C j x a) :=
  raw_before _ before a

def HasOr (C : Circuit) (j : ℕ) : Prop := ∃ g : Gate, C.gates[j]?=some g ∧ g.op=.or

theorem has_first {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (hm : Monotone2 C)
    (hf : ∀ x, C.eval (List.ofFn x)=true ↔ EdgeOn G x)
    (nonempty : ∃ x : Fin n → Bool, EdgeOn G x)
    (avoid : ∀ d, ∃ x : Fin n → Bool, x d=false ∧ EdgeOn G x) :
    ∃ j g, C.gates[j]?=some g ∧ g.op=.or ∧ (∀ h ∈ C.gates.take j, h.op=.and) := by
  classical
  have monoOr (g : Gate) (hg : g ∈ C.gates) : g.op=.and ∨ g.op=.or := (hm g hg).1
  have indexed (g : Gate) (hg : g ∈ C.gates) : ∃ i : ℕ, C.gates[i]?=some g := by
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hg
    exact ⟨i,(List.getElem?_eq_getElem hi).trans (congrArg some he)⟩
  have existsOr : ∃ i, HasOr C i := by
    by_contra hn
    have alland : ∀ g ∈ C.gates, g.op=.and := by
      intro g hg
      apply (monoOr g hg).resolve_right
      intro hor
      obtain ⟨i,hi⟩ := indexed g hg
      exact hn ⟨i,g,hi,hor⟩
    have raw := raw_before (n:=n) C.gates alland C.output
    change RawTerm (fun x : Fin n → Bool => C.eval (List.ofFn x)) at raw
    obtain ⟨u,hu⟩ := nonempty
    rcases raw with ff | ⟨S,hS⟩
    · exact Bool.noConfusion ((ff u).symm.trans ((hf u).mpr hu))
    by_cases he : S.Nonempty
    · obtain ⟨d,hd⟩ := he
      obtain ⟨x,hx,hy⟩ := avoid d
      have xt := (hS x).mp ((hf x).mpr hy) d hd
      exact Bool.noConfusion (hx.symm.trans xt)
    · have eq := Finset.not_nonempty_iff_eq_empty.mp he
      have yes := (hf (fun _ => false)).mp ((hS _).mpr (by simp [eq]))
      simp [EdgeOn] at yes
  let j := Nat.find existsOr
  obtain ⟨g,idx,op⟩ := Nat.find_spec existsOr
  refine ⟨j,g,idx,op,?_⟩
  intro h hh
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hh
  have hij : i<j := by
    have bound : (C.gates.take j).length ≤ j := by simp
    exact lt_of_lt_of_le hi bound
  have readH : C.gates[i]? = some h := by
    have z := List.getElem?_eq_getElem hi
    simp only [List.getElem?_take,hij,↓reduceIte] at z
    exact z.trans (congrArg some eq)
  apply (monoOr h (List.mem_of_getElem? readH)).resolve_right
  intro oh
  exact (Nat.find_min existsOr hij) ⟨_,readH,oh⟩

theorem genuine_arms {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (idx : C.gates[j]?=some g) (op : g.op=.or) (arity : g.inputs.length≤2)
    (pre : ∀ h ∈ C.gates.take j, h.op=.and)
    (useful : ¬∃ z, AliasAt C (none : Option (Fin n)) j z) :
    ∃ a b, g.inputs=[a,b] ∧ ∃ S T : Finset (Fin n), S.Nonempty ∧ T.Nonempty ∧
       (∀ x, readAt C j x a=true ↔ InArm S x) ∧
       (∀ x, readAt C j x b=true ↔ InArm T x) := by
  classical
  have absurdAlias (z : Bool ⊕ ℕ)
      (h : ∀ x : Fin n → Bool, g.op.eval (g.inputs.map (readAt C j x))=repValue C j x z) : False :=
    useful ⟨z, fun x => (readAt_new C j x g idx).trans (h x)⟩
  cases hg : g.inputs with
  | nil => exact (absurdAlias (.inl false) (by simp [op,hg,GateOp.eval,repValue])).elim
  | cons a l =>
    cases l with
    | nil => exact (absurdAlias (.inr a) (by simp [op,hg,GateOp.eval,repValue])).elim
    | cons b l =>
      have hl : l=[] := by simpa [hg] using arity
      subst l
      refine ⟨a,b,rfl,?_⟩
      rcases rawRead (n:=n) C j pre a with h | ⟨S,hS⟩
      · exact (absurdAlias (.inr b) (by simp [op,hg,GateOp.eval,repValue,h])).elim
      rcases rawRead (n:=n) C j pre b with h | ⟨T,hT⟩
      · exact (absurdAlias (.inr a) (by simp [op,hg,GateOp.eval,repValue,h])).elim
      have nearm (u : ℕ) (K : Finset (Fin n))
          (hu : u=a ∨ u=b) (hK : ∀ x, readAt C j x u=true ↔ InArm K x) : K.Nonempty := by
        by_contra emp
        have ke := Finset.not_nonempty_iff_eq_empty.mp emp
        have yes (x : Fin n → Bool) := (hK x).mpr (by simp [InArm,ke])
        rcases hu with rfl | rfl <;>
          exact absurdAlias (.inl true) (by simp [op,hg,GateOp.eval,repValue,yes])
      exact ⟨S,T,nearm a S (Or.inl rfl) hS,nearm b T (Or.inr rfl) hT,hS,hT⟩

end M599

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem arm_low {n : ℕ} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n))
    (h : ∀ x, f x = true ↔ InArm S x) (d : Fin n) (hd : d ∈ S)
    (x : Fin n → Bool) (hx : x d = false) : f x = false := by
  cases eq : f x with
  | false => rfl
  | true => have bad := (h x).mp eq d hd; rw [hx] at bad; contradiction

theorem first_charges {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (idx : C.gates[j]? = some g) (op : g.op = .or) (a b : ℕ) (hargs : g.inputs = [a,b])
    (S T : Finset (Fin n)) (hS : ∀ x, readAt C j x a = true ↔ InArm S x)
    (hT : ∀ x, readAt C j x b = true ↔ InArm T x) : ∀ d ∈ S ∪ T, Charged C d j := by
  intro d hd
  refine ⟨g, idx, op, ?_⟩
  rcases Finset.mem_union.mp hd with hs | ht
  · exact ⟨a, by simp [hargs], arm_low _ S hS d hs⟩
  · exact ⟨b, by simp [hargs], arm_low _ T hT d ht⟩

theorem first_factors {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : Monotone2 C) (hc : Computes G C) (j : ℕ) (g : Gate)
    (idx : C.gates[j]? = some g) (op : g.op = .or) (a b : ℕ) (hargs : g.inputs = [a,b])
    (S T : Finset (Fin n)) (hS : ∀ x, readAt C j x a = true ↔ InArm S x)
    (hT : ∀ x, readAt C j x b = true ↔ InArm T x)
    (avoidOutput : ∀ d, ∃ x : Fin n → Bool, x d = false ∧ C.eval (List.ofFn x) = true)
    (unique : ∀ d ∈ S ∪ T, ∀ k, Charged C d k → k = j)
    (noniso : ∀ d ∈ S ∪ T, ∃ w, G.Adj d w) : MonomialFactors G S T ∧ Disjoint S T := by
  have uncharged (d : Fin n) (hd : d ∈ S ∪ T) (i : ℕ) (gate : Gate)
      (hg : C.gates[i]? = some gate) (ho : gate.op = .or) (hij : i ≠ j)
      (w : ℕ) (hw : w ∈ gate.inputs) : ¬ ∀ x : Fin n → Bool, x d = false → readAt C i x w = false :=
    fun low => hij (unique d hd i ⟨gate, hg, ho, w, hw, low⟩)
  have val (x : Fin n → Bool) : g.op.eval (g.inputs.map (readAt C j x)) = true ↔ SplitArm S T x := by
    simp [op, hargs, GateOp.eval, SplitArm, hS, hT]
  constructor
  · intro D sub x y outside same
    have eq := front_eq C hmono D x y j outside (fun gate hgate => by
      have he : gate = g := Option.some.inj (hgate.symm.trans idx)
      subst gate
      exact Or.inl (Bool.eq_iff_iff.mpr ((val x).trans (same.trans (val y).symm))))
      (fun i gate hg ho hij w hw d hd => uncharged d (sub hd) i gate hg ho hij w hw)
      (fun d _ => avoidOutput d)
    exact (hc x).symm.trans (eq ▸ hc y)
  · apply overlap_impossible G S T noniso
    intro d hs ht x y outside
    have eq := front_eq_of_low C hmono d x y j outside (fun gate hgate z hz => by
      have he : gate = g := Option.some.inj (hgate.symm.trans idx)
      subst gate
      simp [op, hargs, GateOp.eval, arm_low _ S hS d hs z hz, arm_low _ T hT d ht z hz])
      (uncharged d (Finset.mem_union_left _ hs)) (avoidOutput d)
    exact (hc x).symm.trans (eq ▸ hc y)

end M599

namespace M599
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity M599Graph

theorem double_charge (n : ℕ) : DoubleCharge n := by
  classical
  intro G C A hm hc _ ge regular twins useful inert
  obtain ⟨p,q,epq⟩ := edge_of_count G (by omega)
  have positive : ∃ x : Fin n → Bool, EdgeOn G x := ⟨bits {p,q},(edge_pair G p q).mpr epq⟩
  have off (d : Fin n) : ∃ x : Fin n → Bool, x d=false ∧ EdgeOn G x := by
    obtain ⟨u,v,e,hu,hv⟩ := avoid G ge regular d
    exact ⟨bits {u,v},by simp [bits,hu.symm,hv.symm],(edge_pair G u v).mpr e⟩
  have out (d : Fin n) : ∃ x : Fin n → Bool, x d=false ∧ C.eval (List.ofFn x)=true := by
    obtain ⟨x,zero,yes⟩ := off d
    exact ⟨x,zero,(hc x).mpr yes⟩
  obtain ⟨j,g,idx,op,pre⟩ := has_first G C hm hc positive off
  have ar := (hm g (List.mem_of_getElem? idx)).2
  obtain ⟨a,b,args,S,T,sne,tne,hs,ht⟩ := genuine_arms C j g idx op ar pre (useful j g idx op)
  have paid := first_charges C j g idx op a b args S T hs ht
  have degree (d : Fin n) (hd : d ∈ S ∪ T) : deg G d = 2 :=
    (regular d).resolve_left (fun hz => inert d j hz (paid d hd))
  by_contra bad
  have single (d : Fin n) (hd : d ∈ S ∪ T) (k : ℕ) (charged : Charged C d k) : k=j := by
    by_contra ne
    exact bad ⟨d,k,j,degree d hd,ne,charged,paid d hd⟩
  have noniso (d : Fin n) (hd : d ∈ S ∪ T) : ∃ z, G.Adj d z := by
    obtain ⟨z,he,_⟩ := neighbor2 G d (degree d hd) d
    exact ⟨z,he⟩
  obtain ⟨f,dis⟩ := first_factors G C hm hc j g idx op a b args S T hs ht out single noniso
  obtain ⟨u,hu⟩ := sne
  obtain ⟨v,hv⟩ := tne
  have du := degree u (Finset.mem_union_left T hu)
  have ne : u ≠ v := fun h => Finset.disjoint_left.mp dis hu (h ▸ hv)
  have left := arm_unique G S T dis
    (fun d hd => neighbor2 G d (degree d (Finset.mem_union_left _ hd))) f
  have right := arm_unique G T S dis.symm
    (fun d hd => neighbor2 G d (degree d (Finset.mem_union_right _ hd))) (factors_swap f)
  have es : S = {u} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hu,fun z hz => left z hz u hu⟩
  have et : T = {v} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hv,fun z hz => right z hz v hv⟩
  exact twins u v ne du (singleton_twins G u v (es ▸ et ▸ f))

end M599

theorem PEqualNP.Outside.L_meta_599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ), (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) → (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → G.edgeSet.ncard ≤ A.card + 1 := by
  exact M599.finish M599.double_charge
