import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13009_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The backward support argument refines RepReads.needed by charging zero for NOT.
def pins (g : Gate) : List Nat := match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def charge (g : Gate) : Nat := match g.op with
  | .not => 0
  | _ => 1

def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

lemma pinBound (g : Gate) (h : g.inputs.length ≤ 2) :
    (pins g).length ≤ charge g + 1 := by
  rcases g with ⟨op,ins⟩
  cases op <;> simp_all [pins,charge]

lemma runGate (g : Gate) (x y : Nat → Bool) (eq : ∀ i ∈ pins g,x i=y i) :
    g.op.eval (g.inputs.map x)=g.op.eval (g.inputs.map y) := by
  rcases g with ⟨op,ins⟩
  cases op <;> try
    apply congrArg _
    apply List.map_congr_left
    simpa [pins] using eq
  cases ins with
  | nil => rfl
  | cons a xs =>
    have h := eq a (by simp [pins])
    simp [GateOp.eval,h]

lemma lastLookup (xs : List Bool) (z : Bool) (i : Nat) :
    (xs ++ [z]).getD i false = if i=xs.length then z else xs.getD i false := by
  split_ifs with h
  · subst i
    simp
  · rcases Nat.lt_or_gt_of_ne h with h|h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

lemma needed (gs : List Gate) (h : ∀ g ∈ gs,g.inputs.length≤2) :
    ∀ (n : Nat) (N : Finset Nat),∃ S : Finset Nat,S.card≤N.card+(gs.map charge).sum ∧
    ∀ (x y : List Bool),x.length=n → y.length=n → (∀ i ∈ S,x.getD i false=y.getD i false) →
    ∀ i ∈ N,(gs.foldl step x).getD i false=(gs.foldl step y).getD i false := by
  induction gs with
  | nil =>
    intro n N
    exact ⟨N,by simp,fun x y _ _ e => e⟩
  | cons g gs ih =>
    intro n N
    obtain ⟨S,bound,agree⟩ := ih (fun w hw => h w (by simp [hw])) (n+1) N
    have combine (U : Finset Nat)
        (fix : ∀ x y : List Bool,x.length=n → y.length=n →
          (∀ i ∈ U,x.getD i false=y.getD i false) →
          ∀ i ∈ S,(step x g).getD i false=(step y g).getD i false) :
        ∀ x y : List Bool,x.length=n → y.length=n → (∀ i ∈ U,x.getD i false=y.getD i false) →
        ∀ i ∈ N,((g::gs).foldl step x).getD i false=((g::gs).foldl step y).getD i false := by
      intro x y hx hy same
      exact agree (step x g) (step y g) (by simp [step,hx]) (by simp [step,hy]) (fix x y hx hy same)
    by_cases mem : n∈S
    · refine ⟨S.erase n ∪ (pins g).toFinset,?_,combine _ ?_⟩
      · have hu := Finset.card_union_le (S.erase n) (pins g).toFinset
        have he := Finset.card_erase_of_mem mem
        have hp := List.toFinset_card_le (pins g)
        have hb := pinBound g (h g (by simp))
        have hs : 0<S.card := Finset.card_pos.mpr ⟨n,mem⟩
        simp only [List.map_cons,List.sum_cons]
        omega
      · intro x y hx hy same i hi
        simp only [step,lastLookup,hx,hy]
        split_ifs with e
        · apply runGate
          intro j hj
          exact same j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
        · exact same i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩))
    · refine ⟨S,?_,combine _ ?_⟩
      · simp only [List.map_cons,List.sum_cons]
        omega
      · intro x y hx hy same i hi
        have ne : i≠n := fun e => mem (e ▸ hi)
        simp only [step,lastLookup,hx,hy]
        split_ifs with eq
        · exact (ne eq).elim
        · exact same i hi

lemma chargeAtMostOne (g : Gate) : charge g ≤ 1 := by
  rcases g with ⟨op,ins⟩
  cases op <;> simp [charge]

lemma chargeBound (gs : List Gate) : (gs.map charge).sum ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hc := chargeAtMostOne g
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

lemma chargeStrict (gs : List Gate) (neg : ∃ g ∈ gs,g.op=.not) :
    (gs.map charge).sum < gs.length := by
  induction gs with
  | nil => simp at neg
  | cons g gs ih =>
    obtain ⟨t,ht,op⟩ := neg
    rcases List.mem_cons.mp ht with same|later
    · subst t
      have hc : charge g=0 := by simp [charge,op]
      have hb := chargeBound gs
      simp only [List.map_cons,List.sum_cons,List.length_cons,hc]
      omega
    · have hb := ih ⟨t,later,op⟩
      have hc := chargeAtMostOne g
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega

lemma rawRead {n : Nat} (v : Fin n → Bool) {j : Nat} (hj : j<n) :
    (List.ofFn v).getD j false=v ⟨j,hj⟩ := by
  simp [List.getD_eq_getElem?_getD,hj]

lemma essentialBound {n : Nat} (C : Circuit) (basis : FanInTwo C) (f : (Fin n → Bool) → Bool)
    (computes : ∀ x,C.eval (List.ofFn x)=f x)
    (essential : ∀ k : Fin n,∃ x y : Fin n → Bool,(∀ j,j≠k → x j=y j) ∧ f x≠f y) :
    n ≤ 1+(C.gates.map charge).sum := by
  obtain ⟨S,hS,agree⟩ := needed C.gates (fun g hg => (basis g hg).2) n {C.output}
  have allRaw : Finset.range n ⊆ S := by
    intro j hj
    by_contra outside
    let k : Fin n := ⟨j,Finset.mem_range.mp hj⟩
    obtain ⟨x,y,same,changes⟩ := essential k
    apply changes
    rw [← computes x,← computes y]
    apply agree (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
    intro m hm
    by_cases mb : m<n
    · rw [rawRead x mb,rawRead y mb]
      apply same
      intro h
      have e : m=j := congrArg Fin.val h
      exact outside (e ▸ hm)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt mb),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt mb)]
  have h := Finset.card_le_card allRaw
  simp only [Finset.card_range] at h
  simp only [Finset.card_singleton] at hS
  omega

end PEqualNP.Outside.L_meta_13009_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_13009_aux

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_13009 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4005620416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4005620416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let f := fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2^32 + 4005620416)
    (∑ i : Fin 6, if x i then 2^i.val else 0)
  let row := fun (k i : Fin 6) => (([8,4,2,1,10,1] : List Nat).getD k.val 0).testBit i.val
  have sensitive : ∀ k : Fin 6,f (row k)≠f (Function.update (row k) k true) := by decide +kernel
  have essential : ∀ k : Fin 6,∃ x y : Fin 6 → Bool,(∀ j,j≠k → x j=y j) ∧ f x≠f y := by
    intro k
    exact ⟨row k,Function.update (row k) k true,fun j ne => (Function.update_of_ne ne _ _).symm,sensitive k⟩
  let model : Circuit := ⟨[⟨.or,[3,5]⟩,⟨.and,[0,6]⟩,⟨.and,[3,4]⟩,
    ⟨.or,[2,8]⟩,⟨.and,[1,9]⟩,⟨.or,[7,10]⟩],11⟩
  have good : Monotone2 model := by
    simp [Monotone2,model]
  have truth : ∀ x : Fin 6 → Bool,model.eval (List.ofFn x)=f x := by decide +kernel
  intro s small
  by_cases six : 6≤s
  · exact ⟨model,good,six,truth⟩
  · obtain ⟨C,basis,sz,spec⟩ := small
    have needed := essentialBound C basis f spec essential
    refine ⟨C,?_,sz,spec⟩
    intro g hg
    obtain ⟨op,arity⟩ := basis g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
    refine ⟨?_,arity⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rcases op with a|b|c
    · exact Or.inl a
    · exact Or.inr b
    · have hc := chargeStrict C.gates ⟨g,hg,c⟩
      change C.gates.length≤s at sz
      omega
