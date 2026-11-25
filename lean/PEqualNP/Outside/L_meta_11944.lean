import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11944
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def baseline : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[7,2]⟩,⟨.or,[5,6]⟩,
  ⟨.or,[4,9]⟩,⟨.or,[0,9]⟩,⟨.and,[8,10]⟩,⟨.and,[3,11]⟩,⟨.or,[12,13]⟩],14⟩
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
theorem baseline_ok : ∀ x : Fin 7 → Bool, baseline.eval (List.ofFn x) = target x := by
  decide +kernel
theorem size_ok : baseline.size = 8 := rfl
theorem monotone_ok : Monotone2 baseline := by
  intro g hg
  simp [baseline] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
theorem rising_inputs : ∀ i : Fin 7, ∃ y : Fin 7 → Bool,
    y i = false ∧ target y = false ∧ target (Function.update y i true) = true := by
  decide +kernel

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

-- Trace the requested output wires backwards through the remaining gates.
def demand (n : ℕ) (gs : List Gate) (targets : Finset ℕ) : Finset ℕ :=
  match gs with
  | [] => targets
  | g :: tail =>
    let s := demand (n+1) tail targets
    if n ∈ s then (s.erase n) ∪ g.inputs.toFinset else s

theorem demand_card (n : ℕ) (gs : List Gate) (targets : Finset ℕ)
    (binary : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (demand n gs targets).card ≤ targets.card + gs.length := by
  induction gs generalizing n with
  | nil => simp [demand]
  | cons g gs ih =>
    have bound := ih (n+1) (fun a h => binary a (List.mem_cons_of_mem _ h))
    have deg := (List.toFinset_card_le g.inputs).trans (binary g (by simp))
    simp only [demand,List.length_cons]
    split_ifs with mem
    · have remove := Finset.card_erase_add_one mem
      have split := Finset.card_union_le (demand (n+1) gs targets |>.erase n) g.inputs.toFinset
      omega
    · omega

def Mono (gs : List Gate) := ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

theorem demand_le (gs : List Gate) (S : Finset ℕ) (x y : List Bool) (mono : Mono gs)
    (len : x.length=y.length)
    (h : ∀ i ∈ demand x.length gs S, x.getD i false = true → y.getD i false = true) :
    ∀ i ∈ S, (wf gs x).getD i false = true → (wf gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun i => x.getD i false)
    let b := g.op.eval (g.inputs.map fun i => y.getD i false)
    let T := demand (x.length+1) gs S
    change ∀ i ∈ S, (wf gs (x ++ [a])).getD i false = true → (wf gs (y ++ [b])).getD i false = true
    apply ih _ _ (fun t ht => mono t (List.mem_cons_of_mem _ ht)) (by simp [len])
    have step : demand x.length (g::gs) S =
        if x.length ∈ T then (T.erase x.length) ∪ g.inputs.toFinset else T := rfl
    intro i hi
    have inT : i ∈ T := by simpa [T] using hi
    rcases Nat.lt_trichotomy i x.length with low | eq | high
    · rw [getD_snoc_lt _ _ _ low,getD_snoc_lt _ _ _ (len ▸ low)]
      apply h; rw [step]; split_ifs
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne_of_lt low,inT⟩)
      · exact inT
    · subst i
      rw [getD_snoc_eq,len,getD_snoc_eq]
      have operands : ∀ j ∈ g.inputs, x.getD j false = true → y.getD j false = true := by
        intro j hj
        apply h
        rw [step,ite_eq_left inT]
        exact Finset.mem_union_right _ (by simpa using hj)
      rcases (mono g (by simp)).1 with op | op
      · simp only [a,b,op,GateOp.eval,List.all_map,List.all_eq_true,Function.comp,id]
        exact fun on_ j hj => operands j hj (on_ j hj)
      · simp only [a,b,op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id]
        exact fun ⟨j,hj,on_⟩ => ⟨j,hj,operands j hj on_⟩
    · rw [getD_snoc_gt _ _ _ high]; simp

theorem neg_le (ins : List ℕ) (x y : List Bool)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    GateOp.not.eval (ins.map fun i => y.getD i false) = true →
      GateOp.not.eval (ins.map fun i => x.getD i false) = true := by
  cases ins with
  | nil => exact id
  | cons i rest =>
    simp only [GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
    intro off
    exact Bool.eq_false_iff.mpr fun on_ => by have := h i on_; simp_all

def notBit (ins : List ℕ) (w : List Bool) := GateOp.not.eval (ins.map fun i => w.getD i false)

theorem split_value (pre post : List Gate) (ins : List ℕ) (o : ℕ) (X : List Bool) :
    Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ X =
      (wf post (wf pre X ++ [notBit ins (wf pre X)])).getD o false := by
  simp [Circuit.eval,Circuit.wires,wf,List.foldl_append,notBit]

theorem append_le (S : Finset ℕ) (U V : List Bool) (a b : Bool) (len : U.length=V.length)
    (base : ∀ i ∈ S.erase U.length, U.getD i false = true → V.getD i false = true)
    (newBit : U.length ∈ S → a = true → b = true) :
    ∀ i ∈ S, (U ++ [a]).getD i false = true → (V ++ [b]).getD i false = true := by
  intro i hi
  rcases Nat.lt_trichotomy i U.length with lt | eq | gt
  · rw [getD_snoc_lt _ _ _ lt,getD_snoc_lt _ _ _ (len ▸ lt)]
    exact base i (Finset.mem_erase.mpr ⟨lt.ne,hi⟩)
  · subst i; rw [getD_snoc_eq,len,getD_snoc_eq]; exact newBit hi
  · rw [getD_snoc_gt _ _ _ gt]; simp


-- A rising input must reach the output on a path other than the falling NOT wire.
theorem useful_cost (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (mp : Mono pre) (ms : Mono post)
    (correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post, o⟩ (List.ofFn x) = target x)
    (used : 7+pre.length ∈ demand (7+pre.length+1) post {o}) :
    8 ≤ (pre ++ ⟨GateOp.not,ins⟩ :: post).length := by
  let m := 7+pre.length
  let S := demand (m+1) post {o}
  let T := demand 7 pre (S.erase m)
  have sub : Finset.range 7 ⊆ T := by
    intro i hi
    have lt := Finset.mem_range.mp hi
    let v : Fin 7 := ⟨i,lt⟩
    by_contra absent
    obtain ⟨x,xoff,lo,rise⟩ := rising_inputs v
    let y := Function.update x v true
    let X := List.ofFn x
    let Y := List.ofFn y
    let U := wf pre X
    let V := wf pre Y
    have ulen : U.length=m := by simp [U,X,m,wf_len]
    have vlen : V.length=m := by simp [V,Y,m,wf_len]
    have raw (j : ℕ) (jne : j ≠ i) : Y.getD j false = X.getD j false := by
      by_cases hj : j < 7
      · have ne : (⟨j,hj⟩ : Fin 7) ≠ v := fun e => jne (congrArg Fin.val e)
        simp only [Y,X,y,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hj,dite_eq_left,Option.getD_some,Function.update_of_ne ne]
      · simp [Y,X,List.getD_eq_getElem?_getD,hj]
    have down : ∀ j ∈ T, Y.getD j false = true → X.getD j false = true := by
      intro j hj; rw [raw j (fun e => absent (e ▸ hj))]; exact id
    have rest (j : ℕ) (hj : j ∈ S.erase m) : V.getD j false = true → U.getD j false = true := by
      apply demand_le pre (S.erase m) Y X mp (by simp [Y,X]) _ j hj
      simpa only [Y,List.length_ofFn] using down
    have ordered (j : ℕ) : X.getD j false = true → Y.getD j false = true := by
      by_cases e : j=i
      · subst j
        simp only [X,List.getD_eq_getElem?_getD,List.getElem?_ofFn,lt,dite_eq_left,Option.getD_some]
        intro on_
        exact (Bool.noConfusion (xoff.symm.trans on_))
      · rw [raw j e]; exact id
    have prefixOrder (j : ℕ) : U.getD j false = true → V.getD j false = true := by
      apply demand_le pre {j} X Y mp (by simp [X,Y]) (fun k _ => ordered k) j (by simp)
    have cannotRise := neg_le ins U V prefixOrder
    have dom (j : ℕ) (hj : j ∈ S) :
        (V ++ [notBit ins V]).getD j false = true → (U ++ [notBit ins U]).getD j false = true :=
      append_le S V U _ _ (vlen.trans ulen.symm)
        (fun k hk => rest k (vlen ▸ hk)) (fun _ => cannotRise) j hj
    have toOld := demand_le post {o} (V ++ [notBit ins V]) (U ++ [notBit ins U]) ms
      (by simp [ulen,vlen]) (by simpa only [List.length_append,List.length_cons,List.length_nil,vlen] using dom) o (by simp)
    have hy := (correct y).trans rise
    have hx := (correct x).trans lo
    rw [split_value] at hy hx
    have contra := toOld hy
    rw [show (wf post (U ++ [notBit ins U])).getD o false = false from hx] at contra
    contradiction
  have low := Finset.card_le_card sub
  simp only [Finset.card_range] at low
  have bp := demand_card 7 pre (S.erase m) (fun g h => (mp g h).2)
  have bs := demand_card (m+1) post {o} (fun g h => (ms g h).2)
  have rem : (S.erase m).card+1=S.card := Finset.card_erase_add_one used
  change T.card ≤ (S.erase m).card+pre.length at bp
  change S.card ≤ ({o} : Finset ℕ).card+post.length at bs
  simp only [Finset.card_singleton] at bs
  simp only [List.length_append,List.length_cons]
  omega

-- An unread NOT can be replaced in place by a constant false OR.
theorem unused_eq (pre post : List Gate) (ins : List ℕ) (o : ℕ) (ms : Mono post)
    (unused : 7+pre.length ∉ demand (7+pre.length+1) post {o}) (x : Fin 7 → Bool) :
    Circuit.eval ⟨pre ++ ⟨.or,[]⟩ :: post,o⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (List.ofFn x) := by
  let W := wf pre (List.ofFn x)
  let m := 7+pre.length
  have len : W.length=m := by simp [W,m,wf_len]
  have pin (a b : Bool) : (wf post (W ++ [a])).getD o false = true →
      (wf post (W ++ [b])).getD o false = true := by
    apply demand_le post {o} _ _ ms (by simp) _ o (by simp)
    apply append_le _ W W _ _ rfl (fun _ _ => id)
    intro bad
    exact (unused (by simpa [len,m] using bad)).elim
  rw [split_value]
  have replaced : Circuit.eval ⟨pre ++ ⟨.or,[]⟩ :: post,o⟩ (List.ofFn x) =
      (wf post (W ++ [false])).getD o false := by
    simp [Circuit.eval,Circuit.wires,W,wf,List.foldl_append,GateOp.eval]
  rw [replaced]; exact Bool.eq_iff_iff.mpr ⟨pin _ _,pin _ _⟩

end PEqualNP.Outside.L_meta_11944

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_11944

theorem PEqualNP.Outside.L_meta_11944 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal unique correct
  by_cases large : 8 ≤ gates.length
  · exact ⟨baseline.gates,baseline.output,monotone_ok,size_ok.trans_le large,baseline_ok⟩
  by_cases someNot : ∃ g ∈ gates, g.op=.not
  · obtain ⟨⟨op,ins⟩,mem,e⟩ := someNot
    change op = .not at e
    subst op
    obtain ⟨pre,post,rfl⟩ := List.append_of_mem mem
    let g : Gate := ⟨.not,ins⟩
    let all := pre ++ g :: post
    let mid : Fin all.length := ⟨pre.length,by simp [all]⟩
    have atMid : (all.get mid).op = .not := by simp [all,mid,g,List.get_eq_getElem]
    have mp : Mono pre := by
      intro k hk
      obtain ⟨op,arity⟩ := legal k (List.mem_append_left _ hk)
      refine ⟨?_,arity⟩
      rcases op with hand | hor | hn
      · exact Or.inl hand
      · exact Or.inr hor
      · obtain ⟨i,lt,eq⟩ := List.getElem_of_mem hk
        let idx : Fin all.length := ⟨i,by simp [all]; omega⟩
        have atIdx : (all.get idx).op = .not := by
          simpa only [all,idx,List.get_eq_getElem,List.getElem_append_left lt,eq] using hn
        have same := congrArg Fin.val (unique idx mid atIdx atMid)
        change i=pre.length at same
        omega
    have ms : Mono post := by
      intro k hk
      obtain ⟨op,arity⟩ := legal k (by simp [hk])
      refine ⟨?_,arity⟩
      rcases op with hand | hor | hn
      · exact Or.inl hand
      · exact Or.inr hor
      · obtain ⟨i,lt,eq⟩ := List.getElem_of_mem hk
        let idx : Fin all.length := ⟨pre.length+(i+1),by simp [all]; omega⟩
        have atIdx : (all.get idx).op = .not := by
          simp only [all,idx,List.get_eq_getElem,List.getElem_append_right (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left,List.getElem_cons_succ,eq,hn]
        have same := congrArg Fin.val (unique idx mid atIdx atMid)
        change pre.length+(i+1)=pre.length at same
        omega
    have unused : 7+pre.length ∉ demand (7+pre.length+1) post {o} :=
      fun h => large (useful_cost pre post ins o mp ms correct h)
    refine ⟨pre ++ ⟨.or,[]⟩::post,o,?_,by simp,fun x => (unused_eq pre post ins o ms unused x).trans (correct x)⟩
    intro k hk
    simp only [List.mem_append,List.mem_cons] at hk
    rcases hk with h | rfl | h
    · exact mp k h
    · simp
    · exact ms k h
  · refine ⟨gates,o,?_,le_rfl,correct⟩
    intro k hk
    obtain ⟨op,arity⟩ := legal k hk
    rcases op with h | h | h
    · exact ⟨Or.inl h,arity⟩
    · exact ⟨Or.inr h,arity⟩
    · exact (someNot ⟨k,hk,h⟩).elim
