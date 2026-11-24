import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

open PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

def address (n : Nat) (S : List Nat) (w : Nat) :=
  if w<n then if w∈S then n+S.idxOf w else w else w+S.length
def copyGate (w : Nat) : Gate := ⟨.and,[w,w]⟩
def mapped (n : Nat) (S : List Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map (address n S)⟩
def wrap (n : Nat) (S : List Nat) (C : Circuit) : Circuit :=
  ⟨S.map copyGate ++ C.gates.map (mapped n S),address n S C.output⟩
theorem wrapSize (n : Nat) (S : List Nat) (C : Circuit) : (wrap n S C).size=S.length+C.size := by
  simp [wrap,Circuit.size]
theorem copyAt {n : Nat} {S : List Nat} {C : Circuit} {j : Nat} (h : j<S.length) :
    gateAt (wrap n S C) j=copyGate S[j] := by
  rw [gateAt_eq (by simp [wrap]; omega)]
  simp [wrap,List.getElem_append_left,h]
theorem mappedAt {n : Nat} {S : List Nat} {C : Circuit} {j : Nat} (h : j<C.size) :
    gateAt (wrap n S C) (S.length+j)=mapped n S (gateAt C j) := by
  rw [gateAt_eq (by change _ < (wrap n S C).size; rw [wrapSize]; omega),gateAt_eq h]
  simp [wrap,List.getElem_append_right]; rfl
theorem addrBound {n j w : Nat} (S : List Nat) (h : w<n+j) : address n S w < n+(S.length+j) := by
  unfold address; split
  next raw =>
    split
    next mem => have := List.idxOf_lt_length_iff.mpr mem; omega
    next => omega
  next => omega
theorem model {n : Nat} {S : List Nat} {C : Circuit} (good : IsAO2 n C) (raw : ∀w∈S,w<n) :
    IsAO2 n (wrap n S C) := by
  let D := wrap n S C
  have form (g : Gate) (hg : g∈D.gates) :
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
    rcases List.mem_append.mp hg with h|h
    · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h; exact ⟨Or.inl rfl,rfl⟩
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h; exact ⟨good.1 u hu,by simpa [mapped] using good.2.2 u hu⟩
  refine ⟨fun g h => (form g h).1,?_,fun g h => (form g h).2⟩
  intro k hk w hw
  by_cases early : k<S.length
  · rw [copyAt early] at hw
    have eq : w=S[k] := by simpa [copyGate] using hw
    have bound := raw S[k] (List.getElem_mem early); omega
  · let j:=k-S.length
    have eq : S.length+j=k := by dsimp [j]; omega
    change k<D.size at hk
    rw [show D.size=S.length+C.size from wrapSize ..] at hk
    have hj : j<C.size := by omega
    rw [←eq,mappedAt hj] at hw
    obtain ⟨v,read,rfl⟩ := List.mem_map.mp hw
    rw [←eq]; exact addrBound S (good.2.1 _ hj v read)
theorem safeOr {n : Nat} {D : Circuit} (col : Nat → Bool) (keep : Bool)
    (ok : ∀j<D.size,(gateAt D j).op=.or → ∀v∈(gateAt D j).inputs,v<n → col v=keep) :
    tCount n D col=0 := by
  classical
  unfold tCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j h
  obtain ⟨_,_,⟨a,ha,ca⟩,⟨b,hb,cb⟩⟩ := (Finset.mem_filter.mp h).2
  have mono (i : Fin n) (mem : i∈orIn n D (n+j)) : col i.val=keep := by
    simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at mem
    rcases mem with eq|⟨k,hk,_,hop,read⟩
    · have := i.isLt; omega
    · exact ok k hk hop _ read i.isLt
  have za := mono a ha; have zb := mono b hb; rw [ca] at za; rw [cb] at zb; cases za.trans zb.symm
theorem noMix {n : Nat} {S : List Nat} {C : Circuit} (col : Nat → Bool) (keep : Bool)
    (pick : ∀g∈C.gates,∀w∈g.inputs,w<n → col w≠keep → w∈S) : tCount n (wrap n S C) col=0 := by
  apply safeOr col keep
  intro k hk hop v read low
  by_cases early : k<S.length
  · rw [copyAt early] at hop; contradiction
  · let j:=k-S.length
    have eq : S.length+j=k := by dsimp [j]; omega
    rw [wrapSize] at hk
    have hj : j<C.size := by omega
    rw [←eq,mappedAt hj] at read
    obtain ⟨w,hit,rfl⟩ := List.mem_map.mp read
    by_cases raw : w<n
    · by_cases mem : w∈S
      · simp [address,raw,mem] at low
      · have clr : col w=keep := by by_contra ne; exact mem (pick _ (gateAt_mem hj) w hit raw ne)
        simpa [address,raw,mem] using clr
    · simp [address,raw] at low; omega


theorem readGate {n : Nat} {C : Circuit} (good : IsAO2 n C) {x : List Bool} (len : x.length=n)
    {j : Nat} (hj : j<C.size) :
    val C x (n+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (val C x)) := by
  rw [val_gate len hj]
  congr 1
  apply List.map_congr_left
  intro w read; simp [good.2.1 j hj w read]
theorem sim {n : Nat} {S : List Nat} {C : Circuit} (good : IsAO2 n C) (raw : ∀w∈S,w<n)
    (x : List Bool) (len : x.length=n) (w : Nat) : val (wrap n S C) x (address n S w)=val C x w := by
  let D:=wrap n S C
  have dm := model good raw
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases input : w<n
    · rw [val_input len input]
      by_cases mem : w∈S
      · have h : S.idxOf w < S.length := List.idxOf_lt_length_iff.mpr mem
        have hd : S.idxOf w < D.size := by rw [show D.size=S.length+C.size from wrapSize ..]; omega
        simp only [address,input,if_true,mem]
        rw [readGate dm len hd,copyAt h]
        have idx : S[S.idxOf w]=w := List.getElem_idxOf h
        simp [copyGate,idx,GateOp.eval,val_input len input]
      · simp only [address,input,mem,if_true,if_false]; exact val_input len input
    by_cases valid : w<n+C.size
    · let j := w-n
      have addressEq : n+j=w := by dsimp [j]; omega
      have hj : j<C.size := by omega
      have large : S.length+j<D.size := by rw [show D.size=S.length+C.size from wrapSize ..]; omega
      have lift : address n S w=n+(S.length+j) := by simp [address,input]; omega
      rw [lift,readGate dm len large,mappedAt hj,←addressEq,readGate good len hj]
      change (gateAt C j).op.eval (((gateAt C j).inputs.map (address n S)).map (val D x))=_
      rw [List.map_map]; congr 1; apply List.map_congr_left
      intro v read; exact ih v (by have := good.2.1 j hj v read; omega)
    · have oc : n+C.size≤w := by omega
      have od : n+D.size≤address n S w := by rw [show D.size=S.length+C.size from wrapSize ..]; simp [address,input]; omega
      exact (val_ge len od).trans (val_ge len oc).symm
theorem useCount {n : Nat} {C : Circuit} (good : IsAO2 n C) :
    (C.gates.flatMap Gate.inputs).length=2*C.size := by
  have count (L : List Gate) (leg : ∀g∈L,g.inputs.length=2) : (L.flatMap Gate.inputs).length=2*L.length := by
    induction L with
    | nil => simp
    | cons g L ih =>
      have a:=leg g (by simp)
      have b:=ih (fun k h => leg k (List.mem_cons_of_mem _ h))
      simp [a,b]; omega
  exact count _ good.2.2
theorem partition (L : List Nat) (tag : Nat → Bool) :
    (L.filter tag).length+(L.filter (fun w => !(tag w))).length=L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases h : tag a <;> simp [List.filter_cons,h] <;> omega
theorem normalized {n : Nat} {C : Circuit} (good : IsAO2 n C) (col : Nat → Bool) :
    ∃ D : Circuit,IsAO2 n D ∧ D.size≤2*C.size ∧ circuitFun n D=circuitFun n C ∧ tCount n D col=0 := by
  let L := C.gates.flatMap Gate.inputs
  let R := L.filter (fun w => decide (w<n))
  let U := R.dedup
  let A := U.filter col
  let B := U.filter (fun w => !(col w))
  have sum : A.length+B.length=U.length := partition U col
  have budget : U.length≤2*C.size := R.dedup_sublist.length_le.trans ((List.length_filter_le ..).trans (le_of_eq (useCount good)))
  have choose (S : List Nat) (keep : Bool) (card : S.length≤C.size) (raw : ∀w∈S,w<n)
      (pick : ∀g∈C.gates,∀w∈g.inputs,w<n → col w≠keep → w∈S) :
      ∃ D : Circuit,IsAO2 n D ∧ D.size≤2*C.size ∧ circuitFun n D=circuitFun n C ∧ tCount n D col=0 := by
    refine ⟨wrap n S C,model good raw,by rw [wrapSize]; omega,?_,noMix col keep pick⟩
    funext x; exact sim good raw _ List.length_ofFn C.output
  have rawU {w} (h : w∈U) : w<n := of_decide_eq_true (List.mem_filter.mp (List.mem_dedup.mp h)).2
  have belongs {g w} (hg : g∈C.gates) (hw : w∈g.inputs) (v : w<n) : w∈U :=
    List.mem_dedup.mpr (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨g,hg,hw⟩,decide_eq_true v⟩)
  by_cases cheap : A.length≤B.length
  · apply choose A false (by omega) (fun w h => rawU (List.mem_filter.mp h).1)
    intro g hg w hw h ne
    exact List.mem_filter.mpr ⟨belongs hg hw h,Bool.eq_true_of_not_eq_false ne⟩
  · apply choose B true (by omega) (fun w h => rawU (List.mem_filter.mp h).1)
    intro g hg w hw h ne
    exact List.mem_filter.mpr ⟨belongs hg hw h,by simp [Bool.eq_false_iff.mpr ne]⟩
end PEqualNP.Outside.L_meta_4791

theorem PEqualNP.Outside.L_meta_4791 : ∀ (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (p + l) C → 1 ≤ C.size → (∀ i : Fin (p + l), PEqualNP.MetaComplexity.circuitFun (p + l) C (fun k => decide (k = i)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size + 4 ≤ 6 * C.size ∧ PEqualNP.MetaComplexity.circuitFun (p + l) D = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧ PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  intro p l C good pos _
  obtain ⟨D,legal,sz,eq,col⟩ := PEqualNP.Outside.L_meta_4791.normalized good (fun i => decide (p ≤ i))
  exact ⟨D,legal,by omega,eq,col⟩
