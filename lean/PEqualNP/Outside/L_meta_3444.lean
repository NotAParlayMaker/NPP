import Mathlib
import PEqualNP.Defs

-- Fleet pull request 6956 exhibits a three-leaf star. The circuit below removes
-- one gate and works for every star. If F is the edge function and x1 a chosen
-- leaf, its output is F OR (F AND x1). Both branches feed the output.
-- The intersection accepts only the edge to x1, although all leaf inputs feed it.
-- With r leaves, the two sides of the proposed bound are 2r+1 and r+3.
namespace PEqualNP.Outside.L_meta_3444
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadK PEqualNP.ReadTwo

-- There are t+1 leaves, numbered 1 through t+1. The center is 0.
abbrev star (t : ℕ) := SimpleGraph.starGraph (0 : Fin (t+2))

theorem adjacent (t : ℕ) (u v : Fin (t+2)) :
    (star t).Adj u v ↔ (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0) := by
  rw [SimpleGraph.starGraph_adj]; grind

def front (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => n+k

def chain (n : ℕ) : ℕ → List Gate
  | 0 => []
  | k+1 => chain n k ++ [⟨.or,[front n k,k+2]⟩]

def circ (t : ℕ) : Circuit :=
  let n := t+2
  ⟨chain n t ++ [⟨.and,[0,front n t]⟩,⟨.and,[n+t,1]⟩,⟨.or,[n+t,n+t+1]⟩],n+t+2⟩

def cs (t : ℕ) := maximalCores (star t) (circ t)
def edgesD (t : ℕ) := (cs t).biUnion (gammaE (star t) (circ t))
def inside (t : ℕ) := (cs t).biUnion (coneSet (t+2) (circ t))
def counted (t : ℕ) := (inside t).filter fun w => w ∈ cs t ∨
  ((readers (t+2) (circ t) w).filter (fun k => InOutputCone (t+2) (circ t) k)) ⊆ inside t

def stat (t : ℕ) : Prop :=
  (∀ u v, (star t).Adj u v → decide (u=0) ≠ decide (v=0)) ∧
  NoFourCycle (star t) ∧ IsAO2 (t+2) (circ t) ∧
  (∀ x, circuitFun (t+2) (circ t) x = graphFun (star t) ∅ x) ∧
  IsLiftFixedPoint (star t) (circ t) ∧ (∀ k < (circ t).size, InOutputCone (t+2) (circ t) k) ∧
  cs t = {t+1} ∧ edgesD t = {s(0,1)} ∧
  IsMinCover ((star t).deleteEdges (edgesD t : Set _)) {0} ∧
  (counted t).card = t+1 ∧ ((star t).edgeFinset \ edgesD t).card = t ∧ (circ t).size = t+3

@[simp] theorem chain_len (n t : ℕ) : (chain n t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [chain,ih]

def stepList {α : Type} (v : Gate → List α → α) (gs : List Gate) (a : List α) :=
  gs.foldl (fun w g => w++[v g w]) a

theorem snoc {α : Type} (l : List α) (a d : α) : (l++[a]).getD l.length d = a := by simp

theorem stepAppend {α : Type} (v : Gate → List α → α) (p q : List Gate) (a : List α) :
    stepList v (p++q) a = stepList v q (stepList v p a) := List.foldl_append

theorem stepLen {α : Type} (v : Gate → List α → α) (gs : List Gate) (a : List α) :
    (stepList v gs a).length = a.length+gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => change (stepList v gs (a++[v g a])).length = _; rw [ih]; simp; omega

theorem untouched {α : Type} (d : α) (v : Gate → List α → α) (gs : List Gate) (a : List α)
    (j : ℕ) (h : j < a.length) : (stepList v gs a).getD j d = a.getD j d := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    change (stepList v gs (a++[v g a])).getD j d = _
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ h]

theorem frontLt (n k : ℕ) (h : 2≤n) : front n k < n+k := by
  cases k <;> simp [front] <;> omega

def acc {α : Type} (join : α → α → α) (z : ℕ → α) : ℕ → α
  | 0 => z 1
  | k+1 => join (acc join z k) (z (k+2))

theorem chainVal {α : Type} (d : α) (v : Gate → List α → α) (join : α → α → α)
    (orRule : ∀ i j w, v ⟨.or,[i,j]⟩ w = join (w.getD i d) (w.getD j d))
    (n k : ℕ) (w : List α) (sz : w.length=n) (hk : k+2≤n) :
    (stepList v (chain n k) w).getD (front n k) d = acc join (fun j => w.getD j d) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := ih (by omega)
    let pre := stepList v (chain n k) w
    have l : pre.length=n+k := by simp [pre,stepLen,sz]
    change (stepList v (chain n k ++ [⟨.or,[front n k,k+2]⟩]) w).getD (n+k) d = _
    rw [stepAppend]
    change (pre ++ [v ⟨.or,[front n k,k+2]⟩ pre]).getD (n+k) d = _
    rw [←l,snoc,orRule]
    exact congrArg₂ join h (untouched d v _ _ _ (by omega))

def bv (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun j => w.getD j false)
def bank (t : ℕ) (x : Fin (t+2) → Bool) := stepList bv (chain (t+2) t) (List.ofFn x)
def leaves (t : ℕ) (x : Fin (t+2) → Bool) := acc (· || ·) (fun i => (List.ofFn x).getD i false) t
def edgeValue (t : ℕ) (x : Fin (t+2) → Bool) := x 0 && leaves t x

theorem accBool (z : ℕ → Bool) (k : ℕ) :
    acc (· || ·) z k = true ↔ ∃ j, 1≤j ∧ j≤k+1 ∧ z j=true := by
  induction k with
  | zero =>
    constructor
    · intro h; exact ⟨1,by decide,by decide,h⟩
    · rintro ⟨j,a,b,c⟩
      have ej : j=1 := by omega
      simpa [acc,ej] using c
  | succ k ih =>
    simp only [acc,Bool.or_eq_true,ih]
    constructor
    · rintro (⟨j,a,b,c⟩|h)
      · exact ⟨j,a,by omega,c⟩
      · exact ⟨k+2,by omega,by omega,h⟩
    · rintro ⟨j,a,b,c⟩
      by_cases h : j≤k+1
      · exact Or.inl ⟨j,a,h,c⟩
      · have ej : j=k+2 := by omega
        exact Or.inr (ej ▸ c)

theorem leavesTrue (t : ℕ) (x : Fin (t+2) → Bool) :
    leaves t x = true ↔ ∃ j : Fin (t+2), j ≠ 0 ∧ x j = true := by
  rw [leaves,accBool]
  constructor
  · rintro ⟨j,a,b,c⟩
    refine ⟨⟨j,by omega⟩,fun h => by have := congrArg Fin.val h; simp at this; omega,?_⟩
    rwa [List.getD_eq_getElem _ _ (by simp; omega),List.getElem_ofFn] at c
  · rintro ⟨j,ne,h⟩
    have j0 : j.val ≠ 0 := by simpa using ne
    exact ⟨j.val,by omega,by have := j.isLt; omega,by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]; exact h⟩

theorem graphValue (t : ℕ) (x : Fin (t+2) → Bool) : graphFun (star t) ∅ x = edgeValue t x := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
    decide_eq_true_eq,edgeValue,Bool.and_eq_true,leavesTrue]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    rcases (adjacent _ _ _).mp hab with ⟨rfl,ne⟩|⟨rfl,ne⟩
    · exact ⟨ha,b,ne,hb⟩
    · exact ⟨hb,a,ne,ha⟩
  · rintro ⟨h,j,ne,hj⟩; exact ⟨0,j,(adjacent t _ _).mpr (Or.inl ⟨rfl,ne⟩),h,hj⟩

theorem circuitWires (t : ℕ) (x : Fin (t+2) → Bool) :
    (circ t).wires (List.ofFn x) = bank t x ++
      [edgeValue t x,edgeValue t x && x 1,edgeValue t x] := by
  let n := t+2
  let a := bank t x
  have len : a.length=n+t := by simp [a,bank,stepLen,n]
  have raw (j : Fin (t+2)) : a.getD j.val false = x j := by
    rw [show a=stepList bv (chain n t) (List.ofFn x) from rfl,untouched _ _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]
  have root : a.getD (front n t) false = leaves t x :=
    chainVal false bv (· || ·) (fun _ _ _ => by simp [bv,GateOp.eval]) n t (List.ofFn x) (by simp [n]) (by omega)
  let f := edgeValue t x
  have e0 : bv ⟨.and,[0,front n t]⟩ a = f := by
    have c := raw 0
    change a.getD 0 false = x 0 at c
    change (a.getD 0 false && (a.getD (front n t) false && true)) = _
    rw [c,root,Bool.and_true]; rfl
  have e1 : bv ⟨.and,[n+t,1]⟩ (a++[f]) = (f && x 1) := by
    have c := raw 1
    have hl : 1 < a.length := by rw [len]; dsimp [n]; omega
    change ((a++[f]).getD (n+t) false && ((a++[f]).getD 1 false && true)) = _
    rw [←len,snoc,List.getD_append _ _ _ _ hl,Bool.and_true]
    congr 1
  have e2 : bv ⟨.or,[n+t,n+t+1]⟩ (a++[f,f && x 1]) = f := by
    change (((a++[f,f && x 1]).getD (n+t) false) || ((a++[f,f && x 1]).getD (n+t+1) false || false)) = f
    rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),len]
    simp <;> tauto
  let g0 : Gate := ⟨.and,[0,front n t]⟩
  let g1 : Gate := ⟨.and,[n+t,1]⟩
  let g2 : Gate := ⟨.or,[n+t,n+t+1]⟩
  change stepList bv (chain n t ++ [g0,g1,g2]) (List.ofFn x) = a++[f,f && x 1,f]
  rw [stepAppend]
  change ((a++[bv g0 a]) ++ [bv g1 (a++[bv g0 a])]) ++
    [bv g2 ((a++[bv g0 a])++[bv g1 (a++[bv g0 a])])] = _
  change bv g0 a = f at e0
  change bv g1 (a++[f]) = (f && x 1) at e1
  change bv g2 (a++[f,f && x 1]) = f at e2
  rw [e0,e1]
  simp only [List.append_assoc,List.cons_append,List.nil_append,e2]

theorem computes (t : ℕ) : circuitFun (t+2) (circ t) = graphFun (star t) ∅ := by
  funext x
  change ((circ t).wires (List.ofFn x)).getD (t+2+t+2) false = _
  rw [circuitWires,graphValue,List.getD_append_right _ _ _ _ (by simp [bank,stepLen] <;> omega)]
  simp [bank,stepLen]

def rows (k : ℕ) := (List.range k).map fun j => (List.range j).reverse

theorem rowAt (k j : ℕ) (h : j<k) : (rows k).getD j [] = (List.range j).reverse := by
  rw [List.getD_eq_getElem _ _ (by simpa [rows] using h)]
  simp [rows]

theorem rowNext (k : ℕ) : rows (k+1) = rows k ++ [(List.range k).reverse] := by
  simp [rows,List.range_succ]

theorem coneAdd (n k u : ℕ) (en : 2≤n) (hu : u<n) (op : GateOp) :
    coneStep n (rows k) ⟨op,[front n k,u]⟩ = rows (k+1) ∧
    coneStep n (rows k) ⟨op,[u,front n k]⟩ = rows (k+1) := by
  rw [rowNext]
  have no : ¬ n≤u := by omega
  cases k with
  | zero => simp [coneStep,rows,front,no,show ¬n≤1 by omega]
  | succ k =>
    have len : (rows (k+1)).length = k+1 := by simp [rows]
    have lookup := rowAt (k+1) k (by omega)
    simp [coneStep,front,len,no,List.filter_cons,lookup,List.range_succ]
    simp [rows]

theorem coneChain (n k : ℕ) (hk : k+2≤n) :
    (chain n k).foldl (coneStep n) [] = rows k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [chain,List.foldl_append,ih (by omega)]
    exact (coneAdd n k (k+2) (by omega) (by omega) .or).1

theorem coneAll (t : ℕ) : cones (t+2) (circ t) = rows (t+2) ++
    [((t::(List.range t).reverse) ++ ((t+1)::(List.range (t+1)).reverse))] := by
  let n := t+2
  unfold cones
  change (chain n t ++ _).foldl (coneStep n) [] = _
  rw [List.foldl_append,coneChain n t (by omega)]
  change coneStep n (coneStep n (coneStep n (rows t) ⟨.and,[0,front n t]⟩)
    ⟨.and,[front n (t+1),1]⟩) ⟨.or,[n+t,n+t+1]⟩ = _
  rw [(coneAdd n t 0 (by omega) (by omega) .and).2,(coneAdd n (t+1) 1 (by omega) (by omega) .and).1]
  have len : (rows (t+2)).length=t+2 := by simp [rows]
  have lt0 : n+t < n+(t+2) := by omega
  have lt1 : n+t+1 < n+(t+2) := by omega
  have sub : n+t+1-n = t+1 := by omega
  simp [coneStep,len,List.filter_cons,lt0,lt1,sub,rowAt,show n≤n+t+1 by omega]
  simp [rows]

theorem ancestor (t i j : ℕ) (hj : j < t+3) : InCone (t+2) (circ t) i j ↔ i < j := by
  unfold InCone
  rw [coneAll]
  by_cases h : j<t+2
  · rw [List.getD_append _ _ _ _ (by simpa [rows] using h),rowAt _ _ h]
    simp
  · have eq : j=t+2 := by omega
    subst j
    rw [List.getD_append_right _ _ _ _ (by simp [rows])]
    simp [rows]
    omega

theorem live (t : ℕ) (k : ℕ) (hk : k < (circ t).size) : InOutputCone (t+2) (circ t) k := by
  have small : k<t+3 := by simpa [Circuit.size,circ] using hk
  refine ⟨hk,?_⟩
  change (t+2+t+2 = t+2+k) ∨ (t+2 ≤ t+2+t+2 ∧ InCone (t+2) (circ t) k (t+2+t+2-(t+2)))
  rw [show t+2+t+2-(t+2)=t+2 by omega,ancestor _ _ _ (by omega)]
  omega

theorem chainPrefix (n k t : ℕ) (h : k≤t) : ∃ q, chain n t = chain n k ++ q := by
  induction t with
  | zero => have e : k=0 := by omega
            exact ⟨[],by simp [e]⟩
  | succ t ih =>
    by_cases low : k≤t
    · obtain ⟨q,eq⟩ := ih low
      exact ⟨q++[_],by rw [chain,eq,List.append_assoc]⟩
    · have eq : k=t+1 := by omega
      exact ⟨[],by simp [eq]⟩

theorem gateEarly (t j : ℕ) (h : j<t) : gateAt (circ t) j = ⟨.or,[front (t+2) j,j+2]⟩ := by
  obtain ⟨q,e⟩ := chainPrefix (t+2) (j+1) t (by omega)
  change (chain (t+2) t ++ _).getD j _ = _
  rw [List.getD_append _ _ _ _ (by simpa using h),e,
    List.getD_append _ _ _ _ (by simp),chain, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem gateLate (t : ℕ) :
    gateAt (circ t) t = ⟨.and,[0,front (t+2) t]⟩ ∧
    gateAt (circ t) (t+1) = ⟨.and,[t+2+t,1]⟩ ∧
    gateAt (circ t) (t+2) = ⟨.or,[t+2+t,t+2+t+1]⟩ := by
  simp only [gateAt,circ,List.getD_append_right,chain_len,Nat.le_refl,
    Nat.le_add_right, Nat.add_sub_cancel_left,Nat.sub_self]
  exact ⟨rfl,rfl,rfl⟩

theorem rawWire (t : ℕ) (x : Fin (t+2) → Bool) (i : Fin (t+2)) :
    wval (circ t) x i.val = x i := by
  change (stepList bv (circ t).gates (List.ofFn x)).getD _ _ = _
  rw [untouched _ _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
    List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),List.getElem_ofFn]

theorem earlyWire (t k : ℕ) (hk : k≤t) (x : Fin (t+2) → Bool) :
    wval (circ t) x (front (t+2) k) = acc (· || ·) (fun i => (List.ofFn x).getD i false) k := by
  obtain ⟨q,eq⟩ := chainPrefix (t+2) k t hk
  change (stepList bv (chain (t+2) t ++ _) (List.ofFn x)).getD _ _ = _
  rw [eq,List.append_assoc,stepAppend,untouched _ _ _ _ _ (by
    rw [stepLen,List.length_ofFn,chain_len]; exact frontLt _ _ (by omega))]
  exact chainVal false bv (· || ·) (fun _ _ _ => by simp [bv,GateOp.eval]) _ _ _ (by simp) (by omega)

theorem lateValues (t : ℕ) (x : Fin (t+2) → Bool) :
    gateVal (t+2) (circ t) t x = edgeValue t x ∧
    gateVal (t+2) (circ t) (t+1) x = (edgeValue t x && x 1) ∧
    gateVal (t+2) (circ t) (t+2) x = edgeValue t x := by
  have len : (bank t x).length=t+2+t := by simp [bank,stepLen]
  simp only [gateVal,circuitWires]
  rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
  simp [len,show t+2+(t+1)-(t+2+t)=1 by omega,show t+2+(t+2)-(t+2+t)=2 by omega]

theorem readDuplicate (t : ℕ) : ReadTwiceAt (t+2) (circ t) (t+1) 0 1 := by
  let n := t+2
  let V := List (List ℕ)
  let merge (a b : V) := b.foldl insertNew (a.foldl insertNew [])
  let vec (g : Gate) (w : List V) :=
    let ins := g.inputs.map (fun j => w.getD j [])
    match g.op with
    | .or => ins.foldl (fun (acc A : V) => A.foldl insertNew acc) []
    | .and => ins.foldl (andStep 1) [[0,0]]
    | _ => []
  let z := (List.range n).map (leafVectors [0,1] 1)
  let pre := stepList vec (chain n t) z
  have lenz : z.length=n := by simp [z]
  have len : pre.length=n+t := by simp [pre,stepLen,lenz]
  have get (j : ℕ) (hj : j<n) : z.getD j [] = leafVectors [0,1] 1 j := by
    rw [List.getD_eq_getElem _ _ (lenz ▸ hj)]; simp [z]
  have raw (j : ℕ) (hj : j<n) : pre.getD j [] = leafVectors [0,1] 1 j :=
    (untouched _ _ _ _ _ (lenz ▸ hj)).trans (get j hj)
  have accV (k : ℕ) (hk : k+2≤n) : acc merge (fun j => z.getD j []) k = [[0,1]] := by
    induction k with
    | zero => rw [acc,get _ (by omega)]; rfl
    | succ k ih =>
      rw [acc,ih (by omega),get _ (by omega)]
      have no : k+2 ∉ ([0,1] : List ℕ) := by simp <;> omega
      simp only [leafVectors,if_neg no]; rfl
  have root : pre.getD (front n t) [] = [[0,1]] :=
    (chainVal [] vec merge (fun _ _ _ => rfl) n t z lenz (by omega)).trans (accV _ (by omega))
  have v0 : vec ⟨.and,[0,front n t]⟩ pre = [[1,1]] := by
    change (([pre.getD 0 [],pre.getD (front n t) []] : List V).foldl (andStep 1) [[0,0]]) = _
    rw [root,raw 0 (by omega)]; rfl
  have v1 : vec ⟨.and,[n+t,1]⟩ (pre++[[[1,1]]]) = [[1,2]] := by
    change (([(pre++[[[1,1]]]).getD (n+t) [],(pre++[[[1,1]]]).getD 1 []] : List V).foldl (andStep 1) [[0,0]]) = _
    rw [←len,snoc,List.getD_append _ _ _ _ (by omega),raw 1 (by omega)]; rfl
  let g0 : Gate := ⟨.and,[0,front n t]⟩
  let g1 : Gate := ⟨.and,[n+t,1]⟩
  let g2 : Gate := ⟨.or,[n+t,n+t+1]⟩
  change ((stepList vec (chain n t ++ [g0,g1,g2]) z).getD (n+(t+1)) []).any _ = false
  rw [stepAppend]
  change ((((pre++[vec g0 pre])++[vec g1 (pre++[vec g0 pre])])++[_]).getD (n+(t+1)) []).any _ = false
  change vec g0 pre = _ at v0
  change vec g1 (pre++[[[1,1]]]) = _ at v1
  rw [v0,v1,List.getD_append _ _ _ _ (by simp [len]; omega)]
  rw [List.getD_append_right _ _ _ _ (by simp [len] <;> omega)]
  simp [len,show n+(t+1)-(n+t+1)=0 by omega]

theorem sizeG (t : ℕ) : (circ t).gates.length=t+3 := by simp [circ]

theorem ne01 (t : ℕ) : (0 : Fin (t+2)) ≠ 1 := by
  intro h; have hh := congrArg Fin.val h; simpa using hh

theorem firstOn (t : ℕ) (x : Fin (t+2) → Bool) (c : x 0=true) (l : x 1=true) :
    edgeValue t x=true := by
  rw [edgeValue,c, Bool.true_and,leavesTrue]; exact ⟨1,(ne01 t).symm,l⟩

theorem implicants (t : ℕ) :
    IsImpGate (star t) (circ t) t ∧ IsImpGate (star t) (circ t) (t+1) := by
  have f := firstOn t (fun _ => true) rfl rfl
  constructor
  · exact ⟨fun x hx => by rwa [graphValue,←(lateValues t x).1],fun _ => true,
      (lateValues t _).1.trans f⟩
  · refine ⟨?_,fun _ => true,?_⟩
    · intro x hx
      rw [(lateValues t x).2.1,Bool.and_eq_true] at hx
      rwa [graphValue,hx.1]
    · rw [(lateValues t _).2.1,f]; rfl

theorem coreB (t : ℕ) : IsCore (star t) (circ t) (t+1) := by
  refine ⟨by rw [sizeG]; omega,(implicants t).2,?_,0,1,(adjacent t _ _).mpr (Or.inl ⟨rfl,(ne01 t).symm⟩),?_,readDuplicate t⟩
  · rintro ⟨_,b⟩
    have hb := b.1
    rw [opnd,(gateLate t).2.1] at hb
    change t+2 ≤ 1 at hb
    omega
  · rw [(lateValues t _).2.1,firstOn t _ (by simp [pairInput]) (by simp [pairInput])]
    simp [pairInput]

theorem outNotCore (t : ℕ) : ¬ IsCore (star t) (circ t) (t+2) := by
  intro h
  apply h.2.2.1
  simp only [opnd,(gateLate t).2.2]
  change IsImpOperand (star t) (circ t) (t+2+t) ∧ IsImpOperand (star t) (circ t) (t+2+t+1)
  constructor
  · exact ⟨by omega,by simpa using (implicants t).1⟩
  · exact ⟨by omega,by rw [show t+2+t+1-(t+2)=t+1 by omega]; exact (implicants t).2⟩

theorem coresEq (t : ℕ) : cs t = {t+1} := by
  ext j
  simp only [cs,maximalCores,gatesWhere,Finset.mem_filter,Finset.mem_range,sizeG,Finset.mem_singleton]
  constructor
  · rintro ⟨hj,c,m⟩
    have no : j≠t+2 := fun e => outNotCore t (e ▸ c)
    have outside := m (t+1) (by rw [sizeG]; omega) (coreB t)
    rw [ancestor _ _ _ (by omega)] at outside
    omega
  · rintro rfl
    refine ⟨by omega,coreB t,?_⟩
    intro i hi core
    rw [sizeG] at hi
    have ne : i ≠ t+2 := fun e => outNotCore t (e ▸ core)
    rw [ancestor _ _ _ hi]; omega

theorem dEq (t : ℕ) : edgesD t = {s(0,1)} := by
  rw [edgesD,coresEq,Finset.singleton_biUnion]
  ext e
  simp only [gammaE,Finset.mem_filter,Finset.mem_singleton]
  constructor
  · rintro ⟨ge,u,v,rfl,h⟩
    rw [(lateValues t _).2.1,Bool.and_eq_true] at h
    have adj := SimpleGraph.mem_edgeFinset.mp ge
    rw [SimpleGraph.mem_edgeSet,adjacent] at adj
    have one : (1 : Fin (t+2))=u ∨ 1=v := of_decide_eq_true h.2
    rcases adj with ⟨rfl,hn⟩|⟨rfl,hn⟩ <;> rcases one with h|h
    · exact ((ne01 t).symm h).elim
    · rw [←h]
    · rw [←h,Sym2.eq_swap]
    · exact ((ne01 t).symm h).elim
  · rintro rfl
    refine ⟨SimpleGraph.mem_edgeFinset.mpr ((adjacent t _ _).mpr (Or.inl ⟨rfl,(ne01 t).symm⟩)),0,1,rfl,?_⟩
    rw [(lateValues t _).2.1,firstOn t _ (by simp [pairInput]) (by simp [pairInput])]
    simp [pairInput]

theorem insideEq (t : ℕ) : inside t = Finset.range (t+2) := by
  rw [inside,coresEq,Finset.singleton_biUnion]
  ext w
  simp only [coneSet,Finset.mem_insert,Finset.mem_filter,Finset.mem_range,sizeG,ancestor t w (t+1) (by omega)]
  omega

theorem countedEq (t : ℕ) : counted t = (Finset.range (t+2)).erase t := by
  have reads (w : ℕ) : t+2 ∈ readers (t+2) (circ t) w ↔ w=t ∨ w=t+1 := by
    rw [readers,Finset.mem_filter,Finset.mem_range,sizeG,(gateLate t).2.2]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    omega
  ext w
  simp only [counted,insideEq,coresEq,Finset.mem_filter,Finset.mem_range,Finset.mem_singleton,Finset.mem_erase]
  constructor
  · rintro ⟨lo, root|internal⟩
    · exact ⟨by omega,lo⟩
    · refine ⟨?_,lo⟩
      rintro rfl
      have mem := (reads w).mpr (Or.inl rfl)
      have := internal (Finset.mem_filter.mpr ⟨mem,live w _ (by change _ < (circ w).gates.length; rw [sizeG]; omega)⟩)
      simpa using this
  · rintro ⟨ne,lo⟩
    refine ⟨lo,?_⟩
    by_cases root : w=t+1
    · exact Or.inl root
    · right
      intro j hj
      have hm := (Finset.mem_filter.mp hj).1
      have js := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
      rw [sizeG] at js
      apply Finset.mem_range.mpr
      by_contra! far
      have eq : j=t+2 := by omega
      have wrong := (reads w).mp (eq ▸ hm)
      tauto

theorem countedCard (t : ℕ) : (counted t).card = t+1 := by
  rw [countedEq,Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),Finset.card_range]
  omega

theorem edgeSet (t : ℕ) : (star t).edgeFinset =
    (Finset.univ.erase 0).map (Sym2.mkEmbedding (0 : Fin (t+2))) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,adjacent,Finset.mem_map]
    constructor
    · rintro (⟨rfl,ne⟩|⟨rfl,ne⟩)
      · exact ⟨b,by simpa using ne,rfl⟩
      · exact ⟨a,by simpa using ne,Sym2.eq_swap⟩
    · rintro ⟨v,hv,h⟩
      have nv : v≠0 := by simpa using hv
      change s(0,v) = s(a,b) at h
      rcases (Sym2.mk_eq_mk_iff (p := (0,v)) (q := (a,b))).mp h with eq|eq <;> have aeq := congrArg Prod.fst eq <;>
        have beq := congrArg Prod.snd eq <;> simp at aeq beq <;> subst_vars <;> simp [star,nv]

theorem remaining (t : ℕ) : ((star t).edgeFinset \ edgesD t).card = t := by
  have total : (star t).edgeFinset.card = t+1 := by
    rw [edgeSet,Finset.card_map,Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have mem : s(0,1) ∈ (star t).edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr ((adjacent t _ _).mpr (Or.inl ⟨rfl,(ne01 t).symm⟩))
  rw [dEq,Finset.sdiff_singleton_eq_erase,Finset.card_erase_of_mem mem,total]; simp

theorem minCover (t : ℕ) (ht : 1≤t) : IsMinCover ((star t).deleteEdges (edgesD t : Set _)) {0} := by
  rw [dEq]
  let z : Fin (t+2) := ⟨2,by omega⟩
  have z0 : z ≠ 0 := by intro e; have := congrArg Fin.val e; simp [z] at this
  have z1 : z ≠ 1 := by intro e; have := congrArg Fin.val e; simp [z] at this
  have e : ((star t).deleteEdges (({s(0,1)} : Finset (Sym2 (Fin (t+2)))) : Set _)).Adj 0 z := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨(adjacent t _ _).mpr (Or.inl ⟨rfl,z0⟩),?_⟩
    change s(0,z) ∉ ({s(0,1)} : Finset (Sym2 (Fin (t+2))))
    intro h
    exact z1 ((Sym2.mkEmbedding (0 : Fin (t+2))).injective (Finset.mem_singleton.mp h))
  constructor
  · intro a b h
    rcases (adjacent t _ _).mp (SimpleGraph.deleteEdges_adj.mp h).1 with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
  · intro T h
    have nonempty : T.Nonempty := by
      rcases h e with ha|ha <;> exact ⟨_,ha⟩
    simpa using Finset.card_pos.mpr nonempty

theorem shore (t : ℕ) (u v : Fin (t+2)) (h : (star t).Adj u v) : decide (u=0) ≠ decide (v=0) := by
  rcases (adjacent t _ _).mp h with ⟨rfl,other⟩|⟨rfl,other⟩ <;> simp [other]

theorem squareFree (t : ℕ) : NoFourCycle (star t) := by
  intro a b ne
  have sub : (Finset.univ.filter fun w => (star t).Adj a w ∧ (star t).Adj b w) ⊆ {0} := by
    intro w hw; obtain ⟨ha,hb⟩ := (Finset.mem_filter.mp hw).2
    rcases (adjacent t _ _).mp ha with ⟨rfl,hn⟩|⟨rfl,_⟩
    · rcases (adjacent t _ _).mp hb with ⟨rfl,_⟩|⟨eq,_⟩
      · exact (ne rfl).elim
      · exact (hn eq).elim
    · simp
  simpa using Finset.card_le_card sub

theorem proper (t : ℕ) : IsAO2 (t+2) (circ t) := by
  have shape (j : ℕ) (h : j < (circ t).gates.length) :
      let g := gateAt (circ t) j
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ ∀ i ∈ g.inputs, i<t+2+j := by
    rw [sizeG] at h
    by_cases early : j<t
    · simp [gateEarly _ _ early,frontLt,show j+2<t+2+j by omega]
    · obtain rfl|rfl|rfl : j=t ∨ j=t+1 ∨ j=t+2 := by omega
      · simp [(gateLate _).1,frontLt]
      · simp [(gateLate _).2.1] <;> omega
      · simp [(gateLate _).2.2] <;> omega
  have located (g : Gate) (hg : g ∈ (circ t).gates) : ∃ j < (circ t).gates.length, gateAt (circ t) j = g := by
    obtain ⟨j,hj,e⟩ := List.getElem_of_mem hg
    exact ⟨j,hj,by rw [gateAt,List.getD_eq_getElem _ _ hj,e]⟩
  refine ⟨?_,fun j hj => (shape j hj).2.2,?_⟩
  · intro g hg; obtain ⟨j,hj,rfl⟩ := located g hg; exact (shape j hj).1
  · intro g hg; obtain ⟨j,hj,rfl⟩ := located g hg; exact (shape j hj).2.1

theorem fixed (t : ℕ) : IsLiftFixedPoint (star t) (circ t) := by
  let off (j : Fin (t+2)) := decide (j≠0)
  have offF : graphFun (star t) ∅ off = false := by simp [graphValue,edgeValue,off]
  have leafOn (j : ℕ) (lo : 0<j) (hi : j<t+2) : wval (circ t) off j = true := by
    have ne : (⟨j,hi⟩ : Fin (t+2)) ≠ 0 := by intro h; have e:=congrArg Fin.val h; simp at e; omega
    exact (rawWire t off ⟨j,hi⟩).trans (by simp [off,ne])
  have frontOn (j : ℕ) (hj : j ≤ t) : wval (circ t) off (front (t+2) j) = true := by
    rw [earlyWire _ _ hj,accBool]
    refine ⟨1,by omega,by omega,?_⟩
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega),List.getElem_ofFn]
    simp [off]
  rintro ⟨j,hj,b,_,op,no,imp⟩
  rw [sizeG] at hj
  by_cases early : j<t
  · have on : wval (circ t) off (opnd (circ t) j b) = true := by
      rw [opnd,gateEarly _ _ early]
      fin_cases b
      · exact frontOn j (by omega)
      · exact leafOn (j+2) (by omega) (by omega)
    have bad := imp.1 off on
    rw [offF] at bad; contradiction
  · obtain rfl|rfl|rfl : j=t ∨ j=t+1 ∨ j=t+2 := by omega
    · simp [(gateLate _).1] at op
    · simp [(gateLate _).2.1] at op
    · apply no
      intro x hx; rwa [graphValue,←(lateValues t x).2.2]

theorem family (t : ℕ) (ht : 1≤t) : stat t :=
  ⟨shore t,squareFree t,proper t,fun x => congrFun (computes t) x,fixed t,live t,
    coresEq t,dEq t,minCover t ht,countedCard t,remaining t,sizeG t⟩

-- Taking t = d + 1 makes the left side exactly d greater than gates plus one.
theorem arbitraryGap (d : ℕ) :
    let t := d+1
    stat t ∧ (counted t).card + ((star t).edgeFinset \ edgesD t).card +
      ({0} : Finset (Fin (t+2))).card + (cs t).card = (circ t).size + 1 + d := by
  dsimp only
  refine ⟨family _ (by omega),?_⟩
  rw [countedCard,remaining,coresEq,Finset.card_singleton,Finset.card_singleton]
  change _ = (circ (d+1)).gates.length+1+d
  rw [sizeG]
  omega

theorem refutes : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro claimed
  obtain ⟨hs,gap⟩ := arbitraryGap 1
  obtain ⟨shore,sq,ao,ev,noLift,live,_,_,cover,_⟩ := hs
  have bound := @claimed 4 (star 2) inferInstance (circ 2) (fun j => decide (j=0))
    {0} shore sq ao (funext ev) noLift live cover
  change (counted 2).card + ((star 2).edgeFinset \ edgesD 2).card +
    ({0} : Finset (Fin 4)).card + (cs 2).card ≤ (circ 2).size+1 at bound
  change (counted 2).card + ((star 2).edgeFinset \ edgesD 2).card +
    ({0} : Finset (Fin 4)).card + (cs 2).card = (circ 2).size+1+1 at gap
  omega

end PEqualNP.Outside.L_meta_3444

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) :=
  PEqualNP.Outside.L_meta_3444.refutes

