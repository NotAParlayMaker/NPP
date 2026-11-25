import Mathlib
import PEqualNP.Defs

-- Tape evaluation lemmas adapted from steveDOTdigital, L-meta-8981 (PR #13180).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_9023

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires xs

theorem run_append (a b : List Gate) (xs : List Bool) :
    run (a ++ b) xs = run b (run a xs) := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    change (run gs (xs ++ [_])).length = _
    rw [ih]
    simp
    omega

theorem keep (gs : List Gate) (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    (run gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (xs ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

-- run, run_append, run_length and keep adapt steveDOTdigital's L-meta-8981 (PR #13180).
variable {α β : Type} [DecidableEq β]
def legal (gs : List Gate) := Monotone2 (⟨gs,0⟩ : Circuit)
theorem legalAppend {P Q : List Gate} (hp : legal P) (hq : legal Q) : legal (P++Q) := by
  intro g hg
  exact (List.mem_append.mp hg).elim (hp g) (hq g)

theorem bins (base : Nat) (raw : α → Nat) (key : α → β) (seed : β → Nat)
    (hr : ∀ j, raw j < base) (hs : ∀ c, seed c < base) (items : List α) :
    ∃ gs : List Gate, ∃ p : β → Nat, legal gs ∧ gs.length = items.length ∧
    (∀ c, p c < base+gs.length) ∧ ∀ xs : List Bool, xs.length=base → ∀ c,
    (run gs xs).getD (p c) false = true ↔ xs.getD (seed c) false = true ∨
      ∃ j ∈ items, key j = c ∧ xs.getD (raw j) false = true := by
  induction items using List.reverseRecOn with
  | nil =>
    exact ⟨[],seed,(by intro g hg; cases hg),rfl,by simpa,by simp [run,Circuit.wires]⟩
  | append_singleton items j ih =>
    obtain ⟨gs,p,hm,hl,hp,he⟩ := ih
    let g : Gate := ⟨.or,[p (key j),raw j]⟩
    let out (c : β) := if key j = c then base+gs.length else p c
    refine ⟨gs++[g],out,legalAppend hm (by intro t ht; obtain rfl := List.mem_singleton.mp ht; simp [g]),
      by simp [hl],?_,?_⟩
    · intro c; have := hp c; dsimp [out]; split <;> simp <;> omega
    · intro xs hx c
      have len : (run gs xs).length = base+gs.length := by rw [run_length,hx]
      have old := keep gs xs (raw j) (by rw [hx]; exact hr j)
      have last : (run (gs++[g]) xs).getD (base+gs.length) false =
          ((run gs xs).getD (p (key j)) false || xs.getD (raw j) false) := by
        rw [run_append,←len]
        simp [run,Circuit.wires,g,GateOp.eval,List.getD_eq_getElem?_getD] at old ⊢
        exact old ▸ rfl
      by_cases eq : key j = c
      · subst c; simp only [out,if_pos rfl,last,Bool.or_eq_true,he xs hx]
        simp only [List.mem_append,List.mem_singleton]
        aesop
      · have bound : p c < (run gs xs).length := by rw [len]; exact hp c
        simp only [out,if_neg eq,run_append,keep [g] _ _ bound,he xs hx,
          List.mem_append,List.mem_singleton]
        aesop

theorem classify {m : Nat} (base : Nat) (raw : Fin m → Nat) (key : Fin m → β)
    (hr : ∀ j, raw j < base) (onto : Function.Surjective key) :
    ∃ gs : List Gate, ∃ p : β → Nat, legal gs ∧ gs.length = m ∧
      (∀ c, p c < base+gs.length) ∧ ∀ xs : List Bool, xs.length=base → ∀ v : Fin m,
      (∀ j, xs.getD (raw j) false = decide (j=v)) →
      ∀ c, (run gs xs).getD (p c) false = decide (key v=c) := by
  classical
  let pick (c : β) := (onto c).choose
  obtain ⟨gs,p,h,l,b,e⟩ := bins base raw key (fun c => raw (pick c)) hr (fun c => hr _) (List.finRange m)
  refine ⟨gs,p,h,by simpa using l,b,?_⟩
  intro xs hx v hv c
  apply Bool.eq_iff_iff.mpr
  rw [e xs hx]
  simp only [hv,decide_eq_true_eq,List.mem_finRange,true_and]
  have pk : key (pick c) = c := (onto c).choose_spec
  aesop
end PEqualNP.Outside.L_meta_9023

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_9023

theorem encode {m : Nat} (n base : Nat) (raw : Fin m → Nat) (hr : ∀ j, raw j<base)
    (key : Nat → Fin m → Bool) (onto : ∀ i<n, Function.Surjective (key i)) :
    ∃ gs : List Gate, ∃ port : Nat → Bool → Nat, legal gs ∧ gs.length=n*m ∧
      (∀ i<n, ∀ b, port i b < base+gs.length) ∧ ∀ xs : List Bool, xs.length=base → ∀ v : Fin m,
      (∀ j, xs.getD (raw j) false = decide (j=v)) →
      ∀ i<n, ∀ b, (run gs xs).getD (port i b) false = decide (key i v=b) := by
  induction n with
  | zero => exact ⟨[],fun _ _ => 0,(by intro g hg; cases hg),by simp,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨P,p,hp,lp,bp,ep⟩ := ih (fun i hi => onto i (by omega))
    obtain ⟨Q,q,hq,lq,bq,eq⟩ := classify (base+P.length) raw (key n)
      (fun j => (hr j).trans_le (Nat.le_add_right ..)) (onto n (by omega))
    refine ⟨P++Q,fun i b => if i=n then q b else p i b,legalAppend hp hq,by simp [lp,lq,Nat.succ_mul],?_,?_⟩
    · intro i hi b
      by_cases e : i=n
      · simpa [e,Nat.add_assoc] using bq b
      · have := bp i (by omega) b; simp [e]; omega
    · intro xs hx v hv i hi b
      have len : (run P xs).length=base+P.length := by rw [run_length,hx]
      rw [run_append]
      by_cases e : i=n
      · subst i
        simp only [ite_true]
        apply eq _ len v _ b
        intro j; rw [keep P xs _ (hx ▸ hr j),hv]
      · have hin : i<n := by omega
        simp only [if_neg e]
        rw [keep Q _ _ (len ▸ bp i hin b),ep xs hx v hv i hin b]

theorem bitsOnto (d i : Nat) (hi : i<d) :
    Function.Surjective (fun v : Fin (2^d) => v.val.testBit i) := by
  intro b
  cases b with
  | false => exact ⟨⟨0,by positivity⟩,by simp⟩
  | true => exact ⟨⟨2^i,Nat.pow_lt_pow_right (by decide) hi⟩,by simp⟩

theorem chunk {k d : Nat} (base : Nat) (raw : Fin (2^k) → Nat) (hr : ∀ j, raw j < base)
    (key : Fin (2^k) → Fin (2^d)) (onto : Function.Surjective key) :
    ∃ gs : List Gate, ∃ p : Nat → Bool → Nat, legal gs ∧ gs.length = 2^k+d*2^d ∧
      (∀ i<d, ∀ b, p i b < base+gs.length) ∧ ∀ xs : List Bool, xs.length=base → ∀ v : Fin (2^k),
      (∀ j, xs.getD (raw j) false = decide (j=v)) → ∀ i<d, ∀ b,
      (run gs xs).getD (p i b) false = decide ((key v).val.testBit i=b) := by
  obtain ⟨P,p,hp,lp,bp,ep⟩ := classify base raw key hr onto
  obtain ⟨Q,q,hq,lq,bq,eq⟩ := encode d (base+P.length) p bp
    (fun i a => a.val.testBit i) (bitsOnto d)
  exact ⟨P++Q,q,legalAppend hp hq,by simp [lp,lq],by simpa [Nat.add_assoc] using bq,
    fun xs hx v hv i hi b => by
      rw [run_append]
      apply eq _ (by rw [run_length,hx]) (key v) _ i hi b
      intro j
      rw [ep xs hx v hv]
      simp [eq_comm]⟩
end PEqualNP.Outside.L_meta_9023

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_9023

def budget (k : Nat) := 2*2^k+k*2^((k+1)/2)

theorem literalSide (k base : Nat) (raw : Fin (2^k) → Nat) (hr : ∀ i, raw i < base) :
    ∃ gs : List Gate, ∃ p : Fin k → Bool → Nat, legal gs ∧ gs.length ≤ budget k ∧
      (∀ i b, p i b < base+gs.length) ∧ ∀ xs : List Bool, xs.length=base → ∀ v : Fin (2^k),
      (∀ j, xs.getD (raw j) false = decide (j=v)) → ∀ i b,
      (run gs xs).getD (p i b) false = decide (v.val.testBit i=b) := by
  let h := (k+1)/2
  let l := k/2
  have sum : h+l=k := by dsimp [h,l]; omega
  have smaller : l≤h := by dsimp [h,l]; omega
  have powers : 2^h*2^l = 2^k := by rw [←pow_add,sum]
  have pos : 0 < 2^l := by positivity
  have ple : (2:Nat)^l ≤ 2^h := Nat.pow_le_pow_right (by decide) smaller
  have pk : (2:Nat)^l ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
  let low (v : Fin (2^k)) : Fin (2^l) := ⟨v.val%2^l,Nat.mod_lt _ pos⟩
  let high (v : Fin (2^k)) : Fin (2^h) := ⟨v.val/2^l, (Nat.div_lt_iff_lt_mul pos).mpr (by rw [powers]; exact v.isLt)⟩
  have ontoL : Function.Surjective low := by
    intro v
    exact ⟨⟨v.val,v.isLt.trans_le pk⟩,Fin.ext (Nat.mod_eq_of_lt v.isLt)⟩
  have ontoH : Function.Surjective high := by
    intro v
    exact ⟨⟨v.val*2^l,by rw [←powers]; exact Nat.mul_lt_mul_of_pos_right v.isLt pos⟩,
      Fin.ext (Nat.mul_div_cancel _ pos)⟩
  obtain ⟨P,p,hp,lp,bp,ep⟩ := chunk base raw hr low ontoL
  obtain ⟨Q,q,hq,lq,bq,eq⟩ := chunk (base+P.length) raw (fun i => (hr i).trans_le (Nat.le_add_right ..)) high ontoH
  let out (i : Fin k) (b : Bool) := if i.val<l then p i b else q (i.val-l) b
  refine ⟨P++Q,out,legalAppend hp hq,?_,?_,?_⟩
  · have add : l*2^l + h*2^h ≤ k*2^h := by
      calc
        _ ≤ l*2^h+h*2^h := Nat.add_le_add_right (Nat.mul_le_mul_left _ ple) _
        _ = _ := by rw [←Nat.add_mul]; congr 1; omega
    change _ ≤ 2*2^k + k*2^h
    simp only [List.length_append,lp,lq]
    omega
  · intro i b
    dsimp [out]
    split
    next e => have := bp i e b; simp; omega
    next e => simpa [Nat.add_assoc] using bq (i.val-l) (by have := i.isLt; omega) b
  · intro xs hx v hot i b
    have len : (run P xs).length=base+P.length := by rw [run_length,hx]
    rw [run_append]
    dsimp [out]
    split
    next e =>
      rw [keep Q _ _ (len ▸ bp i e b),ep xs hx v hot i e b]
      simp [low,e]
    next e =>
      rw [eq _ len v (fun j => (keep P xs (raw j) (hx ▸ hr j)).trans (hot j)) _ (by have := i.isLt; omega)]
      simp only [high,Nat.testBit_div_two_pow]
      rw [Nat.sub_add_cancel (by omega)]
end PEqualNP.Outside.L_meta_9023

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_9023
-- Input substitution, following the suffix simulation of nicohabets in L-meta-8982.
def wire (n base : Nat) (p : Fin n → Nat) (i : Nat) : Nat :=
  if h : i<n then p ⟨i,h⟩ else base+(i-n)
def rewire (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩

theorem appendRead {n base : Nat} {p : Fin n → Nat} {x y : List Bool}
    (hx : x.length=n) (hy : y.length=base) (bound : ∀ i, p i < base)
    (agree : ∀ i : Fin n, y.getD (p i) false = x.getD i false) (tail : List Bool) (i : Nat) :
    (y++tail).getD (wire n base p i) false = (x++tail).getD i false := by
  by_cases h : i<n
  · simp only [wire,dif_pos h]
    rw [List.getD_append _ _ _ _ (hy ▸ bound ⟨i,h⟩),List.getD_append _ _ _ _ (by omega)]
    exact agree ⟨i,h⟩
  · simp only [wire,dif_neg h]
    rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

theorem runCons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g::gs) w = run gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem replay {n base : Nat} {p : Fin n → Nat} {x y : List Bool}
    (hx : x.length=n) (hy : y.length=base) (bound : ∀ i, p i < base)
    (agree : ∀ i : Fin n, y.getD (p i) false = x.getD i false) (gs : List Gate) (tail : List Bool) :
    ∃ t : List Bool, run gs (x++tail) = x++t ∧
      run (gs.map (rewire (wire n base p))) (y++tail) = y++t := by
  induction gs generalizing tail with
  | nil => exact ⟨_,rfl,rfl⟩
  | cons g gs ih =>
    rw [List.map_cons,runCons,runCons]
    have ports : ((g.inputs.map (wire n base p)).map fun i => (y++tail).getD i false) =
        g.inputs.map fun i => (x++tail).getD i false := by
      rw [List.map_map]; exact List.map_congr_left (fun i _ => appendRead hx hy bound agree tail i)
    simp only [rewire,ports,List.append_assoc]
    apply ih

theorem replayOut {n base : Nat} {p : Fin n → Nat} {x y : List Bool}
    (hx : x.length=n) (hy : y.length=base) (bound : ∀ i, p i < base)
    (agree : ∀ i : Fin n, y.getD (p i) false = x.getD i false) (C : Circuit) :
    (run (C.gates.map (rewire (wire n base p))) y).getD (wire n base p C.output) false = C.eval x := by
  obtain ⟨t,a,b⟩ := replay hx hy bound agree C.gates []
  simp only [List.append_nil] at a b
  change _ = (run C.gates x).getD C.output false
  rw [a,b,appendRead hx hy bound agree]

theorem legalMap (C : Circuit) (hc : Monotone2 C) (f : Nat → Nat) : legal (C.gates.map (rewire f)) := by
  intro g hg
  obtain ⟨g,hmem,rfl⟩ := List.mem_map.mp hg
  simpa [rewire] using hc g hmem
end PEqualNP.Outside.L_meta_9023

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace PEqualNP.Outside.L_meta_9023
-- The table-index digit lemmas are from the project's Library/Helpers/RRSeeded.
theorem tableIndex_succ {m : ℕ} (x : Fin (m + 1) → Bool) :
    PEqualNP.MetaComplexity.tableIndex x
      = (if x 0 = true then 1 else 0) + 2 * PEqualNP.MetaComplexity.tableIndex (Fin.tail x) := by
  unfold PEqualNP.MetaComplexity.tableIndex
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  have h2 : (∑ i : Fin m, if x i.succ = true then 2 ^ ((i.succ : Fin (m + 1)) : ℕ) else 0)
      = ∑ i : Fin m, 2 * (if Fin.tail x i = true then 2 ^ (i : ℕ) else 0) :=
    Finset.sum_congr rfl (fun i _ => by
      by_cases hx : x i.succ = true <;> simp [hx, Fin.tail, pow_succ, mul_comm])
  rw [h2]
  simp

theorem testBit_tableIndex : ∀ (m : ℕ) (x : Fin m → Bool) (j : ℕ),
    (PEqualNP.MetaComplexity.tableIndex x).testBit j = if h : j < m then x ⟨j, h⟩ else false := by
  intro m
  induction m with
  | zero =>
    intro x j
    simp [PEqualNP.MetaComplexity.tableIndex]
  | succ m ih =>
    intro x j
    rw [tableIndex_succ]
    cases j with
    | zero =>
      rw [dif_pos (by omega)]
      show _ = x 0
      cases hx : x 0 <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ j =>
      rw [Nat.testBit_succ]
      have e : ((if x 0 = true then 1 else 0) + 2 * PEqualNP.MetaComplexity.tableIndex (Fin.tail x)) / 2
          = PEqualNP.MetaComplexity.tableIndex (Fin.tail x) := by
        split_ifs <;> omega
      rw [e, ih]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (by omega)]; rfl
      · rw [dif_neg hj, dif_neg (by omega)]

theorem index_of_bits {d : Nat} (v : Fin (2^d)) :
    tableIndex (fun i : Fin d => v.val.testBit i) = v.val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_tableIndex]
  split
  next => rfl
  next h => exact (Nat.testBit_lt_two_pow (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm

def bits {k l : Nat} (u : Fin (2^k)) (v : Fin (2^l)) : Fin (k+l) → Bool :=
  Fin.addCases (fun i => u.val.testBit i) (fun i => v.val.testBit i)

theorem adjBits {k l : Nat} (A : Fin (2^k) → Fin (2^l) → Bool) (u v) :
    adjFun A (bits u v) = A u v := by
  simp [adjFun,bits,index_of_bits]

theorem network (k l : Nat) :
    ∃ G : List Gate, ∃ p : Fin (k+l) → Bool → Nat, legal G ∧ G.length ≤ budget k + budget l ∧
      (∀ i b, p i b < 2^k+2^l+G.length) ∧ ∀ (u : Fin (2^k)) (v : Fin (2^l)) i b,
        (run G (oneEach u v)).getD (p i b) false = decide (bits u v i=b) := by
  let n := 2^k+2^l
  obtain ⟨P,a,hp,lp,bp,ep⟩ := literalSide k n Fin.val (fun i => i.isLt.trans_le (Nat.le_add_right ..))
  obtain ⟨Q,b,hq,lq,bq,eq⟩ := literalSide l (n+P.length) (fun j => 2^k+j.val) (by intro j; have := j.isLt; dsimp [n]; omega)
  let p : Fin (k+l) → Bool → Nat := Fin.addCases a b
  refine ⟨P++Q,p,legalAppend hp hq,by simpa using Nat.add_le_add lp lq,?_,?_⟩
  · intro i c
    induction i using Fin.addCases with
    | left i => have := bp i c; simpa [p,n,Nat.add_assoc] using (this.trans_le (Nat.le_add_right _ Q.length))
    | right i => simpa [p,n,Nat.add_assoc] using bq i c
  · intro u v i c
    have len : (oneEach u v).length=n := by simp [oneEach,n]
    have lenP : (run P (oneEach u v)).length = n+P.length := by rw [run_length,len]
    rw [run_append]
    induction i using Fin.addCases with
    | left i =>
      simp only [p,bits,Fin.addCases_left]
      rw [keep Q _ _ (lenP ▸ bp i c)]
      apply ep _ len u _ i c
      intro j
      simp [oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using j.isLt : j.val < (List.ofFn (fun t : Fin (2^k) => decide (t=u))).length)]
    | right i =>
      simp only [p,bits,Fin.addCases_right]
      apply eq _ lenP v _ i c
      intro j
      rw [keep P _ _ (by rw [len]; dsimp [n]; have := j.isLt; omega)]
      simp [oneEach,List.getD_eq_getElem?_getD,j.isLt]

theorem main (k l s : Nat) (A : Fin (2^k) → Fin (2^l) → Bool) (hf : HasLitSize (k+l) (adjFun A) s) :
    RepSizeAtMost A (s + 2*2^k + k*2^((k+1)/2) + 2*2^l + l*2^((l+1)/2)) := by
  obtain ⟨C,hc,cs,ce⟩ := hf
  obtain ⟨G,p,hg,cost,bound,spec⟩ := network k l
  let n := k+l
  let base := 2^k+2^l+G.length
  let ports : Fin (n+n) → Nat := Fin.addCases (fun i => p i true) (fun i => p i false)
  let ren := wire (n+n) base ports
  let D : Circuit := ⟨G++C.gates.map (rewire ren),ren C.output⟩
  refine ⟨D,legalAppend hg (legalMap C hc ren),?_,?_⟩
  · change (G++C.gates.map _).length ≤ _
    simp only [List.length_append,List.length_map]
    unfold budget at cost
    change C.gates.length ≤ s at cs
    omega
  · intro u v
    let z := bits u v
    let x := List.ofFn z ++ List.ofFn (fun i => !z i)
    let y := run G (oneEach u v)
    have lx : x.length=n+n := by simp [x,n]
    have ly : y.length=base := by simp [y,base,run_length,oneEach]
    have pb (i : Fin (n+n)) : ports i < base := by
      induction i using Fin.addCases with
      | left j => simpa only [ports,Fin.addCases_left] using bound j true
      | right j => simpa only [ports,Fin.addCases_right] using bound j false
    have agree (i : Fin (n+n)) : y.getD (ports i) false = x.getD i false := by
      induction i using Fin.addCases with
      | left i =>
        simp only [ports,Fin.addCases_left,y,x,Fin.val_castAdd,spec]
        have hi : i.val < k+l := i.isLt
        rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi)]
        simp [List.getD_eq_getElem?_getD,z,hi]
      | right i =>
        simp only [ports,Fin.addCases_right,y,x,Fin.val_natAdd,spec]
        rw [List.getD_append_right _ _ _ _ (by simp [n])]
        simp [List.getD_eq_getElem?_getD,z,n]
    change (run (G++C.gates.map _) (oneEach u v)).getD (ren C.output) false = _
    rw [run_append]
    exact (replayOut lx ly pb agree C).trans ((ce z).trans (adjBits A u v))
end PEqualNP.Outside.L_meta_9023

theorem PEqualNP.Outside.L_meta_9023 : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.Represents.HasLitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2)) :=
  PEqualNP.Outside.L_meta_9023.main
