import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_717

-- Wire evaluation and gate deletion from the project's proof of L-meta-540.
def stW (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wV (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ) : Bool :=
 (C.wires (List.ofFn x)).getD w false
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
 C.wires x=C.gates.foldl stW x:=rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
 (gs.foldl stW w).length=w.length+gs.length:=by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons,ih]
  simp [stW]
  omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
 (gs.foldl stW w).getD i false=w.getD i false:=by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stW w g).length:=by simp [stW];omega
  rw [ih (stW w g) hlt]
  simp [stW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length<=i) :
 w.getD i false=false:=by
 simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n->Bool) :
 (C.wires (List.ofFn x)).length=n+C.gates.length:=by
 rw [wires_eq_foldl,foldl_stepWire_length,List.length_ofFn]
lemma wvI (n : ℕ) (C : Circuit) (x : Fin n->Bool) (i : Fin n) :
 wV n C x i.val=x i:=by
 unfold wV
 rw [wires_eq_foldl,foldl_stepWire_getD_lt C.gates (List.ofFn x) i.val (by simp)]
 simp [List.getD_eq_getElem?_getD]
lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n->Bool) (w : ℕ)
 (hw : n+C.gates.length<=w) : wV n C x w=false:=by
 unfold wV
 exact getD_ge_length _ _ (by rw [wires_length];exact hw)
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
 ∃ (pre post : List Gate) (gj : Gate),
  gs=pre ++ gj :: post/\pre.length=j/\gs[j]'hj=gj:=by
 refine ⟨gs.take j,gs.drop (j+1),gs[j]'hj,?_,by simp;omega,rfl⟩
 rw [List.cons_getElem_drop_succ,List.take_append_drop]
lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
 gateAt C j=C.gates[j]'hj:=by
 simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n->Bool) (j : ℕ)
 (hj : j < C.gates.length) :
 wV n C x (n+j) =
  (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
   if i < n+j then wV n C x i else false):=by
 obtain ⟨pre,post,gj,hgs,hpre_len,hget⟩:=split_gates C.gates j hj
 have hgj : gateAt C j=gj:=by rw [gateAt_eq_getElem C j hj,hget]
 rw [hgj]
 let w0:=pre.foldl stW (List.ofFn x)
 have hW0L : w0.length=n+j:=by
  simp [w0,foldl_stepWire_length,hpre_len]
 have hCj : wV n C x (n+j)=gj.op.eval (gj.inputs.map fun i => w0.getD i false):=by
  unfold wV
  rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
  rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
  simp [stW,List.getD_eq_getElem?_getD,hW0L]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _ => ?_
 by_cases hi : i < n+j
 . rw [ite_eq_left hi]
   unfold wV
   rw [wires_eq_foldl,hgs,List.foldl_append]
   exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
 . rw [ite_eq_right hi]
   exact getD_ge_length w0 i (by omega)

def shiftDown (wOld u : ℕ) : ℕ :=
 if wOld < u then u - 1 else u
def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
 wC.length=wD.length+1 ∧
 w0.length<=wD.length ∧
 wC.getD w0.length false=bOld ∧
 (∀ u,u < w0.length->wD.getD u false=w0.getD u false) ∧
 (∀ u,u < w0.length->wC.getD u false=w0.getD u false) ∧
 (∀ u,w0.length < u->wD.getD (u - 1) false=wC.getD u false)
lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
 wiresMatch w0 bOld (w0 ++ [bOld]) w0:=by
 refine ⟨by simp,le_rfl,?_,fun _ _ => rfl,?_,?_⟩
 . simp [List.getD_eq_getElem?_getD]
 . intro u hu
   simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hu]
 . intro u hu
   have h1 : w0.length<=u - 1:=by omega
   have h2 : (w0 ++ [bOld]).length<=u:=by simp;omega
   rw [getD_ge_length w0 (u - 1) h1,getD_ge_length (w0 ++ [bOld]) u h2]
lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
 (hm : wiresMatch w0 bOld wC wD) :
 wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]):=by
 obtain ⟨hlen,hle,hbold,hltD,hltC,hgt⟩:=hm
 refine ⟨by simp;omega,by simp;omega,?_,?_,?_,?_⟩
 . have hlt : w0.length < wC.length:=by omega
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hlt]
   simpa [List.getD_eq_getElem?_getD] using hbold
 . intro u hu
   have h1 : u < wD.length:=by omega
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left h1]
   simpa [List.getD_eq_getElem?_getD] using hltD u hu
 . intro u hu
   have h2 : u < wC.length:=by omega
   rw [List.getD_eq_getElem?_getD,List.getElem?_append_left h2]
   simpa [List.getD_eq_getElem?_getD] using hltC u hu
 . intro u hu
   by_cases h1 : u - 1 < wD.length
   . have h2 : u < wC.length:=by omega
     rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
      List.getElem?_append_left h1,List.getElem?_append_left h2]
     simpa [List.getD_eq_getElem?_getD] using hgt u hu
   . by_cases heq : u - 1=wD.length
     . have heqC : u=wC.length:=by omega
       rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,heq,heqC,
        List.getElem?_append_right le_rfl,List.getElem?_append_right le_rfl]
       simp
     . have hg1 : (wD ++ [b]).length<=u - 1:=by simp;omega
       have hg2 : (wC ++ [b]).length<=u:=by simp;omega
       rw [getD_ge_length _ _ hg1,getD_ge_length _ _ hg2]
lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
 (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u≠w0.length) :
 wD.getD (shiftDown w0.length u) false=wC.getD u false:=by
 unfold shiftDown
 by_cases hgt : w0.length < u
 . rw [ite_eq_left hgt];exact hm.2.2.2.2.2 u hgt
 . rw [ite_eq_right hgt]
   have hlt : u < w0.length:=by omega
   rw [hm.2.2.2.1 u hlt,hm.2.2.2.2.1 u hlt]
lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
 (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length=gsC.length)
 (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
  wiresMatch w0 bOld vC vD->vD.length=wD.length+t →
  (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
  (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
 wiresMatch w0 bOld (gsC.foldl stW wC) (gsD.foldl stW wD):=by
 induction gsC generalizing gsD wC wD with
 | nil =>
  cases gsD with
  | nil => exact hm
  | cons => simp at hlen
 | cons gC restC ih =>
  cases gsD with
  | nil => simp at hlen
  | cons gD restD =>
   simp only [List.foldl_cons]
   have heq0:=hstep 0 (by simp) (by simp) wC wD hm (by simp)
   simp only [List.getElem_cons_zero] at heq0
   have hm1 : wiresMatch w0 bOld (stW wC gC) (stW wD gD):=by
    unfold stW
    rw [heq0]
    exact wiresMatch_step hm
   apply ih restD (stW wC gC) (stW wD gD) hm1 (by simp at hlen;omega)
   intro t htC htD vC vD hmv hvlen
   have h':=hstep (t+1) (by simp;omega) (by simp;omega) vC vD hmv
    (by simp [stW] at hvlen ⊢;omega)
   simpa only [List.getElem_cons_succ] using h'

def aliasWire (wOld wNew u : ℕ) : ℕ :=
 if u=wOld then wNew else shiftDown wOld u
lemma no_duplicate_wire {n : ℕ} {C : Circuit}
 (hmin : IsMinimalCircuit n C)
 (i j : ℕ) (hij : i < n+j) (hj : j < C.gates.length) :
 ∃ x : Fin n->Bool,wV n C x i≠wV n C x (n+j):=by
 by_contra hsame
 push Not at hsame
 obtain ⟨pre,post,gj,hgs,hpre_len,_⟩:=split_gates C.gates j hj
 let aliasGate (g : Gate) : Gate:=⟨g.op,g.inputs.map (aliasWire (n+j) i)⟩
 let D : Circuit:=⟨pre ++ post.map aliasGate,aliasWire (n+j) i C.output⟩
 have hfitD : FanInTwo D:=by
  intro g hg
  rcases List.mem_append.mp hg with hpre | hpost
  . exact hmin.1 g (by rw [hgs];exact List.mem_append_left _ hpre)
  . obtain ⟨g0,hg0,rfl⟩:=List.mem_map.mp hpost
    have hg0C:=hmin.1 g0 (by rw [hgs];exact List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
    exact ⟨hg0C.1,by simp [aliasGate,hg0C.2]⟩
 have hfunD : circuitFun n D=circuitFun n C:=by
  funext x
  have hxy:=hsame x
  simp only [circuitFun,Circuit.eval,wires_eq_foldl,D]
  conv_rhs => rw [hgs,List.foldl_append,List.foldl_cons]
  rw [List.foldl_append]
  let w0:=pre.foldl stW (List.ofFn x)
  have hW0L : w0.length=n+j:=by
   simp [w0,foldl_stepWire_length,hpre_len]
  let bOld:=gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hval_eq : w0.getD i false=bOld:=by
   have hCi : wV n C x i=w0.getD i false:=by
    unfold wV
    rw [wires_eq_foldl,hgs,List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
   have hCj : wV n C x (n+j)=bOld:=by
    unfold wV
    rw [wires_eq_foldl,hgs,List.foldl_append,List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stW w0 gj) (n+j) (by simp [stW];omega)]
    simp [stW,List.getD_eq_getElem?_getD,hW0L,bOld]
   rw [← hCi,← hCj,hxy]
  have hm0 : wiresMatch w0 bOld (stW w0 gj) w0:=wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool),wiresMatch w0 bOld vC vD →
   ∀ u,vD.getD (aliasWire (n+j) i u) false=vC.getD u false:=by
   intro vC vD hmv u
   unfold aliasWire
   by_cases hu : u=n+j
   . subst hu
     rw [ite_eq_left rfl,hmv.2.2.2.1 i (by omega),hval_eq,← hW0L,hmv.2.2.1]
   . rw [ite_eq_right hu,← hW0L]
     exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stW (stW w0 gj))
   ((post.map aliasGate).foldl stW w0):=by
   refine foldl_wiresMatch w0 bOld post (post.map aliasGate) (stW w0 gj) w0 hm0
    (by simp) ?_
   intro t htC htD vC vD hmv _
   simp only [List.getElem_map,aliasGate,List.map_map]
   congr 1
   refine List.map_congr_left fun u _ => ?_
   exact halias_get vC vD hmv u
  exact halias_get _ _ hmEnd C.output
 have hle:=hmin.2 D hfitD hfunD
 have hlenC : C.gates.length=pre.length+1+post.length:=by
  have:=congrArg List.length hgs;simp at this;omega
 simp only [Circuit.size,D,List.length_append,List.length_map] at hle
 omega

lemma other_wire_eq {n j : ℕ} {C : Circuit} {x y : Fin (n + 1) → Bool}
    (sameInput : ∀ i : Fin (n+1), i.val ≠ n → x i = y i)
    (sameGate : wV (n+1) C x (n+1+j) = wV (n+1) C y (n+1+j))
    (onlyReader : ∀ k, k < C.gates.length → n ∈ (gateAt C k).inputs → k = j) :
    ∀ i : ℕ, i ≠ n → wV (n+1) C x i = wV (n+1) C y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hInput : i < n+1
    · let t : Fin (n+1) := ⟨i, hInput⟩
      exact (wvI _ C x t).trans ((sameInput t hi).trans (wvI _ C y t).symm)
    by_cases hBound : i < (n+1) + C.gates.length
    · let k := i - (n+1)
      have hk : k < C.gates.length := by dsimp [k]; omega
      have he : i = n+1+k := by dsimp [k]; omega
      by_cases hkj : k = j
      · rw [he, hkj]; exact sameGate
      rw [he, wireVal_gate _ C x k hk, wireVal_gate _ C y k hk]
      congr 1
      apply List.map_congr_left
      intro u hu
      split
      · rename_i hlt
        exact ih u (by omega) (fun hn => hkj (onlyReader k hk (hn ▸ hu)))
      · rfl
    · rw [wireVal_ge _ C x i (by omega), wireVal_ge _ C y i (by omega)]

lemma control_gate {n j : ℕ} {C : Circuit} (hj : j < C.gates.length)
    (reads : n ∈ (gateAt C j).inputs) (x : Fin (n+1) → Bool) (b : Bool)
    (hx : x (Fin.last n) = b)
    (hop : ((gateAt C j).op = .and ∧ b = false) ∨ ((gateAt C j).op = .or ∧ b = true)) :
    wV (n+1) C x (n+1+j) = b := by
  rw [wireVal_gate _ C x j hj]
  have hf : (if n < n+1+j then wV (n+1) C x n else false) = b := by
    rw [ite_eq_left (by omega)]
    exact (wvI _ C x (Fin.last n)).trans hx
  have hm : b ∈ (gateAt C j).inputs.map (fun i => if i < n+1+j then wV (n+1) C x i else false) :=
    List.mem_map.mpr ⟨n, reads, hf⟩
  rcases hop with ⟨ha, rfl⟩ | ⟨ho, rfl⟩
  · rw [ha, GateOp.eval, List.all_eq_false]
    exact ⟨false, hm, by decide⟩
  · rw [ho, GateOp.eval, List.any_eq_true]
    exact ⟨true, hm, rfl⟩

end PEqualNP.Outside.L_meta_717

open PEqualNP.Outside.L_meta_717

theorem PEqualNP.Outside.L_meta_717 : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ y y' : Fin n → Bool, g y ≠ g y') → PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' → (∀ x : Fin (n + 1) → Bool, C'.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → C.size ≤ C'.size) → ¬ ∃ (j : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some h ∧ (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n ∈ h.inputs ∧ ∀ (j' : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j := by
  intro n g C hNon hFan hEval hMin
  rintro ⟨j, h, hj?, hop, hread, huniq⟩
  obtain ⟨hj, hAt⟩ := List.getElem?_eq_some_iff.mp hj?
  have hGate : gateAt C j = h := (gateAt_eq_getElem _ _ hj).trans hAt
  rw [← hGate] at hop hread
  have hm : IsMinimalCircuit (n+1) C := by
    refine ⟨hFan, fun D hf hd => hMin D hf ?_⟩
    intro x
    exact (congrFun hd x).trans (hEval x)
  obtain ⟨x, hx⟩ := no_duplicate_wire hm n j (by omega) hj
  have hIn : wV (n+1) C x n = x (Fin.last n) := wvI _ _ _ (Fin.last n)
  rw [hIn] at hx
  let y : Fin (n+1) → Bool := Function.update x (Fin.last n) (!(x (Fin.last n)))
  have hLast : y (Fin.last n) = !(x (Fin.last n)) := Function.update_self ..
  have hOther (i : Fin (n+1)) (hi : i.val ≠ n) : x i = y i := by
    exact (Function.update_of_ne (fun he => hi (congrArg Fin.val he)) _ _).symm
  have hgEq : wV (n+1) C x (n+1+j) = wV (n+1) C y (n+1+j) := by
    rcases hop with op | op
    · cases hz : x (Fin.last n) with
      | false => exact False.elim (hx (hz.trans (control_gate hj hread x false hz (Or.inl ⟨op,rfl⟩)).symm))
      | true =>
        have hv : wV (n+1) C x (n+1+j) = false := by
          cases hv : wV (n+1) C x (n+1+j) <;> simp_all
        exact hv.trans (control_gate hj hread y false (by simp [hLast, hz]) (Or.inl ⟨op,rfl⟩)).symm
    · cases hz : x (Fin.last n) with
      | false =>
        have hv : wV (n+1) C x (n+1+j) = true := by
          cases hv : wV (n+1) C x (n+1+j) <;> simp_all
        exact hv.trans (control_gate hj hread y true (by simp [hLast, hz]) (Or.inr ⟨op,rfl⟩)).symm
      | true => exact False.elim (hx (hz.trans (control_gate hj hread x true hz (Or.inr ⟨op,rfl⟩)).symm))
  have hout : C.output ≠ n := by
    intro he
    have hf (a : Fin n → Bool) : g a = false := by
      let z : Fin (n+1) → Bool := Fin.snoc a false
      have hin : C.eval (List.ofFn z) = z (Fin.last n) := by
        change wV _ C z C.output = _
        rw [he]
        exact wvI _ C z (Fin.last n)
      have hh := (hEval z).symm.trans hin
      simpa [z, Fin.snoc_last, Fin.snoc_castSucc] using hh
    obtain ⟨a,b,hab⟩ := hNon
    exact hab ((hf a).trans (hf b).symm)
  have houtEq := other_wire_eq hOther hgEq (fun k hk hr =>
    huniq k (gateAt C k) (by rw [gateAt_eq_getElem _ _ hk, List.getElem?_eq_getElem hk]) hr) C.output hout
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at houtEq
  have hRestrict : (fun i : Fin n => x i.castSucc) = (fun i : Fin n => y i.castSucc) := by
    funext i
    exact hOther _ (by have := i.isLt; simp; omega)
  rw [hEval x, hEval y, ← hRestrict, hLast] at houtEq
  exact (show ∀ a b : Bool, xor a b ≠ xor (!a) b by decide) _ _ houtEq
