import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1720

-- The wire evaluation follows the checked L-meta-1693 proof.

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma wire_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = .and) :
    value C x (n + j.val) = true ↔
      ∀ r ∈ (C.gates.get j).inputs, r < n + j.val ∧ value C x r = true := by
  rw [gate_value C x _ (by omega) (by simp [Circuit.size, j.isLt])]
  simp [← List.get_eq_getElem, hop, GateOp.eval, List.all_eq_true]

private lemma wire_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = .or) :
    value C x (n + j.val) = true ↔
      ∃ r ∈ (C.gates.get j).inputs, r < n + j.val ∧ value C x r = true := by
  rw [gate_value C x _ (by omega) (by simp [Circuit.size, j.isLt])]
  simp [← List.get_eq_getElem, hop, GateOp.eval, List.any_eq_true]

private def Good (n : ℕ) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧ ReadsBack n C

private lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by simp [gateAt,hj]

private def pushGate (C : Circuit) (a b : ℕ) : Circuit := ⟨C.gates ++ [⟨.or,[a,b]⟩],0⟩

private lemma push_size (C : Circuit) (a b : ℕ) : (pushGate C a b).size = C.size+1 := by
  simp [pushGate,Circuit.size]

private lemma push_good (n : ℕ) (C : Circuit) (hC : Good n C) (a b : ℕ)
    (ha : a < n+C.size) (hb : b < n+C.size) : Good n (pushGate C a b) := by
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hh | hh
    · exact hC.1 g hh
    · obtain rfl : g = ⟨.or,[a,b]⟩ := by simpa using hh
      simp
  · intro j hj w hw
    by_cases h : j < C.gates.length
    · have e : gateAt (pushGate C a b) j = gateAt C j := by
        unfold gateAt pushGate
        exact List.getD_append _ _ _ _ h
      exact hC.2 j h w (e ▸ hw)
    · have he : j = C.gates.length := by
        have hj' : j < C.gates.length+1 := by simpa [pushGate] using hj
        omega
      subst j
      simp [gateAt,pushGate] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb

private lemma push_value {n : ℕ} (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n+C.size) : value (pushGate C a b) x w = value C x w := by
  change (run (C.gates++_) (List.ofFn x)).getD w false = (run C.gates (List.ofFn x)).getD w false
  have h : w < (run C.gates (List.ofFn x)).length := by simpa [run_length,Circuit.size] using hw
  rw [show run (C.gates++[⟨.or,[a,b]⟩]) (List.ofFn x) =
      run [⟨.or,[a,b]⟩] (run C.gates (List.ofFn x)) from by simp [run,List.foldl_append]]
  exact run_getD _ _ _ h

private lemma push_or {n : ℕ} (C : Circuit) (a b : ℕ) (x : Fin n → Bool) :
    value (pushGate C a b) x (n+C.size) = (value C x a || value C x b) := by
  let W := run C.gates (List.ofFn x)
  have h : W.length = n+C.size := by simp [W,run_length,Circuit.size]
  change (run (C.gates++[⟨.or,[a,b]⟩]) (List.ofFn x)).getD (n+C.size) false = _
  rw [show run (C.gates++[⟨.or,[a,b]⟩]) (List.ofFn x) = run [⟨.or,[a,b]⟩] W from
    by simp [W,run,List.foldl_append],run_cons]
  simp only [run,List.foldl_nil]
  rw [← h,List.getD_append_right _ _ _ _ (by omega)]
  simp [GateOp.eval,value,W,run,Circuit.wires]

private lemma append_chain {n : ℕ} (C : Circuit) (a : ℕ) (tail : List ℕ)
    (hC : Good n C) (ha : a < n+C.size) (hTail : ∀ w ∈ tail, w < n+C.size) :
    ∃ D : Circuit, ∃ o : ℕ, Good n D ∧ D.size = C.size+tail.length ∧ o < n+D.size ∧
      (∀ (x : Fin n → Bool) (w : ℕ), w < n+C.size → value D x w = value C x w) ∧
      (∀ x : Fin n → Bool, value D x o = true ↔ ∃ w ∈ a::tail, value C x w = true) := by
  induction tail generalizing C a with
  | nil =>
    exact ⟨C,a,hC,by simp,ha,fun _ _ _ => rfl,fun x => by simp⟩
  | cons b tail ih =>
    let E := pushGate C a b
    have hb := hTail b (by simp)
    have hE := push_good n C hC a b ha hb
    have hEsize : E.size = C.size+1 := push_size C a b
    have hElt : n+C.size < n+E.size := by omega
    have hRest (w : ℕ) (hw : w ∈ tail) : w < n+E.size :=
      (hTail w (by simp [hw])).trans hElt
    obtain ⟨D,o,hD,hSize,ho,hEq,hOut⟩ := ih E (n+C.size) hE hElt hRest
    refine ⟨D,o,hD,by simp only [hSize,hEsize,List.length_cons]; omega,ho,?_,?_⟩
    · intro x w hw
      exact (hEq x w (hw.trans hElt)).trans (push_value C a b x w hw)
    · intro x
      rw [hOut x]
      simp only [List.mem_cons,exists_eq_or_imp, Bool.or_eq_true, push_or, E]
      have he : (∃ w ∈ tail, value (pushGate C a b) x w = true) ↔
          ∃ w ∈ tail, value C x w = true := by
        constructor <;> rintro ⟨w,hw,ht⟩ <;> refine ⟨w,hw,?_⟩
        · exact (push_value C a b x w (hTail w (by simp [hw]))).symm ▸ ht
        · exact (push_value C a b x w (hTail w (by simp [hw]))) ▸ ht
      rw [he]
      tauto

private lemma append_groups {n : ℕ} (C : Circuit) (m : ℕ) (S : Fin m → List ℕ)
    (hC : Good n C) (hS : ∀ i, ∀ w ∈ S i, w < n+C.size) :
    ∃ D : Circuit, ∃ o : Fin m → ℕ, Good n D ∧
      C.size ≤ D.size ∧ D.size ≤ C.size + ∑ i, (S i).length ∧
      (∀ (x : Fin n → Bool) w, w < n+C.size → value D x w = value C x w) ∧
      (∀ (i : Fin m) (x : Fin n → Bool), value D x (o i) = true ↔
        ∃ w ∈ S i, value C x w = true) := by
  induction m generalizing C with
  | zero =>
    exact ⟨C,Fin.elim0,hC,le_rfl,by simp,fun _ _ _ => rfl,fun i => Fin.elim0 i⟩
  | succ m ih =>
    cases hs : S 0 with
    | nil =>
      obtain ⟨D,o,hD,hLower,hUpper,hEq,hOut⟩ := ih C (fun i => S i.succ) hC
        (fun i => hS i.succ)
      refine ⟨D,Fin.cases (n+D.size) o,hD,hLower,?_,hEq,?_⟩
      · rw [Fin.sum_univ_succ,hs]
        simpa using hUpper
      · intro i x
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [hs,missing_value D x _ (Nat.le_refl _)]
        · simpa using hOut j x
    | cons a tail =>
      have ha := hS 0 a (by rw [hs]; simp)
      have hTail (w : ℕ) (hw : w ∈ tail) : w < n+C.size := hS 0 w (by rw [hs]; simp [hw])
      obtain ⟨E,o₀,hE,hESize,ho₀,hEEq,hEOut⟩ := append_chain C a tail hC ha hTail
      obtain ⟨D,o,hD,hLower,hUpper,hEq,hOut⟩ := ih E (fun i => S i.succ) hE
        (fun i w hw => by have := hS i.succ w hw; omega)
      refine ⟨D,Fin.cases o₀ o,hD,by omega,?_,?_,?_⟩
      · rw [Fin.sum_univ_succ,hs]
        simp only [List.length_cons]
        omega
      · intro x w hw
        exact (hEq x w (by omega)).trans (hEEq x w hw)
      · intro i x
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero,hs,hEq x o₀ ho₀] using hEOut x
        · simp only [Fin.cases_succ,hOut]
          constructor <;> rintro ⟨w,hw,ht⟩ <;> refine ⟨w,hw,?_⟩
          · exact (hEEq x w (hS j.succ w hw)) ▸ ht
          · exact (hEEq x w (hS j.succ w hw)).symm ▸ ht

private def relabel (n w : ℕ) : ℕ := if w < n then 0 else w-n

private lemma alias_lt {n k w : ℕ} (_hn : 0 < n) (hw : w < n+n+k) :
    relabel n w < n+k := by
  unfold relabel
  split <;> omega

private def projected (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op,g.inputs.map (relabel n)⟩),0⟩

private lemma projected_size (n : ℕ) (C : Circuit) : (projected n C).size = C.size := by
  simp [projected,Circuit.size]

private lemma projected_good {n : ℕ} (hn : 0 < n) (C : Circuit) (hC : Good (n+n) C) :
    Good n (projected n C) := by
  constructor
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa using hC.1 a ha
  · intro j hj w hw
    have hj' : j < C.gates.length := by simpa [projected] using hj
    have e : gateAt (projected n C) j =
        (⟨(gateAt C j).op,(gateAt C j).inputs.map (relabel n)⟩ : Gate) := by
      unfold gateAt projected
      simp [hj']
    rw [e] at hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact alias_lt hn (hC.2 j hj' v hv)

private lemma projected_value {n : ℕ} (hn : 0 < n) (C : Circuit) (hC : Good (n+n) C)
    (y : Fin n → Bool) (w : ℕ) (hw : w < n+n+C.size) :
    value (projected n C) y (relabel n w) =
      value C (Fin.append (fun _ : Fin n => y ⟨0,hn⟩) y) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hRaw : w < n+n
    · let p : Fin (n+n) := ⟨w,hRaw⟩
      let v : Fin n := ⟨relabel n w,by simpa using alias_lt (k:=0) hn (by simpa using hRaw)⟩
      change value (projected n C) y v = value C (Fin.append (fun _ : Fin n => y ⟨0,hn⟩) y) p
      rw [input_value,input_value]
      by_cases hp : w < n
      · let a : Fin n := ⟨w,hp⟩
        have ep : p = Fin.castAdd n a := Fin.ext rfl
        have ev : v = ⟨0,hn⟩ := Fin.ext (by simp [v,relabel,hp])
        rw [ep,ev,Fin.append_left]
      · have ep : p = Fin.natAdd n v := Fin.ext (by simp [p,v,relabel,hp]; omega)
        rw [ep,Fin.append_right]
    · let j := w-(n+n)
      have hJ : j < C.gates.length := by unfold j Circuit.size at *; omega
      have hW : w = n+n+j := by omega
      have hAlias : relabel n w = n+j := by unfold relabel; split <;> omega
      rw [hAlias, hW, gate_value (projected n C) y (n+j) (by omega)
        (by rw [projected_size]; unfold Circuit.size; omega),
        gate_value C _ (n+n+j) (by omega) (by unfold Circuit.size; omega)]
      simp only [Nat.add_sub_cancel_left,projected,List.getElem_map]
      apply congrArg (C.gates[j].op.eval)
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      have hLt := hC.2 j hJ r (by simpa only [gateAt_eq C j hJ] using hr)
      simp only [Function.comp_apply,ite_eq_left (alias_lt hn hLt),ite_eq_left hLt]
      exact ih r (by omega) (by unfold Circuit.size; omega)

private def degreeRun (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun w g => w ++ [g.lineDegree w]) d

private lemma degree_len (gs : List Gate) (d : List ℕ) :
    (degreeRun gs d).length = d.length+gs.length := by
  induction gs generalizing d with
  | nil => simp [degreeRun]
  | cons g gs ih =>
    change (degreeRun gs (d++[g.lineDegree d])).length = d.length+(g::gs).length
    rw [ih]
    simp
    omega

private lemma degree_get (gs : List Gate) (d : List ℕ) (w : ℕ) (hw : w < d.length) :
    (degreeRun gs d).getD w 0 = d.getD w 0 := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    change (degreeRun gs (d++[g.lineDegree d])).getD w 0 = d.getD w 0
    rw [ih _ (by simp; omega),List.getD_append _ _ _ _ hw]

private abbrev deg (n : ℕ) (C : Circuit) (S : Finset ℕ) (w : ℕ) : ℕ :=
  (C.lineDegrees n S).getD w 0

private lemma degree_zero {n : ℕ} (C : Circuit) (hBack : ReadsBack n C) (S : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length)
    (hz : ∀ w ∈ (gateAt C j).inputs, deg n C S w = 0) :
    deg n C S (n+j) = 0 := by
  let init := (List.range n).map fun i => if i ∈ S then 1 else 0
  let d := degreeRun (C.gates.take j) init
  let g := gateAt C j
  have hd : d.length = n+j := by simp [d,degree_len,init,Nat.min_eq_left (Nat.le_of_lt hj)]
  have split : C.lineDegrees n S = degreeRun (g :: C.gates.drop (j+1)) d := by
    change degreeRun C.gates init = _
    have h : (C.gates.take j) ++ g::C.gates.drop (j+1) = C.gates := by
      dsimp only [g]
      rw [gateAt_eq C j hj,← List.drop_eq_getElem_cons hj,List.take_append_drop]
    rw (occs := [1]) [← h]
    simp [degreeRun,List.foldl_append,d]
  have hz' (w) (hw : w ∈ g.inputs) : d.getD w 0 = 0 := by
    have hlt := hBack j hj w hw
    have hh : w < d.length := by omega
    rw [← degree_get (g::C.gates.drop (j+1)) d w hh,← split]
    exact hz w hw
  have hZeros : (g.inputs.map fun w => d.getD w 0) = g.inputs.map (fun _ => 0) :=
    List.map_congr_left hz'
  have hGate : g.lineDegree d = 0 := by
    unfold Gate.lineDegree
    rw [hZeros]
    have hSum : (g.inputs.map fun _ => (0 : ℕ)).sum = 0 := by
      induction g.inputs <;> simp_all
    have hMax : (g.inputs.map fun _ => (0 : ℕ)).foldr max 0 = 0 := by
      induction g.inputs <;> simp_all
    rw [hSum,hMax]
    split <;> rfl
  change (C.lineDegrees n S).getD (n+j) 0 = 0
  rw [split]
  change (degreeRun (C.gates.drop (j+1)) (d++[g.lineDegree d])).getD (n+j) 0 = 0
  rw [degree_get _ _ _ (by simp [hd]),List.getD_append_right _ _ _ _ (by omega),hd]
  simp [hGate]

private abbrev pt (n : ℕ) (C : Circuit) := deg (n+n) C (Finset.range n)
private abbrev ln (n : ℕ) (C : Circuit) := deg (n+n) C (Finset.Ico n (n+n))
private def entry (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  pt n C w = 0 ∧ 0 < ln n C w ∧ ∃ j < C.gates.length, w ∈ (gateAt C j).inputs ∧
    0 < pt n C (n+n+j) ∧ 0 < ln n C (n+n+j)

private lemma entry_card (n : ℕ) (C : Circuit) (hC : Good (n+n) C)
    (H : Finset ℕ) (hH : ∀ w ∈ H, entry n C w) :
    H.card ≤ ((Finset.range C.size).filter
      (fun j => 0 < pt n C (n+n+j) ∧ 0 < ln n C (n+n+j))).card := by
  classical
  let J := (Finset.range C.size).filter
    (fun j => 0 < pt n C (n+n+j) ∧ 0 < ln n C (n+n+j))
  let F (j : ℕ) := (gateAt C j).inputs.toFinset.filter (fun w => pt n C w = 0)
  have hCover : H ⊆ J.biUnion F := by
    intro w hw
    obtain ⟨hP,_,j,hj,hm,hJP,hJL⟩ := hH w hw
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hJP,hJL⟩,
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm,hP⟩⟩
  have hSmall (j : ℕ) (hj : j ∈ J) : (F j).card ≤ 1 := by
    obtain ⟨hj',hP,_⟩ := Finset.mem_filter.mp hj
    have hValid : j < C.gates.length := Finset.mem_range.mp hj'
    have hExists : ∃ w ∈ (gateAt C j).inputs, pt n C w ≠ 0 := by
      by_contra! h
      exact (Nat.ne_of_gt hP) (degree_zero C hC.2 (Finset.range n) j hValid h)
    obtain ⟨w,hw,hNot⟩ := hExists
    have hSub : F j ⊆ (gateAt C j).inputs.toFinset.erase w := by
      intro v hv
      obtain ⟨hv',hZ⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_erase.mpr ⟨fun ht => hNot (ht ▸ hZ),hv'⟩
    have hArity := (hC.1 (gateAt C j) (by rw [gateAt_eq _ _ hValid]; exact List.getElem_mem hValid)).2
    have hCard := Finset.card_le_card hSub
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr hw)] at hCard
    have hh := List.toFinset_card_le (gateAt C j).inputs
    omega
  refine (Finset.card_le_card hCover).trans (Finset.card_biUnion_le.trans ?_)
  calc
    ∑ j ∈ J, (F j).card ≤ ∑ _j ∈ J, 1 := Finset.sum_le_sum hSmall
    _ = J.card := by simp

private abbrev one {n : ℕ} (p : Fin n) (a : Fin n) : Bool := decide (a = p)
private abbrev zero {n : ℕ} : Fin n → Bool := fun _ => false

private lemma append_one {n : ℕ} (p l : Fin n) :
    Fin.append (one p) (one l) =
      (fun k => decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l)) := by
  funext k
  refine Fin.addCases (motive := fun z => Fin.append (one p) (one l) z =
      decide (z = Fin.castAdd n p ∨ z = Fin.natAdd n l)) ?_ ?_ k
  · intro a
    have he : Fin.castAdd n a ≠ Fin.natAdd n l := by
      intro h
      have h' := congrArg Fin.val h
      simp at h'
      have := a.isLt
      omega
    simp only [Fin.append_left,he,or_false,Fin.castAdd_inj]
  · intro a
    have he : Fin.natAdd n a ≠ Fin.castAdd n p := by
      intro h
      have h' := congrArg Fin.val h
      simp at h'
      have := p.isLt
      omega
    simp only [Fin.append_right,he,false_or,Fin.natAdd_inj]

private lemma one_card {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun l => one p l = true)).card = 1 := by
  have he : (Finset.univ.filter (fun l => one p l = true)) = {p} := by
    ext l
    simp
  rw [he,Finset.card_singleton]

private lemma finite_count {s : Set ℕ} (F : Finset ℕ)
    (h : ∀ j : ℕ, j ∈ F ↔ j ∈ s) : s.ncard = F.card := by
  rw [← Set.ncard_coe_finset F]
  congr 1
  ext j
  exact (h j).symm

private lemma group_count {n : ℕ} (H : Finset ℕ) (tag : ℕ → Bool × Fin n) :
    (∑ i : Fin n, (H.filter (fun w => tag w = (false,i))).card) +
      (∑ i : Fin n, (H.filter (fun w => tag w = (true,i))).card) ≤ H.card := by
  classical
  let G (b : Bool) (i : Fin n) := H.filter (fun w => tag w = (b,i))
  let B (b : Bool) := Finset.univ.biUnion (G b)
  have hCount (b : Bool) : (∑ i : Fin n, (G b i).card) = (B b).card := by
    apply (Finset.card_biUnion ?_).symm
    intro i _ j _ hne
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    have he := ((Finset.mem_filter.mp hi).2).symm.trans (Finset.mem_filter.mp hj).2
    exact hne (congrArg Prod.snd he)
  have hDis : Disjoint (B false) (B true) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hw'
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hw'
    have he := ((Finset.mem_filter.mp hi).2).symm.trans (Finset.mem_filter.mp hj).2
    exact Bool.false_ne_true (congrArg Prod.fst he)
  have hSub : B false ∪ B true ⊆ H := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hi).1
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hi).1
  change (∑ i, (G false i).card) + (∑ i, (G true i).card) ≤ H.card
  rw [hCount,hCount,← Finset.card_union_of_disjoint hDis]
  exact Finset.card_le_card hSub

end PEqualNP.Outside.L_meta_1720

set_option maxHeartbeats 2000000 in
open PEqualNP.Outside.L_meta_1720 in
theorem PEqualNP.Outside.L_meta_1720 :
(∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (q20 N20 k20 : ℕ) (I20 : Fin N20 → Fin N20 → Prop) [DecidableRel I20] (C20 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q20 → N20 = q20 ^ 2 + q20 + 1 → (∀ l20c : Fin N20, (Finset.univ.filter (fun p20f => I20 p20f l20c)).card = q20 + 1) → (∀ pa20 pb20 : Fin N20, pa20 ≠ pb20 → ∃! lb20 : Fin N20, I20 pa20 lb20 ∧ I20 pb20 lb20) → 1 ≤ k20 → (∀ g20 ∈ C20.gates, (g20.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N20 + N20) C20 → (∀ j20 < C20.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.Ico N20 (N20 + N20))).getD i20 0 = 0) ∨ (∀ h20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.range N20)).getD h20 0 = 0)) → (∀ p20g l20d : Fin N20, I20 p20g l20d → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 (fun i20a => decide (i20a = Fin.castAdd N20 p20g ∨ i20a = Fin.natAdd N20 l20d)) = true) → (∀ z20 : Fin (N20 + N20) → Bool, (Finset.univ.filter (fun l20e : Fin N20 => z20 (Fin.natAdd N20 l20e) = true)).card ≤ k20 → (¬ ∃ p20h l20f : Fin N20, I20 p20h l20f ∧ z20 (Fin.castAdd N20 p20h) = true ∧ z20 (Fin.natAdd N20 l20f) = true) → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 z20 = false) → ∃ (X20 Y20 : PEqualNP.CircuitLowerBounds.Circuit) (ps20 rh20 : Fin N20 → ℕ), ((∀ g20a ∈ X20.gates, (g20a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 X20) ∧ ((∀ g20b ∈ Y20.gates, (g20b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 Y20) ∧ X20.size + Y20.size ≤ 5 * C20.size ∧ (∀ w20 p20 : Fin N20, (X20.wires (List.ofFn (fun a20 => decide (a20 = p20)))).getD (ps20 w20) false = true → I20 p20 w20) ∧ (∀ (w20a : Fin N20) (x20 : Fin N20 → Bool), (∀ p20a : Fin N20, I20 p20a w20a → x20 p20a = false) → (X20.wires (List.ofFn x20)).getD (ps20 w20a) false = false) ∧ (∀ p20b l20 : Fin N20, (Y20.wires (List.ofFn (fun a20a => decide (a20a = l20)))).getD (rh20 p20b) false = true → I20 p20b l20) ∧ (∀ (p20c : Fin N20) (y20 : Fin N20 → Bool), (Finset.univ.filter (fun l20a : Fin N20 => y20 l20a = true)).card ≤ k20 → (∀ l20b : Fin N20, I20 p20c l20b → y20 l20b = false) → (Y20.wires (List.ofFn y20)).getD (rh20 p20c) false = false) ∧ (∀ p20d w20b : Fin N20, I20 p20d w20b → (X20.wires (List.ofFn (fun a20b => decide (a20b = p20d)))).getD (ps20 w20b) false = true ∨ (Y20.wires (List.ofFn (fun a20c => decide (a20c = w20b)))).getD (rh20 p20d) false = true) := by
  intro flag transpose q N k I _ C hq hN hLines hUnique hk hG hBack hKM hHit hSound
  classical
  have hNpos : 0 < N := by omega
  have hGood : Good (N+N) C := ⟨hG,hBack⟩
  let f (x y : Fin N → Bool) := value C (Fin.append x y) C.output
  have hits (p l : Fin N) (h : I p l) : f (one p) (one l) = true := by
    change circuitFun (N+N) C (Fin.append (one p) (one l)) = true
    rw [append_one]
    exact hHit p l h
  have sound (x y : Fin N → Bool)
      (hb : (Finset.univ.filter (fun l => y l = true)).card ≤ k)
      (hn : ∀ p l, I p l → x p = true → y l = true → False) : f x y = false := by
    apply hSound (Fin.append x y)
    · simpa only [Fin.append_right] using hb
    · rintro ⟨p,l,hI,hp,hl⟩
      exact hn p l hI (by simpa only [Fin.append_left] using hp)
        (by simpa only [Fin.append_right] using hl)
  have hZeroY (x : Fin N → Bool) : f x zero = false :=
    sound x zero (by simp) (by simp)
  have hOne (l : Fin N) : (Finset.univ.filter (fun r => one l r = true)).card ≤ k := by
    rw [one_card]
    exact hk
  have hZeroX (l : Fin N) : f zero (one l) = false :=
    sound zero (one l) (hOne l) (by simp)
  let l₀ : Fin N := ⟨0,hNpos⟩
  obtain ⟨p₀,hp₀⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter (fun p : Fin N => I p l₀)).card from by rw [hLines]; omega)
  have hI₀ := (Finset.mem_filter.mp hp₀).2
  have hHit₀ := hits p₀ l₀ hI₀
  have hFlag := (flag N C hG hBack hKM).1
  have hPt : 0 < pt N C C.output := by
    by_contra! h
    have he := (hFlag C.output (one p₀) zero (one l₀) zero).2.1 (show pt N C C.output = 0 by omega)
    exact Bool.false_ne_true ((hHit₀.symm.trans (he.trans (hZeroX l₀))).symm)
  have hLn : 0 < ln N C C.output := by
    by_contra! h
    have he := (hFlag C.output (one p₀) zero (one l₀) zero).1 (show ln N C C.output = 0 by omega)
    exact Bool.false_ne_true ((hHit₀.symm.trans (he.trans (hZeroY (one p₀)))).symm)
  obtain ⟨A,ph,Hconst,hAG,hASize,_,hFormula⟩ := transpose N C hG hBack hKM hPt hLn
  let B := projected N C
  have hBGood : Good N B := projected_good hNpos C hGood
  have hBSize : B.size = C.size := projected_size N C
  let coeff (w : ℕ) (x : Fin N → Bool) := value A x (ph w)
  let lineValue (w : ℕ) (y : Fin N → Bool) : Bool := value C (Fin.append (@zero N) y) w
  have repr (x y : Fin N → Bool) : f x y = true ↔
      ∃ w, entry N C w ∧ lineValue w y = true ∧ (w ∈ Hconst ∨ coeff w x = true) := by
    have he : f x y = true ↔ f x zero = true ∨
        ∃ w, entry N C w ∧ lineValue w y = true ∧ (w ∈ Hconst ∨ coeff w x = true) := hFormula x y
    simpa [hZeroY x] using he
  have valids (w) (hw : entry N C w) : w < N+N+C.size := by
    obtain ⟨_,_,j,hj,hm,_,_⟩ := hw
    have := hBack j hj w hm
    unfold Circuit.size
    omega
  have line_proj (w) (hw : entry N C w) (y : Fin N → Bool) :
      value B y (relabel N w) = lineValue w y := by
    exact (projected_value hNpos C hGood y w (valids w hw)).trans
      ((hFlag w (fun _ => y ⟨0,hNpos⟩) zero y zero).2.1 hw.1)
  let P (w : ℕ) (p : Fin N) : Prop := coeff w (one p) = true
  let L (w : ℕ) (l : Fin N) : Prop := lineValue w (one l) = true
  have rectangle (w) (hw : entry N C w) (p l : Fin N) (hp : P w p) (hl : L w l) : I p l := by
    by_contra hi
    have hh := (repr (one p) (one l)).2 ⟨w,hw,hl,Or.inr hp⟩
    have hz := sound (one p) (one l) (hOne l) (by
      intro a b hab ha hb
      have ea : a = p := of_decide_eq_true ha
      have eb : b = l := of_decide_eq_true hb
      subst a
      subst b
      exact hi hab)
    exact Bool.false_ne_true (hz.symm.trans hh)
  let H := (Finset.range (N+N+C.size)).filter
    (fun w => entry N C w ∧ (∃ p, P w p) ∧ ∃ l, L w l)
  have chooseSide (w : ℕ) (hw : w ∈ H) : ∃ z : Bool × Fin N,
      if z.1 then P w z.2 ∧ ∀ p, P w p → p = z.2
      else L w z.2 ∧ ∀ l, L w l → l = z.2 := by
    obtain ⟨hE,⟨p,hp⟩,l,hl⟩ := (Finset.mem_filter.mp hw).2
    by_cases h : ∀ r, P w r → r = p
    · exact ⟨(true,p),hp,h⟩
    · push Not at h
      obtain ⟨r,hr,hne⟩ := h
      obtain ⟨t,_,hT⟩ := hUnique r p hne
      refine ⟨(false,l),hl,fun s hs => ?_⟩
      exact (hT s ⟨rectangle w hE r s hr hs,rectangle w hE p s hp hs⟩).trans
        (hT l ⟨rectangle w hE r l hr hl,rectangle w hE p l hp hl⟩).symm
  choose tag₀ hTag₀ using chooseSide
  let tag (w : ℕ) : Bool × Fin N :=
    if h : w ∈ H then tag₀ w h else (false,l₀)
  have tagSpec (w) (hw : w ∈ H) :
      if (tag w).1 then P w (tag w).2 ∧ ∀ p, P w p → p = (tag w).2
      else L w (tag w).2 ∧ ∀ l, L w l → l = (tag w).2 := by
    simpa [tag,hw] using hTag₀ w hw
  let G (side : Bool) (i : Fin N) := H.filter (fun w => tag w = (side,i))
  have hEntry (side : Bool) (i : Fin N) (w : ℕ) (hw : w ∈ G side i) : entry N C w :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2.1
  have tagL (l : Fin N) (w : ℕ) (hw : w ∈ G false l) : L w l := by
    have hh := tagSpec w (Finset.mem_filter.mp hw).1
    rw [(Finset.mem_filter.mp hw).2] at hh
    exact hh.1
  have tagP (p : Fin N) (w : ℕ) (hw : w ∈ G true p) : P w p := by
    have hh := tagSpec w (Finset.mem_filter.mp hw).1
    rw [(Finset.mem_filter.mp hw).2] at hh
    exact hh.1
  let Sx (l : Fin N) := (G false l).toList.map ph
  let Sy (p : Fin N) := (G true p).toList.map (relabel N)
  have hSx (l : Fin N) (w : ℕ) (hw : w ∈ Sx l) : w < N+A.size := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
    have hR : r ∈ G false l := Finset.mem_toList.mp hr
    obtain ⟨p,hp⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).2.2.1
    by_contra! h
    exact Bool.false_ne_true ((missing_value A (one p) _ h).symm.trans hp)
  have hSy (p : Fin N) (w : ℕ) (hw : w ∈ Sy p) : w < N+B.size := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
    rw [hBSize]
    exact alias_lt hNpos (valids r (hEntry true p r (Finset.mem_toList.mp hr)))
  obtain ⟨X,ox,hXGood,_,hXCost,_,hXOut⟩ := append_groups A N Sx hAG hSx
  obtain ⟨Y,oy,hYGood,_,hYCost,_,hYOut⟩ := append_groups B N Sy hBGood hSy
  have Xout (l : Fin N) (x : Fin N → Bool) : value X x (ox l) = true ↔
      ∃ w ∈ G false l, coeff w x = true := by
    rw [hXOut]
    constructor
    · rintro ⟨r,hr,hv⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
      exact ⟨w,Finset.mem_toList.mp hw,hv⟩
    · rintro ⟨w,hw,hv⟩
      exact ⟨ph w,List.mem_map.mpr ⟨w,Finset.mem_toList.mpr hw,rfl⟩,hv⟩
  have Yout (p : Fin N) (y : Fin N → Bool) : value Y y (oy p) = true ↔
      ∃ w ∈ G true p, lineValue w y = true := by
    rw [hYOut]
    constructor
    · rintro ⟨r,hr,hv⟩
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hr
      have hm := Finset.mem_toList.mp hw
      exact ⟨w,hm,(line_proj w (hEntry true p w hm) y).symm ▸ hv⟩
    · rintro ⟨w,hw,hv⟩
      exact ⟨relabel N w,List.mem_map.mpr ⟨w,Finset.mem_toList.mpr hw,rfl⟩,
        (line_proj w (hEntry true p w hw) y) ▸ hv⟩
  let Jx := (Finset.range C.size).filter (fun j => ln N C (N+N+j) = 0)
  let Jm := (Finset.range C.size).filter (fun j =>
    0 < pt N C (N+N+j) ∧ 0 < ln N C (N+N+j))
  have hx : Set.ncard { j : ℕ | j < C.gates.length ∧ ln N C (N+N+j) = 0 } = Jx.card :=
    finite_count Jx (by intro j; simp [Jx,Circuit.size])
  have hm : Set.ncard { j : ℕ | j < C.gates.length ∧
      0 < pt N C (N+N+j) ∧ 0 < ln N C (N+N+j) } = Jm.card :=
    finite_count Jm (by intro j; simp [Jm,Circuit.size])
  change A.size ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ ln N C (N+N+j) = 0} +
    3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < pt N C (N+N+j) ∧ 0 < ln N C (N+N+j)} at hASize
  rw [hx,hm] at hASize
  have hPartition : Jx.card + Jm.card ≤ C.size := by
    have hDis : Disjoint Jx Jm := by
      refine Finset.disjoint_left.mpr ?_
      intro j h₁ h₂
      have hZ := (Finset.mem_filter.mp h₁).2
      have hP := (Finset.mem_filter.mp h₂).2.2
      omega
    rw [← Finset.card_union_of_disjoint hDis,← Finset.card_range C.size]
    apply Finset.card_le_card
    intro j hj
    exact (Finset.mem_union.mp hj).elim (fun h => (Finset.mem_filter.mp h).1)
      (fun h => (Finset.mem_filter.mp h).1)
  have hGroups : (∑ i : Fin N, (G false i).card) + (∑ i : Fin N, (G true i).card) ≤ H.card :=
    group_count H tag
  have hH := entry_card N C hGood H (fun w hw => (Finset.mem_filter.mp hw).2.1)
  change H.card ≤ Jm.card at hH
  simp only [Sx,Sy,List.length_map,Finset.length_toList,hBSize] at hXCost hYCost
  refine ⟨X,Y,ox,oy,hXGood,hYGood,by omega,?_,?_,?_,?_,?_⟩
  · intro l p hv
    obtain ⟨w,hw,hHit⟩ := (Xout l (one p)).1 hv
    exact rectangle w (hEntry false l w hw) p l hHit (tagL l w hw)
  · intro l x hOff
    by_contra hTrue
    have ht : value X x (ox l) = true := Bool.eq_true_of_not_eq_false hTrue
    obtain ⟨w,hw,hx'⟩ := (Xout l x).1 ht
    have hTop := (repr x (one l)).2 ⟨w,hEntry false l w hw,tagL l w hw,Or.inr hx'⟩
    have hBot := sound x (one l) (hOne l) (by
      intro p r hi hp hr
      have he : r = l := of_decide_eq_true hr
      subst r
      exact Bool.false_ne_true ((hOff p hi).symm.trans hp))
    exact Bool.false_ne_true (hBot.symm.trans hTop)
  · intro p l hv
    obtain ⟨w,hw,hHit⟩ := (Yout p (one l)).1 hv
    exact rectangle w (hEntry true p w hw) p l (tagP p w hw) hHit
  · intro p y hSmall hOff
    by_contra hTrue
    have ht : value Y y (oy p) = true := Bool.eq_true_of_not_eq_false hTrue
    obtain ⟨w,hw,hy'⟩ := (Yout p y).1 ht
    have hTop := (repr (one p) y).2 ⟨w,hEntry true p w hw,hy',Or.inr (tagP p w hw)⟩
    have hBot := sound (one p) y hSmall (by
      intro r l hi hr hl
      have he : r = p := of_decide_eq_true hr
      subst r
      exact Bool.false_ne_true ((hOff l hi).symm.trans hl))
    exact Bool.false_ne_true (hBot.symm.trans hTop)
  · intro p l hi
    obtain ⟨w,hE,hL,hh⟩ := (repr (one p) (one l)).1 (hits p l hi)
    have hP : P w p := hh.resolve_left (fun hc =>
      Bool.false_ne_true ((hZeroX l).symm.trans ((repr zero (one l)).2 ⟨w,hE,hL,Or.inl hc⟩)))
    have hw : w ∈ H := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (valids w hE),hE,⟨p,hP⟩,⟨l,hL⟩⟩
    have hSpec := tagSpec w hw
    rcases he : tag w with ⟨side,r⟩
    cases side
    · have hl : l = r := by rw [he] at hSpec; exact hSpec.2 l hL
      exact Or.inl ((Xout l (one p)).2 ⟨w,Finset.mem_filter.mpr ⟨hw,he.trans (by rw [hl])⟩,hP⟩)
    · have hp : p = r := by rw [he] at hSpec; exact hSpec.2 p hP
      exact Or.inr ((Yout p (one l)).2 ⟨w,Finset.mem_filter.mpr ⟨hw,he.trans (by rw [hp])⟩,hL⟩)
