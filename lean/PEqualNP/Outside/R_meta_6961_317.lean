import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_6961_317
    (fixed :
      let offsets : Finset (Fin 13) := {0,1,3,9}
      let I := fun (p l : Fin 13) => ∃ d ∈ offsets, p = l+d
      let Q : List (List Nat) := [[3,9],[3,9,1],[4,5],[4,5,7],[6,10],[6,10,11],[2,8],[2,8,12]]
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size = 19 ∧ D.output < 45 ∧
        (∀ x : Fin 26 → Bool, ∃ t : List Bool, t.length = 11 ∧
          D.wires (List.ofFn x) = List.ofFn x ++ Q.map (fun qs => qs.any (fun k => (List.ofFn x).getD k false)) ++ t) ∧
        ∀ x : Fin 26 → Bool, circuitFun 26 D x = true ↔
          ∃ l : Fin 13, I 0 l ∧ ∃ p : Fin 13, I p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (affine :
      let offsets : Finset (Fin 13) := {0,1,3,9}
      let I := fun (p l : Fin 13) => ∃ d ∈ offsets, p = l+d
      let Q : List (List Nat) := [[3,9],[3,9,1],[4,5],[4,5,7],[6,10],[6,10,11],[2,8],[2,8,12]]
      ∃ C : Circuit, Monotone2 C ∧ ReadsBack 45 C ∧ C.size ≤ 43 ∧ C.output < 45+C.size ∧
        ∀ (x : Fin 26 → Bool) (t : List Bool), t.length = 11 →
          (C.eval (List.ofFn x ++ Q.map (fun qs => qs.any (fun k => (List.ofFn x).getD k false)) ++ t) = true ↔
          ∃ l : Fin 13, ¬ I 0 l ∧ ∃ p : Fin 13, I p l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (63 : ℕ) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x2 = Decidable.decide (∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (∃ x5 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x3 = x4 + x5) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) := by
  have gateLookup (c : Circuit) (j : Nat) :
      gateAt c j = c.gates.getD j ⟨GateOp.or,[]⟩ := rfl
  have sizeEq (c : Circuit) : c.size = c.gates.length := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g rest ih =>
      change (rest.foldl step (step w g)).length = _
      rw [ih (step w g)]
      simp [step] <;> omega

  have old_index (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

  have append_order {a b : Circuit} {n : Nat}
      (ha : ReadsBack n a) (hb : ReadsBack (n + a.size) b) :
      ReadsBack n ⟨a.gates ++ b.gates,0⟩ := by
    intro j hj i hi
    by_cases h : j < a.gates.length
    · apply ha j h
      simpa [gateLookup,List.getD_eq_getElem?_getD,List.getElem?_append_left h] using hi
    · have hj' : j - a.gates.length < b.gates.length := by
        simp at hj
        omega
      have hx : i ∈ (gateAt b (j-a.gates.length)).inputs := by
        simpa [gateLookup,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : a.gates.length ≤ j)] using hi
      have := hb _ hj' _ hx
      rw [sizeEq] at this
      omega

  have glue (n : Nat) (a b : Circuit) (ha : Monotone2 a) (hb : Monotone2 b)
      (wa : ReadsBack n a) (wb : ReadsBack (n+a.size) b)
      (oa : a.output < n+a.size) (ob : b.output < n+a.size+b.size) :
      ∃ c : Circuit, Monotone2 c ∧ ReadsBack n c ∧ c.size = a.size+b.size+1 ∧
        ∀ x : Fin n → Bool,
          circuitFun n c x = (circuitFun n a x ||
            b.eval (a.wires (List.ofFn x))) := by
    let ab : Circuit := ⟨a.gates++b.gates,0⟩
    let last : Circuit := ⟨[⟨.or,[a.output,b.output]⟩],0⟩
    let c : Circuit := ⟨ab.gates++last.gates,n+a.size+b.size⟩
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ (a.gates ++ b.gates) ++ [⟨.or,[a.output,b.output]⟩] at hg
      simp only [List.mem_append,List.mem_singleton] at hg
      rcases hg with (h|h)|rfl
      · exact ha _ h
      · exact hb _ h
      · simp
    · have wab : ReadsBack n ab := append_order wa wb
      have wl : ReadsBack (n+ab.size) last := by
        intro j hj i hi
        change j < 1 at hj
        have : j=0 := by omega
        subst j
        simp [gateLookup,last] at hi
        simp [ab,sizeEq] at *
        omega
      exact append_order wab wl
    · simp [c,ab,last,sizeEq,Nat.add_assoc]
    · intro x
      let w := a.wires (List.ofFn x)
      let v := b.wires w
      have hw : w.length = n+a.size := by
        change (a.gates.foldl step (List.ofFn x)).length = _
        rw [fold_length]; simp [sizeEq]
      have hv : v.length = n+a.size+b.size := by
        change (b.gates.foldl step w).length = _
        rw [fold_length,hw]; rfl
      change (((a.gates++b.gates)++last.gates).foldl step (List.ofFn x)).getD _ false =
        (w.getD a.output false || v.getD b.output false)
      rw [List.foldl_append,List.foldl_append]
      change (v ++ [GateOp.or.eval ([a.output,b.output].map fun i => v.getD i false)]).getD (n+a.size+b.size) false = _
      rw [← hv]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),
        Nat.sub_self,List.getElem?_cons_zero,Option.getD_some,List.map_cons,List.map_nil,
        evalOr,List.any_cons,List.any_nil,id_eq,Bool.or_false]
      have hold : v.getD a.output false = w.getD a.output false :=
        old_index b.gates w a.output (by omega)
      simpa only [List.getD_eq_getElem?_getD] using congrArg (fun z => z || v.getD b.output false) hold


  let offsets : Finset (Fin 13) := {0,1,3,9}
  let I := fun (p l : Fin 13) => ∃ d ∈ offsets, p = l+d
  let Q : List (List Nat) := [[3,9],[3,9,1],[4,5],[4,5,7],[6,10],[6,10,11],[2,8],[2,8,12]]
  obtain ⟨D,md,wd,sd,od,hw,hf⟩ := fixed
  obtain ⟨C,mc,wc,sc,oc,hc⟩ := affine
  have nl : 26 + D.size = 45 := by omega
  obtain ⟨G,mg,_,sg,hg⟩ := glue 26 D C md mc wd (nl ▸ wc) (by omega) (by omega)
  refine ⟨G,mg,by omega,?_⟩
  intro x
  obtain ⟨t,ht,hw'⟩ := hw x
  rw [hg x,hw']
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true,decide_eq_true_eq,hf x,hc x t ht]
  have rel (p l : Fin 13) : I p l ↔ ∃ d ∈ [(0 : Fin 13),1,3,9], p=l+d := by simp [I,offsets]
  constructor
  · rintro (⟨l,_,p,hi,hx,hy⟩|⟨l,_,p,hi,hx,hy⟩)
    all_goals exact ⟨p,l,(rel p l).mp hi,hx,hy⟩
  · rintro ⟨p,l,hi,hx,hy⟩
    by_cases h : I 0 l
    · exact Or.inl ⟨l,h,p,(rel p l).mpr hi,hx,hy⟩
    · exact Or.inr ⟨l,h,p,(rel p l).mpr hi,hx,hy⟩
