import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Geometry supplies the short-side row reduction; synthesis then operates only on finite row columns.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2401_617
  (geometry : let D : Finset (Fin 13) := {0,1,3,9}
let I := fun p l : Fin 13 => ∃ d ∈ D, p=l+d
∀ P : Finset (Fin 13), let W : Finset (Fin 13) := Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ P, ¬ I p l)
  P.card ≤ 3 ∨ W.card ≤ 3)
  (witness : let D : Finset (Fin 13) := {0,1,3,9}
let I := fun p w : Fin 13 => ∃ d ∈ D, p=w+d
let S := Finset (Fin 13)
let A : S → Finset (Fin 13) := fun P => Finset.univ.filter (fun w : Fin 13 => ∀ p∈P, ¬ I p w)
let B : S → Finset (Fin 13) := fun L => Finset.univ.filter (fun p : Fin 13 => ∀ w∈L, ¬ I p w)
let Pos := (Finset.univ.filter (fun e : Fin 13 × Fin 13 => I e.1 e.2)).image
  (fun e => (({e.1}, {e.2}) : S × S))
let X : Finset (S × S) := (Finset.univ.filter (fun P : S => P.card ≤ 3 ∧ ¬ ∃ w, ∀ p∈P, I p w)).image (fun P => (P,A P))
let Y : Finset (S × S) := (Finset.univ.filter (fun L : S => L.card ≤ 3 ∧ ¬ ∃ p, ∀ w∈L, I p w)).image (fun L => (B L,L))
let U := Pos ∪ X ∪ Y
let bit := fun (r : S × S) (i : Fin 26) => Fin.addCases (fun p => decide (p∈r.1)) (fun w => decide (w∈r.2)) i
∃ q : Fin 4,
  let j : Fin 26 := if q.val=1 then 1 else if q.val=3 then 14 else 13
  let base := List.ofFn (fun i : Fin 27 => U.filter (fun r =>
    Fin.lastCases (if q.val=0 then bit r 0 && bit r j else bit r 0 || bit r j) (bit r) i = true))
  ∃ L : List (Finset (S × S)), L.length ≤ 62 ∧
    (∀ i : Fin L.length, ∃ a∈base++L.take i.val, ∃ b∈base++L.take i.val,
      L.get i = a ∩ b ∨ L.get i = a ∪ b) ∧ Pos ∈ base++L
) :
  ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  classical
  have compile {α : Type} [DecidableEq α] (n : ℕ)
      (U : Finset α) (x : α → Fin n → Bool) (L : List (Finset α)) :
      let S : List (Finset α) := List.ofFn (fun i : Fin n => U.filter (fun r => x r i = true))
      (∀ i : Fin L.length, ∃ A ∈ S ++ L.take i.val, ∃ B ∈ S ++ L.take i.val,
        L[i.val] = A ∩ B ∨ L[i.val] = A ∪ B) →
      ∃ gs : List Gate, gs.length = L.length ∧ Monotone2 ⟨gs,0⟩ ∧ ReadsBack n ⟨gs,0⟩ ∧
        ∀ r∈U, (Circuit.mk gs 0).wires (List.ofFn (x r)) = (S ++ L).map (fun A => decide (r∈A)) := by
    let S : List (Finset α) := List.ofFn (fun i : Fin n => U.filter (fun r => x r i = true))
    have hS : S.length = n := List.length_ofFn
    change (∀ i : Fin L.length, ∃ A ∈ S ++ L.take i.val, ∃ B ∈ S ++ L.take i.val,
        L[i.val] = A ∩ B ∨ L[i.val] = A ∪ B) → _
    induction L using List.reverseRecOn with
    | nil =>
        intro h
        refine ⟨[],rfl,?_,?_,?_⟩
        · intro g hg
          change g ∈ ([] : List Gate) at hg
          simp at hg
        · intro j hj
          change j<0 at hj
          omega
        · intro r hr
          change List.ofFn (x r) = (S ++ []).map _
          simp only [List.append_nil,S,List.map_ofFn]
          congr 1
          funext i
          change x r i = decide (r ∈ U.filter (fun r => x r i = true))
          simp [Finset.mem_filter,hr]
    | append_singleton T v ih =>
        intro h
        have hT : ∀ i : Fin T.length, ∃ A ∈ S ++ T.take i.val, ∃ B ∈ S ++ T.take i.val,
            T[i.val] = A ∩ B ∨ T[i.val] = A ∪ B := by
          intro i
          have hi : i.val < (T ++ [v]).length  := by simp
          have q := h ⟨i.val,hi⟩
          have te : (T++[v]).take i.val = T.take i.val := List.take_append_of_le_length (Nat.le_of_lt i.isLt)
          change ∃ A ∈ S ++ (T++[v]).take i.val, ∃ B ∈ S ++ (T++[v]).take i.val,
            (T++[v])[i.val] = A ∩ B ∨ (T++[v])[i.val] = A ∪ B at q
          rw [te,List.getElem_append_left i.isLt] at q
          exact q
        obtain ⟨gs,hgs,hm,hr,hval⟩ := ih hT
        have hlast := h ⟨T.length,by simp⟩
        simp only [List.take_left,List.getElem_append_right (Nat.le_refl T.length),Nat.sub_self,List.getElem_cons_zero] at hlast
        obtain ⟨A,hA,B,hB,hv⟩ := hlast
        obtain ⟨a,ha,ea⟩ := List.getElem_of_mem hA
        obtain ⟨b,hb,eb⟩ := List.getElem_of_mem hB
        let op := if v = A ∩ B then GateOp.and else GateOp.or
        have hOp : op = GateOp.and ∨ op = GateOp.or := by
          dsimp [op]; split <;> simp
        let g : Gate := ⟨op,[a,b]⟩
        have a_lt : a < n + gs.length := by simpa [List.length_append,hS,hgs] using ha
        have b_lt : b < n + gs.length := by simpa [List.length_append,hS,hgs] using hb
        refine ⟨gs++[g],by simp [hgs],?_,?_,?_⟩
        · intro t ht
          have h : t ∈ gs ∨ t=g := by simpa using ht
          rcases h with h|rfl
          · exact hm _ h
          · refine ⟨?_,by simp [g]⟩
            simpa [g] using hOp
        · intro j hj i hi
          by_cases hj' : j < gs.length
          · have e : gateAt (Circuit.mk (gs++[g]) 0) j = gateAt (Circuit.mk gs 0) j := by
              change (gs++[g]).getD j ⟨GateOp.or,[]⟩ = gs.getD j ⟨GateOp.or,[]⟩
              simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hj']
            rw [e] at hi
            exact hr j hj' i hi
          · have hj0 : j = gs.length := by simp at hj; omega
            subst j
            have e : gateAt (Circuit.mk (gs++[g]) 0) gs.length = g := by
              change (gs++[g]).getD gs.length ⟨GateOp.or,[]⟩ = g
              simp
            rw [e] at hi
            simp [g] at hi
            rcases hi with rfl|rfl
            · exact a_lt
            · exact b_lt
        · intro r hrU
          let w := (Circuit.mk gs 0).wires (List.ofFn (x r))
          have ew : w = (S++T).map (fun A=>decide (r∈A)) := hval r hrU
          have wa : w.getD a false = decide (r∈A) := by
            rw [ew]
            rw [List.getD_eq_getElem _ _ (by simpa using ha),List.getElem_map,ea]
          have wb : w.getD b false = decide (r∈B) := by
            rw [ew]
            rw [List.getD_eq_getElem _ _ (by simpa using hb),List.getElem_map,eb]
          have stepEq : (Circuit.mk (gs++[g]) 0).wires (List.ofFn (x r)) =
              w ++ [op.eval [w.getD a false,w.getD b false]] := by
            let step := fun (w : List Bool) (t : Gate) =>
              w ++ [t.op.eval (t.inputs.map (fun i=>w.getD i false))]
            change (gs++[g]).foldl step (List.ofFn (x r)) =
              gs.foldl step (List.ofFn (x r)) ++ [op.eval [
                (gs.foldl step (List.ofFn (x r))).getD a false,
                (gs.foldl step (List.ofFn (x r))).getD b false]]
            rw [List.foldl_append]
            rfl
          change _ = (S++(T++[v])).map _
          rw [stepEq,wa,wb,ew,←List.append_assoc]
          simp only [List.map_append,List.map_singleton]
          congr 2
          unfold op
          split
          · rename_i h
            rw [h]
            have ev (a b : Bool) : GateOp.and.eval [a,b] = (a&&b) := by
              cases a <;> cases b <;> rfl
            rw [ev]
            simp [Finset.mem_inter]
          · rename_i h
            have hv' := hv.resolve_left h
            rw [hv']
            have ev (a b : Bool) : GateOp.or.eval [a,b] = (a||b) := by
              cases a <;> cases b <;> rfl
            rw [ev]
            simp [Finset.mem_union]
  
  let D : Finset (Fin 13) := {0,1,3,9}
  let I := fun p w : Fin 13 => ∃ d ∈ D, p=w+d
  let S := Finset (Fin 13)
  let A : S → Finset (Fin 13) := fun P => Finset.univ.filter (fun w : Fin 13 => ∀ p∈P, ¬ I p w)
  let B : S → Finset (Fin 13) := fun L => Finset.univ.filter (fun p : Fin 13 => ∀ w∈L, ¬ I p w)
  let Pos := (Finset.univ.filter (fun e : Fin 13 × Fin 13 => I e.1 e.2)).image
    (fun e => (({e.1}, {e.2}) : S × S))
  let X : Finset (S × S) := (Finset.univ.filter (fun P : S => P.card ≤ 3 ∧ ¬ ∃ w, ∀ p∈P, I p w)).image (fun P => (P,A P))
  let Y : Finset (S × S) := (Finset.univ.filter (fun L : S => L.card ≤ 3 ∧ ¬ ∃ p, ∀ w∈L, I p w)).image (fun L => (B L,L))
  let U := Pos ∪ X ∪ Y
  let bit : (S × S) → Fin 26 → Bool := fun r i => Fin.addCases (motive := fun _ => Bool) (fun p => decide (p∈r.1)) (fun w => decide (w∈r.2)) i
  obtain ⟨q,L,hbudget,hsteps,hout⟩ := witness
  let j : Fin 26 := if q.val=1 then 1 else if q.val=3 then 14 else 13
  let aug : (Fin 26 → Bool) → Fin 27 → Bool := fun y => Fin.lastCases (if q.val=0 then y 0 && y j else y 0 || y j) y
  let x := fun (r : S × S) => aug (bit r)
  let base := List.ofFn (fun i : Fin 27 => U.filter (fun r => x r i = true))
  have hsteps' : ∀ i : Fin L.length, ∃ a∈base++L.take i.val, ∃ b∈base++L.take i.val,
      L[i.val] = a ∩ b ∨ L[i.val] = a ∪ b := hsteps
  obtain ⟨gs,hgs,hm,hr,hwires⟩ := compile 27 U x L hsteps'
  obtain ⟨o,ho,he⟩ := List.getElem_of_mem (show Pos ∈ base++L from hout)
  let C : Circuit := ⟨gs,o⟩
  have hvalue (r : S × S) (hU : r∈U) : circuitFun 27 C (x r) = decide (r∈Pos) := by
    change ((Circuit.mk gs 0).wires (List.ofFn (x r))).getD o false = _
    rw [hwires r hU]
    change ((base++L).map (fun A=>decide (r∈A))).getD o false = _
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ho),List.getElem_map,he]
  have cross : ∀ p w : Fin 13, Fin.castAdd 13 p ≠ Fin.natAdd 13 w := by decide +kernel
  have bit_iff (r : S × S) (k : Fin 26) :
      bit r k=true ↔ (∃ p∈r.1, k=Fin.castAdd 13 p) ∨ (∃ w∈r.2, k=Fin.natAdd 13 w) := by
    refine Fin.addCases (motive := fun k => bit r k=true ↔
      (∃ p∈r.1, k=Fin.castAdd 13 p) ∨ (∃ w∈r.2, k=Fin.natAdd 13 w)) ?_ ?_ k
    · intro p
      rw [show bit r (Fin.castAdd 13 p) = decide (p∈r.1) from Fin.addCases_left _]
      simp only [decide_eq_true_eq,Fin.castAdd_inj]
      constructor
      · intro hp
        exact Or.inl ⟨p,hp,rfl⟩
      · rintro (⟨z,hz,rfl⟩|⟨z,hz,hz'⟩)
        · exact hz
        · exact (cross p z hz').elim
    · intro w
      rw [show bit r (Fin.natAdd 13 w) = decide (w∈r.2) from Fin.addCases_right _]
      simp only [decide_eq_true_eq]
      constructor
      · intro hw
        exact Or.inr ⟨w,hw,rfl⟩
      · rintro (⟨p,hp,he⟩|⟨v,hv,he⟩)
        · exact (cross p w he.symm).elim
        · have hvw : w=v := by
            apply Fin.ext
            have he' := congrArg Fin.val he
            change 13+w.val = 13+v.val at he'
            omega
          rw [hvw]
          exact hv
  refine ⟨q,C,hm,hr,?_,?_⟩
  · change gs.length ≤ 62
    rw [hgs]
    exact hbudget
  dsimp only
  simp only [decide_eq_true_eq]
  change (∀ p w : Fin 13, I p w → circuitFun 27 C (aug (fun k => decide
      (k=Fin.castAdd 13 p ∨ k=Fin.natAdd 13 w))) = true) ∧
    ∀ (P : S), (∀ v∉P, ∃ w, (∀ p∈P, ¬I p w) ∧ I v w) →
      ((¬∃ w, ∀ p∈P, I p w) ∧ ¬∃ p, ∀ w, (∀ z∈P, ¬I z w) → I p w) →
      ∀ (y : Fin 26 → Bool), (∀ k, y k = true ↔ (∃ p∈P, k=Fin.castAdd 13 p) ∨
        (∃ w, k=Fin.natAdd 13 w ∧ (∀ z∈P, ¬I z w))) → circuitFun 27 C (aug y) = false
  constructor
  · intro p w hpw
    let r : S×S := ({p},{w})
    have hPos : r∈Pos := Finset.mem_image.mpr ⟨(p,w),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpw⟩,rfl⟩
    have hU : r∈U := Finset.mem_union_left _ (Finset.mem_union_left _ hPos)
    have heq : bit r = fun k => decide (k=Fin.castAdd 13 p ∨ k=Fin.natAdd 13 w) := by
      funext k
      apply Bool.eq_iff_iff.mpr
      rw [bit_iff]
      change ((∃ z∈({p}:Finset (Fin 13)), k=Fin.castAdd 13 z) ∨
        (∃ z∈({w}:Finset (Fin 13)), k=Fin.natAdd 13 z)) ↔
        decide (k=Fin.castAdd 13 p ∨ k=Fin.natAdd 13 w) = true
      simp only [Finset.mem_singleton,decide_eq_true_eq,exists_eq_left]
    simpa [x,heq,hPos] using hvalue r hU
  · intro P hmax hgen y hy
    have hA (w : Fin 13) : w∈A P ↔ ∀ p∈P, ¬I p w := by simp [A]
    have hBA : B (A P) = P := by
      ext p
      simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hn
        by_contra hp
        obtain ⟨w,hw,hinc⟩ := hmax p hp
        exact hn w ((hA w).mpr hw) hinc
      · intro hp w hw
        exact (hA w).mp hw p hp
    let r : S×S := (P,A P)
    have hU : r∈U := by
      rcases geometry P with hsmall|hsmall
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨P,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsmall,hgen.1⟩,rfl⟩
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        have hnon : ¬∃ p, ∀ w∈A P, I p w := by
          rintro ⟨p,hp⟩
          exact hgen.2 ⟨p,fun w hw => hp w ((hA w).mpr hw)⟩
        exact ⟨A P,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsmall,hnon⟩,by simp only [r,hBA]⟩
    have hn : r∉Pos := by
      intro hm
      obtain ⟨pw,hpw,heq⟩ := Finset.mem_image.mp hm
      have hinc := (Finset.mem_filter.mp hpw).2
      have hp : pw.1 ∈ P := by
        rw [←show ({pw.1} : S) = P from congrArg Prod.fst heq]
        exact Finset.mem_singleton_self _
      have hw : pw.2 ∈ A P := by
        rw [←show ({pw.2} : S) = A P from congrArg Prod.snd heq]
        exact Finset.mem_singleton_self _
      exact (hA _).mp hw _ hp hinc
    have heq : bit r = y := by
      funext k
      apply Bool.eq_iff_iff.mpr
      rw [bit_iff,hy]
      simp only [r]
      constructor
      · rintro (h|⟨w,hw,he⟩)
        · exact Or.inl h
        · exact Or.inr ⟨w,he,(hA w).mp hw⟩
      · rintro (h|⟨w,he,hw⟩)
        · exact Or.inl h
        · exact Or.inr ⟨w,(hA w).mpr hw,he⟩
    simpa [x,heq,hn] using hvalue r hU
