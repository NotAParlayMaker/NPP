import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5056_1
    (exposed : ∀ (C : Circuit), FanInTwo C → C.size=8 → (∀ g∈C.gates, g.op≠.not) →
    (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false=(x 0||x 2)) →
    let f := fun (x : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun t =>
        x (Fin.ofNat 9 (t/10)) && x (Fin.ofNat 9 (t%10))
    ∀ S : Finset ℕ, ¬(0∈S ∧ 2∈S) →
    (∀ x y, (∀ j∈S, (C.wires (List.ofFn x)).getD j false=(C.wires (List.ofFn y)).getD j false) → f x=f y) →
    ∃ i∈S, i<9 ∧ i≠0 ∧ i≠2)
    (residual : ∀ (gs : List Gate), gs.length=7 →
    (∀ g∈gs, g.inputs.length≤2 ∧ (g.op=.and ∨ g.op=.or)) →
    let f := fun (x : Fin 9 → Bool) =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun t =>
        x (Fin.ofNat 9 (t/10)) && x (Fin.ofNat 9 (t%10))
    let h := fun (x : Fin 9 → Bool) => x 0 || x 2
    let V := fun x => gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun j => w.getD j false)])
      (List.ofFn x++[h x])
    ∀ (i : Fin 9), i.val≠0 → i.val≠2 → ∀ T ⊆ Finset.range 17, T.card=4 → 9∉T → i.val∉T →
      ¬(0∈T ∧ 2∈T) → ∃ (b : Bool) (p q : Fin 8 → Bool),
      let x : Fin 9 → Bool := i.insertNth b p
      let y : Fin 9 → Bool := i.insertNth b q
      h x=h y ∧ f x≠f y ∧ ∀ j∈T, (V x).getD j false=(V y).getD j false)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (8 : ℕ) →       (∀ x4 ∈ x1.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →         (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →           have x6 : ℕ → ℕ → Prop := fun (x6 x7 : ℕ) => Relation.ReflTransGen (fun (x8 x9 : ℕ) => (10 : ℕ) ≤ x9 ∧ x9 < (17 : ℕ) ∧ x8 < x9 ∧ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x9 - (9 : ℕ))).inputs) x6 x7;           have x7 : (Fin (9 : ℕ) → Bool) → Bool := fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)));           ∀ x8 ⊆ Finset.range (17 : ℕ), x8.card = (6 : ℕ) → (9 : ℕ) ∈ x8 → ¬((0 : ℕ) ∈ x8 ∧ (2 : ℕ) ∈ x8) → (∀ x13 < (9 : ℕ), ∃ x15 ∈ x8, x6 x13 x15) → (∃ (x14 : Finset ℕ), (4 : ℕ) ≤ x14.card ∧ ∀ x15 ∈ x14, (10 : ℕ) ≤ x15 ∧ x15 < (17 : ℕ) ∧ ∃ x17 ∈ x8, x6 x15 x17) → ∃ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ) → Bool), x7 x15 ≠ x7 x16 ∧ ∀ x17 ∈ x8, (x1.wires (List.ofFn x15)).getD x17 Bool.false = (x1.wires (List.ofFn x16)).getD x17 Bool.false := by
  intro C fan size nn seed
  dsimp only
  intro S bounded width nine special _ _
  classical
  let adv := fun (w : List Bool) (g : Gate) => w++[g.op.eval (g.inputs.map fun j => w.getD j false)]
  have keepPrefix (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j<w.length) :
      (gs.foldl adv w).getD j false=w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (adv w g) (by simp [adv]; omega)]
      exact List.getD_append _ _ _ _ hj
  by_contra empty
  obtain ⟨v,observed,vr,v0,v2⟩ := exposed C fan size nn seed S special
    (fun x y eq => not_not.mp (fun ne => empty ⟨x,y,ne,eq⟩))
  let i : Fin 9 := ⟨v,vr⟩
  let T := (S.erase v).erase 9
  have diff : v≠9 := by omega
  have contains (j) (h : j∈T) : j∈S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  have nine' : 9∈S.erase v := Finset.mem_erase.mpr ⟨Ne.symm diff,nine⟩
  have four : T.card=4 := by simp [T,Finset.card_erase_of_mem nine',Finset.card_erase_of_mem observed,width]
  have hT : ∀ j∈S, j≠v → j≠9 → j∈T := fun j hj hv h9 => Finset.mem_erase.mpr ⟨h9,Finset.mem_erase.mpr ⟨hv,hj⟩⟩
  obtain ⟨gates,o⟩ := C
  cases gates with
  | nil => change (0 : ℕ)=8 at size; omega
  | cons g gs =>
    have len : gs.length=7 := by
      change gs.length+1=8 at size
      omega
    have legal (a : Gate) (ha : a∈gs) : a.inputs.length≤2 ∧ (a.op=.and ∨ a.op=.or) := by
      have m : a∈(Circuit.mk (g::gs) o).gates := List.mem_cons_of_mem g ha
      obtain ⟨op,arity⟩ := fan a m
      exact ⟨arity,by simpa [nn a m] using op⟩
    have val (x : Fin 9 → Bool) : (Circuit.mk (g::gs) o).wires (List.ofFn x) =
        gs.foldl adv (List.ofFn x ++ [x 0 || x 2]) := by
      let u := g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)
      have seen := seed x
      change (gs.foldl adv (List.ofFn x++[u])).getD 9 false = _ at seen
      rw [keepPrefix _ _ _ (by simp)] at seen
      have hu : u=(x 0||x 2) := by simpa [List.getD_eq_getElem?_getD] using seen
      change gs.foldl adv (List.ofFn x++[u])=_
      rw [hu]
    obtain ⟨b,p,q,h,ne,same⟩ := residual gs len legal i v0 v2 T
      (fun _ hj => bounded (contains _ hj)) four (Finset.notMem_erase 9 (S.erase v))
      (fun hx => Finset.notMem_erase v S (Finset.mem_of_mem_erase hx))
      (fun hh => special ⟨contains _ hh.1,contains _ hh.2⟩)
    let x : Fin 9 → Bool := i.insertNth b p
    let y : Fin 9 → Bool := i.insertNth b q
    apply empty
    refine ⟨x,y,ne,?_⟩
    intro j hj
    by_cases eq9 : j=9
    · subst j; rw [seed x,seed y]; exact h
    by_cases eqv : j=v
    · subst j
      have rawval (z : Fin 9 → Bool) : ((Circuit.mk (g::gs) o).wires (List.ofFn z)).getD v false=z i := by
        change ((g::gs).foldl adv (List.ofFn z)).getD v false=_
        rw [keepPrefix _ _ _ (by simpa using vr)]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos vr,Option.getD_some,i]
      rw [rawval x,rawval y]
      simp [x,y]
    · rw [val x,val y]
      exact same j (hT j hj eqv eq9)
