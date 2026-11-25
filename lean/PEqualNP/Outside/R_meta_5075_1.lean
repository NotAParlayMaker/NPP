import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_5075_1
    (packing : ∀ C : Circuit, Monotone2 C → RightOnIncidentPairs singerLines3 C →
      (∀ X Y, IsMaximalFalse singerLines3 X Y → InNoLine singerLines3 X → InNoPencil singerLines3 Y → C.eval (incidenceInput X Y)=false) →
      9≤{i : Fin C.gates.length | (C.gates.get i).op=.and}.ncard)
    (normalize : ∀ C : Circuit,
    let X := Finset (Fin 13) × Finset (Fin 13)
    let raw : Set (Set X) := Set.range (fun p : Fin 13 => {z : X | p∈z.1}) ∪
      Set.range (fun l : Fin 13 => {z : X | l∈z.2})
    let basis := fun (L : List (Set X)) (j : ℕ) => insert Set.univ (raw ∪ {s | s∈L.take j})
    let span := fun (B : Set (Set X)) (Y : Set X) => ∀ x∈Y, ∃ a∈B, x∈a ∧ a⊆Y
    let built := fun (L : List (Set X)) => ∀ i : Fin L.length, ∃ a b : Set X,
      span (basis L i.val) a ∧ span (basis L i.val) b ∧ L[i.val]=a∩b
    Monotone2 C → ∃ L : List (Set X), built L ∧ L.length={i : Fin C.gates.length | (C.gates.get i).op=.and}.ncard ∧
      span (basis L L.length) {z | C.eval (incidenceInput z.1 z.2)=true})
    (finiteCase :
    let X := Finset (Fin 13) × Finset (Fin 13)
    let raw : Set (Set X) := Set.range (fun p : Fin 13 => {z : X | p∈z.1}) ∪
      Set.range (fun l : Fin 13 => {z : X | l∈z.2})
    let basis := fun (L : List (Set X)) (j : ℕ) => insert Set.univ (raw ∪ {s | s∈L.take j})
    let span := fun (B : Set (Set X)) (Y : Set X) => ∀ x∈Y, ∃ a∈B, x∈a ∧ a⊆Y
    let built := fun (L : List (Set X)) => ∀ i : Fin L.length, ∃ a b : Set X,
      span (basis L i.val) a ∧ span (basis L i.val) b ∧ L[i.val]=a∩b
    ∀ (L : List (Set X)) (Y : Set X), 9≤L.length → L.length≤12 → built L → span (basis L L.length) Y →
      (∀ (l : Fin 13) (p : Fin 13), p∈singerLines3 l → ({p},{l})∈Y) →
      ∃ A B, IsMaximalFalse singerLines3 A B ∧ InNoLine singerLines3 A ∧ InNoPencil singerLines3 B ∧ (A,B)∈Y) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → ∃ (x5 : Finset (Fin ((13 : ℕ) + (13 : ℕ)))), (∀ (x6 x7 : Fin (13 : ℕ)), x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ)) → Fin.castAdd (13 : ℕ) x6 ∈ x5 ∨ Fin.natAdd (13 : ℕ) x7 ∈ x5) ∧ x5.card ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro C hm hpos hneg
  let inc := fun p l : Fin 13 => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
  have geom : ∀ p l : Fin 13, p∈singerLines3 l ↔ inc p l := by decide +kernel
  let row := fun (X Y : Finset (Fin 13)) (i : Fin 26) => decide
    ((∃ p∈X,i=Fin.castAdd 13 p) ∨ ∃ l∈Y,i=Fin.natAdd 13 l)
  have lists (X Y : Finset (Fin 13)) : List.ofFn (row X Y)=incidenceInput X Y := by
    have eq : row X Y=Fin.append (fun p : Fin 13 => decide (p∈X)) (fun l : Fin 13 => decide (l∈Y)) := by
      funext i
      refine Fin.addCases (m:=13) (n:=13) ?_ ?_ i
      · intro p
        rw [Fin.append_left]
        have off (l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by intro e; have := congrArg Fin.val e; simp at this; omega
        simp only [row,Fin.castAdd_inj,off,exists_false,and_false,false_or,or_false,exists_const]
        congr 1; apply propext; constructor
        · rintro ⟨w,hw,e⟩; exact (Fin.castAdd_inj.mp e) ▸ hw
        · intro h; exact ⟨p,h,rfl⟩
      · intro l
        change row X Y (Fin.natAdd 13 l)=(Fin.append _ _ (Fin.natAdd 13 l))
        rw [Fin.append_right]
        have off (p : Fin 13) : Fin.natAdd 13 l ≠ Fin.castAdd 13 p := by intro e; have := congrArg Fin.val e; simp at this; omega
        simp only [row,Fin.natAdd_inj,off,exists_false,and_false,false_or,or_false,exists_const]
        congr 1; apply propext; constructor
        · rintro ⟨w,hw,e⟩; exact (Fin.natAdd_injective 13 13 e) ▸ hw
        · intro h; exact ⟨l,h,rfl⟩
    rw [eq,List.ofFn_fin_append]; rfl
  have pos : RightOnIncidentPairs singerLines3 C := by
    intro l p e
    rw [←lists]
    have one : row {p} {l} = fun i => decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l) := by funext i; simp [row]
    rw [one]; exact hpos p l ((geom p l).mp e)
  have neg (X Y) (maximal : IsMaximalFalse singerLines3 X Y) (pl : InNoLine singerLines3 X)
      (ln : InNoPencil singerLines3 Y) : C.eval (incidenceInput X Y)=false := by
    obtain ⟨no,addP,addL⟩ := maximal
    have off (l : Fin 13) : l∈Y ↔ ∀ p∈X, ¬inc p l := by
      constructor
      · exact fun hl p hp e => Finset.disjoint_left.mp (no l hl) ((geom p l).mpr e) hp
      · intro h; by_contra absent; apply addL l absent
        intro k hk; rcases Finset.mem_insert.mp hk with rfl|hk
        · exact Finset.disjoint_left.mpr (fun p e hp => h p hp ((geom p _).mp e))
        · exact no k hk
    have covered (p : Fin 13) (absent : p∉X) : ∃ l, (∀ q∈X, ¬inc q l) ∧ inc p l := by
      by_contra! h
      apply addP p absent
      intro l hl; apply Finset.disjoint_left.mpr; intro q e hq
      rcases Finset.mem_insert.mp hq with rfl|hq
      · exact h l ((off l).mp hl) ((geom _ _).mp e)
      · exact Finset.disjoint_left.mp (no l hl) e hq
    have result := hneg X covered ⟨fun ⟨l,h⟩ => pl l (fun p hp => (geom p l).mpr (h p hp)),
      fun ⟨p,h⟩ => ln p (fun l hl => (geom p l).mpr (h l ((off l).mp hl)))⟩
    have eq : row X Y = fun i : Fin 26 => decide ((∃ p∈X,i=Fin.castAdd 13 p) ∨
        ∃ l, i=Fin.natAdd 13 l ∧ ∀ p∈X, ¬inc p l) := by
      funext i
      simp only [row,decide_eq_decide]
      exact or_congr Iff.rfl (exists_congr (fun l => by rw [←off l]; exact and_comm))
    rw [←lists,eq]
    exact result
  obtain ⟨L,built,len,out⟩ := normalize C hm
  have floor := packing C hm pos neg
  have large : 13≤L.length := by
    by_contra! small
    obtain ⟨A,B,hMax,pl,ln,bad⟩ := finiteCase L {z | C.eval (incidenceInput z.1 z.2)=true}
      (len ▸ floor) (by omega) built (by simpa only [List.take_length] using out) (fun l p hp => pos l p hp)
    change C.eval (incidenceInput A B)=true at bad
    have h := neg A B hMax pl ln
    rw [h] at bad
    contradiction
  let T := Finset.univ.image (Fin.castAdd 13 : Fin 13→Fin 26)
  exact ⟨T,fun p _ _ => Or.inl (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩),
    (show T.card≤13 by simpa [T] using Finset.card_image_le (f:=Fin.castAdd 13) (s:=(Finset.univ : Finset (Fin 13)))).trans (len ▸ large)⟩
