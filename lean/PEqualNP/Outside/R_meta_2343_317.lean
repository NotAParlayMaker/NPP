import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2343_317
  (sensitive :
let L := PEqualNP.HeptadCover.singerLines3
let Qs := PEqualNP.HeptadCover.quadrangles L
let pos := fun (p l : Fin 13) => PEqualNP.GenericRejection.incidenceInput {p} {l}
let neg := fun (Q : Finset (Fin 13)) => PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines L Q)
∀ (F : List Bool → Bool), (∀ x y : List Bool, x.length=26 → y.length=26 →
  (∀ i : ℕ, x.getD i false = true → y.getD i false = true) → F x = true → F y = true) →
  (∀ p l, p∈L l → F (pos p l)=true) → (∀ Q ∈ Qs, F (neg Q)=false) →
  ∃ T : Finset (Finset (Fin 13)), T ⊆ Qs ∧ T.card = 234 ∧ ∀ Q ∈ T, 19 ≤ {i : Fin 26 | F (neg Q) = false ∧
    F (List.ofFn fun j : Fin 26 => (neg Q).getD j.val false || decide (j=i)) = true}.ncard)
  (charge :
∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ops : List ℕ) (x : List Bool),
  PEqualNP.MetaComplexity.Monotone2 C → ops.length ≤ 2 → x.length = 26 →
  (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 27 + i.val) →
  let extend (u : List Bool) := u ++ [ops.any fun k => u.getD k false]
  let V (u : List Bool) (w : ℕ) := (C.wires (extend u)).getD w false
  let H (w : ℕ) := {i : Fin 26 | V x w = false ∧
    V (List.ofFn fun j : Fin 26 => x.getD j.val false || decide (j = i)) w = true}
  19 ≤ (H C.output).ncard →
  17 ≤ {j : Fin C.size | (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    1 < (H (27+j.val)).ncard ∧ ∀ k < 27+j.val, ¬ H (27+j.val) ⊆ H k}.ncard)
  (hard :
let L := PEqualNP.HeptadCover.singerLines3
let Qs := PEqualNP.HeptadCover.quadrangles L
let pos := fun (p l : Fin 13) => PEqualNP.GenericRejection.incidenceInput {p} {l}
let neg := fun (Q : Finset (Fin 13)) => PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines L Q)
∀ (C : Circuit) (ops : List ℕ),
  let V (u : List Bool) (w : ℕ) := (C.wires (u ++ [ops.any fun k => u.getD k false])).getD w false
  let H (Q : Finset (Fin 13)) (w : ℕ) := {i : Fin 26 | V (neg Q) w = false ∧
    V (List.ofFn fun j : Fin 26 => (neg Q).getD j.val false || decide (j=i)) w = true}
  ops.length≤2 → Monotone2 C → (∀ i : Fin C.gates.length, ∀ k ∈ (C.gates.get i).inputs, k < 27+i.val) →
  (∀ p l, p∈L l → V (pos p l) C.output=true) → (∀ Q ∈ Qs, V (neg Q) C.output=false) →
  (∀ t : ℕ, t ≤ 64 → 3978 ≤ 62*t + 234*{j : Fin C.size |
    (C.gates.get j).op = GateOp.or ∧ t <
      {Q : Finset (Fin 13) | Q ∈ Qs ∧ ∀ k < 27+j.val, ¬ H Q (27+j.val) ⊆ H Q k}.ncard}.ncard) → 63 ≤ C.size)
 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  classical
  intro C ops hl mono back S Pair Neg Quad ext good safe
  let L := PEqualNP.HeptadCover.singerLines3
  let Qs := PEqualNP.HeptadCover.quadrangles L
  let pos := fun (p l : Fin 13) => PEqualNP.GenericRejection.incidenceInput {p} {l}
  let neg := fun Q => PEqualNP.GenericRejection.incidenceInput Q (PEqualNP.HeptadCover.missLines L Q)
  let V (u : List Bool) (w : ℕ) := (C.wires (ext u)).getD w false
  let H (Q : Finset (Fin 13)) (w : ℕ) := {i : Fin 26 | V (neg Q) w = false ∧
    V (List.ofFn fun j : Fin 26 => (neg Q).getD j.val false || decide (j=i)) w = true}
  have inc : ∀ p l : Fin 13, p∈L l ↔ p-l∈S := by decide +kernel
  have rowForm (X Y : Finset (Fin 13)) : PEqualNP.GenericRejection.incidenceInput X Y =
      List.ofFn (fun p : Fin 13 => decide (p ∈ X)) ++ List.ofFn (fun l : Fin 13 => decide (l∈Y)) := rfl
  have missForm (Q : Finset (Fin 13)) : PEqualNP.HeptadCover.missLines L Q =
      Finset.univ.filter (fun l => Disjoint (L l) Q) := rfl
  have pg (p l : Fin 13) (hi : p∈L l) : V (pos p l) C.output=true := by
    have row : pos p l = Pair p l := by simp [pos,Pair,rowForm]
    rw [row]
    exact good p l ((inc p l).mp hi)
  have ng (Q : Finset (Fin 13)) (hQ : Q∈Qs) : V (neg Q) C.output=false := by
    have miss (l:Fin 13) : l ∈ PEqualNP.HeptadCover.missLines L Q ↔ ∀ p∈Q, p-l∉S := by
      simp only [missForm,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.disjoint_left]
      constructor
      · intro h p hp he; exact h ((inc p l).mpr he) hp
      · intro h p he hp; exact h p hp ((inc p l).mp he)
    have row : neg Q = Neg Q := by
      simp [neg,Neg,rowForm,miss]
    rw [row]
    apply safe Q
    obtain ⟨hcQ,hn⟩ := Finset.mem_filter.mp hQ
    refine ⟨(Finset.mem_powersetCard.mp hcQ).2,?_⟩
    intro l
    have hf : Q.filter (fun p => p-l∈S) = Q ∩ L l := by
      ext p; simp [inc]
    rw [hf]; exact hn l
  have step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      g.op.eval (g.inputs.map fun i => u.getD i false) = true →
        g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
    have ae (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
    have oe (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
    rcases hop with hop | hop
    · simp only [hop, ae, List.all_eq_true, List.mem_map, id_eq]
      intro hu b hb
      obtain ⟨i, hi, rfl⟩ := hb
      exact h i (hu _ ⟨i, hi, rfl⟩)
    · simp only [hop, oe, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      exact ⟨v.getD i false, ⟨i, hi, rfl⟩, h i hb⟩
  
  have wires_mono (gs : List Gate)
      (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (u v : List Bool) (hlen : u.length = v.length)
      (h : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (Circuit.wires ⟨gs, 0⟩ u).getD i false = true →
        (Circuit.wires ⟨gs, 0⟩ v).getD i false = true := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      let a := g.op.eval (g.inputs.map fun i => u.getD i false)
      let b := g.op.eval (g.inputs.map fun i => v.getD i false)
      change ∀ i, (Circuit.wires ⟨gs, 0⟩ (u ++ [a])).getD i false = true →
        (Circuit.wires ⟨gs, 0⟩ (v ++ [b])).getD i false = true
      apply ih (fun k hk => hgs k (List.mem_cons_of_mem g hk)) _ _ (by simp [hlen])
      intro i hi
      rcases lt_trichotomy i u.length with hlt | rfl | hgt
      · have hlt' : i < v.length := by omega
        simpa only [List.getD_append _ _ _ _ hlt'] using h i
          (by simpa only [List.getD_append _ _ _ _ hlt] using hi)
      · have ha : a = true := by simpa [List.getD_eq_getElem?_getD] using hi
        have hb : b = true := step_mono g (hgs g List.mem_cons_self) u v h ha
        simpa [hlen, List.getD_eq_getElem?_getD] using hb
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact Bool.noConfusion hi
  have mext (x y : List Bool) (hx : x.length=26) (hy : y.length=26)
      (xy : ∀ i : ℕ, x.getD i false=true → y.getD i false=true) :
      V x C.output=true → V y C.output=true := by
    apply wires_mono C.gates (fun g hg => (mono g hg).1) (ext x) (ext y) (by simp [ext,hx,hy]) _ C.output
    intro i hi
    by_cases h : i<26
    · simpa only [ext,List.getD_append _ _ _ _ (show i<y.length by omega)] using
        xy i (by simpa only [ext,List.getD_append _ _ _ _ (show i<x.length by omega)] using hi)
    by_cases h26 : i=26
    · subst i
      have src : ops.any (fun k => x.getD k false)=true := by simpa [ext,List.getD_eq_getElem?_getD,hx] using hi
      obtain ⟨k,hk,hv⟩ := List.any_eq_true.mp src
      have res := List.any_eq_true.mpr (show ∃ k∈ops, y.getD k false=true from ⟨_,hk,xy k hv⟩)
      simpa [ext,List.getD_eq_getElem?_getD,hy] using res
    · rw [List.getD_eq_default _ _ (by simp [ext,hx]; omega)] at hi
      exact Bool.false_ne_true hi |>.elim
  obtain ⟨T,hT,nQ,hs⟩ := sensitive (fun u => V u C.output) mext pg ng
  let fresh (j : Fin C.size) (Q : Finset (Fin 13)) := (C.gates.get j).op=GateOp.or ∧
    1 < (H Q (27+j.val)).ncard ∧ ∀ k < 27+j.val, ¬ H Q (27+j.val) ⊆ H Q k
  have per (Q : Finset (Fin 13)) (hQ : Q∈T) : 17 ≤ (Finset.univ.filter fun j : Fin C.size => fresh j Q).card := by
    have z := charge C ops (neg Q) mono hl (by simp [neg,rowForm]) back (hs Q hQ)
    change 17 ≤ {j : Fin C.size | fresh j Q}.ncard at z
    simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_ofPred] using z
  by_contra! small
  apply Nat.not_lt.mpr (hard C ops hl mono back pg ng ?_) small
  have budget : 234*17 ≤ ∑ j : Fin C.size, (T.filter fun Q => fresh j Q).card := by
    calc
      _ = ∑ _Q ∈ T, 17 := by simp [nQ]
      _ ≤ ∑ Q ∈ T, (Finset.univ.filter fun j : Fin C.size => fresh j Q).card :=
        Finset.sum_le_sum per
      _ = _ := by simp only [Finset.card_filter]; exact Finset.sum_comm
  intro t ht
  let live (j : Fin C.size) := {Q : Finset (Fin 13) | Q ∈ Qs ∧ ∀ k < 27+j.val, ¬H Q (27+j.val) ⊆ H Q k}
  let W := {j : Fin C.size | (C.gates.get j).op = GateOp.or ∧ t < (live j).ncard}
  have bound (j : Fin C.size) : (T.filter fun Q => fresh j Q).card ≤ t+(if j ∈ W then 234 else 0) := by
    by_cases h : j ∈ W
    · simp only [h,ite_true]
      have h' := Finset.card_le_card (Finset.filter_subset (fun Q => fresh j Q) T)
      omega
    · simp only [h,ite_false,Nat.add_zero]
      by_contra! over
      obtain ⟨Q,hm⟩ := Finset.card_pos.mp (show 0 < (T.filter fun Q => fresh j Q).card by omega)
      apply h
      refine ⟨(Finset.mem_filter.mp hm).2.1,over.trans_le ?_⟩
      rw [Set.ncard_eq_toFinset_card']
      apply Finset.card_le_card
      intro R hr
      obtain ⟨hm,hf⟩ := Finset.mem_filter.mp hr
      exact Set.mem_toFinset.mpr ⟨hT hm,hf.2.2⟩
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => bound j)
  rw [Finset.sum_add_distrib,← Finset.sum_filter] at sum
  change 3978 ≤ 62*t+234*W.ncard
  have nle := Nat.mul_le_mul_right t (show C.size ≤ 62 by omega)
  simpa [Set.ncard_eq_toFinset_card',Nat.mul_comm] using
    (show 3978 ≤ 62*t+W.ncard*234 by
      have eq : W.ncard = (Finset.univ.filter fun j => j ∈ W).card := by rw [Set.ncard_eq_toFinset_card']; simp
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,← eq] at sum
      omega)
