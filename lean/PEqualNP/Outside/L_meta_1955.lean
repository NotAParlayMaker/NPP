import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1955_aux
open scoped BigOperators

lemma point_degree {q N : ℕ} (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (L : Fin N → Finset (Fin N)) (hc : ∀ i, (L i).card=q+1)
    (hp : ∀ p r, p≠r → ∃! i, p ∈ L i ∧ r ∈ L i)
    (p : Fin N) : (Finset.univ.filter fun i => p ∈ L i).card=q+1 := by
  classical
  let J := Finset.univ.filter fun i => p ∈ L i
  have hd : (J : Set _).PairwiseDisjoint (fun i => (L i).erase p) := by
    intro i him j hjm hij
    apply Finset.disjoint_left.mpr
    intro r hri hrj
    have hir := Finset.mem_erase.mp hri
    have hjr := Finset.mem_erase.mp hrj
    have hpi : p ∈ L i := (Finset.mem_filter.mp him).2
    have hpj : p ∈ L j := (Finset.mem_filter.mp hjm).2
    obtain ⟨l,_,hu⟩ := hp p r (Ne.symm hir.1)
    exact hij ((hu i ⟨hpi,hir.2⟩).trans (hu j ⟨hpj,hjr.2⟩).symm)
  have hunion : J.biUnion (fun i => (L i).erase p) = Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨i,_,hr,_⟩; exact hr
    · intro hr
      obtain ⟨i,⟨hpi,hri⟩,_⟩ := hp p r (Ne.symm hr)
      exact ⟨i,by simp [J,hpi],hr,hri⟩
  have hs : ∑ i ∈ J, ((L i).erase p).card = J.card*q := by
    calc
      _ = ∑ _i ∈ J, q := Finset.sum_congr rfl (by
        intro i him
        have hpi : p ∈ L i := (Finset.mem_filter.mp him).2
        rw [Finset.card_erase_of_mem hpi,hc]; omega)
      _ = _ := by simp
  have he : J.card*q = q*(q+1) := by
    rw [←hs,←Finset.card_biUnion hd,hunion]
    simp only [Finset.card_erase_of_mem (Finset.mem_univ p),Finset.card_univ,Fintype.card_fin,hN]
    simp only [Nat.add_sub_cancel]
    ring
  apply Nat.eq_of_mul_eq_mul_right (show 0<q by omega)
  simpa [Nat.mul_comm] using he

lemma ncard_sum {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    Set.ncard {i | P i} = ∑ i : Fin N, if P i then 1 else 0 := by
  classical
  have he : {i | P i} = (↑(Finset.univ.filter P) : Set (Fin N)) := by ext; simp
  rw [he,Set.ncard_coe_finset]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]

lemma ncard_swap {N : ℕ} (R : Fin N → Fin N → Prop) :
    ∑ j : Fin N, Set.ncard {i | R i j} = ∑ i : Fin N, Set.ncard {j | R i j} := by
  classical
  simp_rw [ncard_sum]
  exact Finset.sum_comm

lemma regular_cover {N d : ℕ} (hd : 0<d) (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hrow : ∀ p, (Finset.univ.filter fun l => I p l).card=d)
    (hcol : ∀ l, (Finset.univ.filter fun p => I p l).card=d)
    (A B : Finset (Fin N))
    (hcover : ∀ p l, I p l → p∈A ∨ l∈B) : N ≤ A.card+B.card := by
  classical
  let e : Fin N → Fin N → ℕ := fun p l => if I p l then 1 else 0
  have hr p : ∑ l, e p l = d := by
    simpa only [e,Finset.card_eq_sum_ones,Finset.sum_filter] using hrow p
  have hc l : ∑ p, e p l = d := by
    simpa only [e,Finset.card_eq_sum_ones,Finset.sum_filter] using hcol l
  have ht : ∑ p : Fin N, ∑ l : Fin N, e p l = N*d := by simp [hr]
  have hbound : ∑ p : Fin N, ∑ l : Fin N, e p l ≤
      ∑ p : Fin N, ∑ l : Fin N,
        ((if p∈A then e p l else 0)+(if l∈B then e p l else 0)) := by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro l _
    by_cases hi : I p l
    · rcases hcover p l hi with hp | hl
      · simp [hp,e,hi]
      · simp [hl,e,hi]
    · simp [e,hi]
  have hpa : (∑ p : Fin N, ∑ l : Fin N, if p∈A then e p l else 0) = A.card*d := by
    calc
      _ = ∑ p : Fin N, if p∈A then d else 0 := Finset.sum_congr rfl (by
        intro p _; by_cases hp : p∈A <;> simp [hp,hr])
      _ = _ := by simp [←Finset.sum_filter]
  have hlb : (∑ p : Fin N, ∑ l : Fin N, if l∈B then e p l else 0) = B.card*d := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ l : Fin N, if l∈B then d else 0 := Finset.sum_congr rfl (by
        intro l _; by_cases hl : l∈B <;> simp [hl,hc])
      _ = _ := by simp [←Finset.sum_filter]
  simp_rw [Finset.sum_add_distrib] at hbound
  rw [ht,hpa,hlb] at hbound
  nlinarith

lemma split_count {N k q : ℕ} (hk : k≤q) (I A B : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hdegree : ∀ p, (Finset.univ.filter fun l => I p l).card=q+1)
    (hcover : ∀ p l, I p l → A p l ∨ B p l) :
    (k+1)*N ≤ (∑ l : Fin N, Set.ncard {p | A p l}) +
      ∑ p : Fin N, min (k+1) (Set.ncard {l | B p l}) := by
  classical
  have per p : k+1 ≤ Set.ncard {l | A p l}+min (k+1) (Set.ncard {l | B p l}) := by
    have hle : (Finset.univ.filter fun l => I p l).card ≤
        (Finset.univ.filter fun l => A p l).card+(Finset.univ.filter fun l => B p l).card := by
      apply (Finset.card_le_card (show (Finset.univ.filter fun l => I p l) ⊆
          (Finset.univ.filter fun l => A p l) ∪ (Finset.univ.filter fun l => B p l) from ?_)).trans
        (Finset.card_union_le _ _)
      intro l hl
      rcases hcover p l (Finset.mem_filter.mp hl).2 with ha | hb
      · simp [ha]
      · simp [hb]
    have ca : (Finset.univ.filter fun l => A p l).card = Set.ncard {l | A p l} := by
      rw [ncard_sum]; simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    have cb : (Finset.univ.filter fun l => B p l).card = Set.ncard {l | B p l} := by
      rw [ncard_sum]; simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [hdegree,ca,cb] at hle
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => per p)
  rw [ncard_swap A,←Finset.sum_add_distrib]
  simpa [Nat.mul_comm] using hs

end PEqualNP.Outside.L_meta_1955_aux

open PEqualNP.Outside.L_meta_1955_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_1955 : (∀ (N260 k260 t260 : ℕ) (I260 : Fin N260 → Fin N260 → Prop) [DecidableRel I260] (C260 : PEqualNP.CircuitLowerBounds.Circuit), (∀ p260 p260x1 w260 w260x1 : Fin N260, p260 ≠ p260x1 → w260 ≠ w260x1 → I260 p260 w260 → I260 p260x1 w260 → I260 p260 w260x1 → I260 p260x1 w260x1 → False) → (∃ p260x2 w260x2 : Fin N260, I260 p260x2 w260x2) → 1 ≤ k260 → ((∀ g260 ∈ C260.gates, (g260.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g260.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g260.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N260 + N260) C260) → (∀ j260 < C260.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260 0 = 0) ∨ (∀ h260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260 0 = 0)) → (∀ p260x3 w260x3 : Fin N260, I260 p260x3 w260x3 → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append (fun a260 : Fin N260 => decide (a260 = p260x3)) (fun a260x1 : Fin N260 => decide (a260x1 = w260x3))) = true) → (∀ x260 y260 : Fin N260 → Bool, (Finset.univ.filter (fun l260 : Fin N260 => y260 l260 = true)).card ≤ k260 → (¬ ∃ p260x4 w260x4 : Fin N260, I260 p260x4 w260x4 ∧ x260 p260x4 = true ∧ y260 w260x4 = true) → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append x260 y260) = false) → (∀ A260 B260 : Finset (Fin N260), (∀ p260x5 w260x5 : Fin N260, I260 p260x5 w260x5 → p260x5 ∈ A260 ∨ w260x5 ∈ B260) → t260 ≤ A260.card + B260.card) → ∀ mixed260 : ℕ → Prop, mixed260 = (fun i260x1 : ℕ => 0 < (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD i260x1 0 ∧ 0 < (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x1 0) → ∀ cone260 : ℕ → Prop, cone260 = (fun j260x1 : ℕ => j260x1 < C260.gates.length ∧ mixed260 (N260 + N260 + j260x1) ∧ Relation.ReflTransGen (fun a260x2 b260 : ℕ => a260x2 < b260 ∧ ∃ f260 : Fin C260.gates.length, b260 = N260 + N260 + f260.val ∧ a260x2 ∈ (C260.gates.get f260).inputs) (N260 + N260 + j260x1) C260.output) → ∀ gok260 : (Fin N260 → Bool) → ℕ → Prop, gok260 = (fun (x260x1 : Fin N260 → Bool) (j260x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i260x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x2 0 = 0 ∧ (C260.wires (List.ofFn (Fin.append x260x1 (fun u260 : Fin N260 => false)))).getD i260x2 false = true) → ∀ step260 : (Fin N260 → Bool) → ℕ → ℕ → Prop, step260 = (fun (x260x2 : Fin N260 → Bool) (j260x3 j260x4 : ℕ) => cone260 j260x4 ∧ N260 + N260 + j260x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x4).inputs ∧ gok260 x260x2 j260x4) → ∀ lvx260 : (Fin N260 → Bool) → ℕ → Prop, lvx260 = (fun (x260x3 : Fin N260 → Bool) (j260x5 : ℕ) => cone260 j260x5 ∧ gok260 x260x3 j260x5 ∧ ∃ j260x6 : ℕ, N260 + N260 + j260x6 = C260.output ∧ Relation.ReflTransGen (step260 x260x3) j260x5 j260x6) → ∀ slot260 : ℕ → ℕ → Prop, slot260 = (fun h260x1 j260x7 : ℕ => cone260 j260x7 ∧ h260x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x7).inputs ∧ (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260x1 0 = 0) → ∀ ap260 : ℕ → Fin N260 → Prop, ap260 = (fun (h260x2 : ℕ) (p260x6 : Fin N260) => ∃ j260x8 : ℕ, slot260 h260x2 j260x8 ∧ lvx260 (fun a260x3 : Fin N260 => decide (a260x3 = p260x6)) j260x8) → ∀ lh260 : ℕ → Fin N260 → Prop, lh260 = (fun (h260x3 : ℕ) (w260x6 : Fin N260) => (C260.wires (List.ofFn (Fin.append (fun u260x1 : Fin N260 => false) (fun a260x4 : Fin N260 => decide (a260x4 = w260x6))))).getD h260x3 false = true) → ∀ lpw260 : ℕ → Fin N260 → Prop, lpw260 = (fun (h260x4 : ℕ) (w260x7 : Fin N260) => ∀ w260x8 : Fin N260, lh260 h260x4 w260x8 ↔ w260x8 = w260x7) → ∀ ppw260 : ℕ → Fin N260 → Prop, ppw260 = (fun (h260x5 : ℕ) (p260x7 : Fin N260) => (∃ w260x9 w260x10 : Fin N260, w260x9 ≠ w260x10 ∧ lh260 h260x5 w260x9 ∧ lh260 h260x5 w260x10) ∧ ∀ p260x8 : Fin N260, ap260 h260x5 p260x8 ↔ p260x8 = p260x7) → ∀ lps260 : Fin N260 → Fin N260 → Prop, lps260 = (fun p260x9 w260x11 : Fin N260 => ∃ h260x6 : ℕ, lpw260 h260x6 w260x11 ∧ ap260 h260x6 p260x9) → ∀ pps260 : Fin N260 → Fin N260 → Prop, pps260 = (fun p260x10 w260x12 : Fin N260 => ∃ h260x7 : ℕ, ppw260 h260x7 p260x10 ∧ lh260 h260x7 w260x12) → ∑ w260x13 : Fin N260, Set.ncard {p260x11 : Fin N260 | lps260 p260x11 w260x13} + ∑ p260x12 : Fin N260, min (k260 + 1) (Set.ncard {w260x14 : Fin N260 | pps260 p260x12 w260x14}) + t260 ≤ C260.size + 1) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → ∀ (q261 N261 k261 : ℕ) (I261 : Fin N261 → Fin N261 → Prop) [DecidableRel I261] (C261 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q261 → N261 = q261 ^ 2 + q261 + 1 → (∀ l261 : Fin N261, (Finset.univ.filter (fun p261 => I261 p261 l261)).card = q261 + 1) → (∀ pa261 pb261 : Fin N261, pa261 ≠ pb261 → ∃! lb261 : Fin N261, I261 pa261 lb261 ∧ I261 pb261 lb261) → 1 ≤ k261 → k261 ≤ q261 → ((∀ g261 ∈ C261.gates, (g261.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g261.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g261.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N261 + N261) C261) → (∀ j261 < C261.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C261 j261).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i261 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C261 j261).inputs, (C261.lineDegrees (N261 + N261) (Finset.Ico N261 (N261 + N261))).getD i261 0 = 0) ∨ (∀ h261 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C261 j261).inputs, (C261.lineDegrees (N261 + N261) (Finset.range N261)).getD h261 0 = 0)) → (∀ p261x1 l261x1 : Fin N261, I261 p261x1 l261x1 → PEqualNP.MetaComplexity.circuitFun (N261 + N261) C261 (fun i261x1 => decide (i261x1 = Fin.castAdd N261 p261x1 ∨ i261x1 = Fin.natAdd N261 l261x1)) = true) → (∀ z261 : Fin (N261 + N261) → Bool, (Finset.univ.filter (fun l261x2 : Fin N261 => z261 (Fin.natAdd N261 l261x2) = true)).card ≤ k261 → (¬ ∃ p261x2 l261x3 : Fin N261, I261 p261x2 l261x3 ∧ z261 (Fin.castAdd N261 p261x2) = true ∧ z261 (Fin.natAdd N261 l261x3) = true) → PEqualNP.MetaComplexity.circuitFun (N261 + N261) C261 z261 = false) → (k261 + 2) * N261 ≤ C261.size + 1 := by

  classical
  intro theoremN live q N k I inst C hq hN hlines huniq hk hkq hC hkm haccept hreject
  have hNpos : 0<N := by omega
  have hrow : ∀ p, (Finset.univ.filter fun l => I p l).card=q+1 := by
    intro p
    have hd := point_degree hq hN (fun l => Finset.univ.filter fun p => I p l) hlines
      (by intro p r hpr; simpa using huniq p r hpr) p
    simpa using hd
  have hfour : ∀ p p' w w' : Fin N, p≠p' → w≠w' →
      I p w → I p' w → I p w' → I p' w' → False := by
    intro p p' w w' hpp hww h1 h2 h3 h4
    obtain ⟨l,_,hu⟩ := huniq p p' hpp
    exact hww ((hu w ⟨h1,h2⟩).trans (hu w' ⟨h3,h4⟩).symm)
  have hedge : ∃ p w, I p w := by
    let w : Fin N := ⟨0,hNpos⟩
    have hc : 0 < (Finset.univ.filter fun p => I p w).card := by rw [hlines]; omega
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hc
    exact ⟨p,w,(Finset.mem_filter.mp hp).2⟩
  have accept' : ∀ p w : Fin N, I p w →
      PEqualNP.MetaComplexity.circuitFun (N+N) C
        (Fin.append (fun a => decide (a=p)) (fun a => decide (a=w))) = true := by
    intro p w hi
    have he : Fin.append (fun a : Fin N => decide (a=p)) (fun a : Fin N => decide (a=w)) =
        (fun i : Fin (N+N) => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N w)) := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro a
        apply Bool.eq_iff_iff.mpr
        simp only [Fin.append_left,decide_eq_true_eq,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]
        omega
      · intro a
        apply Bool.eq_iff_iff.mpr
        simp only [Fin.append_right,decide_eq_true_eq,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]
        omega
    rw [he]
    exact haccept p w hi
  have reject' : ∀ x y : Fin N → Bool,
      (Finset.univ.filter fun l => y l=true).card≤k →
      (¬∃ p w, I p w ∧ x p=true ∧ y w=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C (Fin.append x y)=false := by
    intro x y hc hno
    apply hreject (Fin.append x y)
    · simpa only [Fin.append_right] using hc
    · simpa only [Fin.append_left,Fin.append_right] using hno
  have reject1 : ∀ x y : Fin N → Bool,
      (Finset.univ.filter fun l => y l=true).card≤1 →
      (¬∃ p w, I p w ∧ x p=true ∧ y w=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C (Fin.append x y)=false := by
    intro x y hc hno
    exact reject' x y (by omega) hno
  have cover : ∀ A B : Finset (Fin N),
      (∀ p w, I p w → p∈A ∨ w∈B) → N≤A.card+B.card := by
    intro A B hcover
    exact regular_cover (by omega : 0<q+1) I hrow hlines A B hcover
  let mixed : ℕ → Prop := fun i =>
    0 < (C.lineDegrees (N+N) (Finset.range N)).getD i 0 ∧
    0 < (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD i 0
  let cone : ℕ → Prop := fun j => j<C.gates.length ∧ mixed (N+N+j) ∧
    Relation.ReflTransGen (fun a b => a<b ∧ ∃ f : Fin C.gates.length,
      b=N+N+f.val ∧ a ∈ (C.gates.get f).inputs) (N+N+j) C.output
  let gok : (Fin N → Bool) → ℕ → Prop := fun x j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op=PEqualNP.CircuitLowerBounds.GateOp.or ∨
    ∃ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs,
      (C.lineDegrees (N+N) (Finset.Ico N (N+N))).getD i 0=0 ∧
      (C.wires (List.ofFn (Fin.append x (fun _ : Fin N => false)))).getD i false=true
  let step : (Fin N → Bool) → ℕ → ℕ → Prop := fun x a b =>
    cone b ∧ N+N+a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b).inputs ∧ gok x b
  let lvx : (Fin N → Bool) → ℕ → Prop := fun x j => cone j ∧ gok x j ∧
    ∃ o, N+N+o=C.output ∧ Relation.ReflTransGen (step x) j o
  let slot : ℕ → ℕ → Prop := fun h j => cone j ∧
    h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs ∧
    (C.lineDegrees (N+N) (Finset.range N)).getD h 0=0
  let ap : ℕ → Fin N → Prop := fun h p => ∃ j, slot h j ∧ lvx (fun a => decide (a=p)) j
  let lh : ℕ → Fin N → Prop := fun h w =>
    (C.wires (List.ofFn (Fin.append (fun _ : Fin N => false) (fun a => decide (a=w))))).getD h false=true
  let lpw : ℕ → Fin N → Prop := fun h w => ∀ v, lh h v ↔ v=w
  let ppw : ℕ → Fin N → Prop := fun h p =>
    (∃ w v, w≠v ∧ lh h w ∧ lh h v) ∧ ∀ a, ap h a ↔ a=p
  let lps : Fin N → Fin N → Prop := fun p w => ∃ h, lpw h w ∧ ap h p
  let pps : Fin N → Fin N → Prop := fun p w => ∃ h, ppw h p ∧ lh h w
  have hpaths := live N I C hC hkm hfour hedge accept' reject1
    mixed rfl cone rfl gok rfl step rfl lvx rfl slot rfl ap rfl lh rfl lpw rfl ppw rfl lps rfl pps rfl
  have hbound := theoremN N k N I C hfour hedge hk hC hkm accept' reject' cover
    mixed rfl cone rfl gok rfl step rfl lvx rfl slot rfl ap rfl lh rfl lpw rfl ppw rfl lps rfl pps rfl
  have hcount := split_count hkq I lps pps hrow hpaths.2.2.2.2.2
  nlinarith
