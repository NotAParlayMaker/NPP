import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L532

namespace PEqualNP.Outside.L_meta_657

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.Loc
open PEqualNP.MetaComplexity.EdgeFn PEqualNP.Library.Peel PEqualNP.Library.Peel.Scratch
open SimpleGraph

/-! ## Target function and graph -/

private def fTheta (x : Fin 11 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) ||
  (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) ||
  (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)

private def thetaEdges : List (Fin 11 × Fin 11) :=
  [(0, 2), (2, 3), (3, 4), (4, 1),
   (0, 5), (5, 6), (6, 7), (7, 1),
   (0, 8), (8, 9), (9, 10), (10, 1)]

private def thetaRel (i j : Fin 11) : Bool :=
  (thetaEdges.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i))

private theorem thetaRel_symm (i j : Fin 11) : thetaRel i j = thetaRel j i := by
  revert i j
  decide

private theorem thetaRel_irrefl (i : Fin 11) : thetaRel i i = false := by
  revert i
  decide

private abbrev thetaG : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel fun i j => thetaRel i j = true

private theorem thetaG_adj_iff (i j : Fin 11) : thetaG.Adj i j ↔ thetaRel i j = true := by
  simp only [thetaG, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rwa [thetaRel_symm]
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [thetaRel_irrefl] at h
    cases h

private theorem fTheta_eq_true (x : Fin 11 → Bool) :
    fTheta x = true ↔ ∃ i j : Fin 11, thetaG.Adj i j ∧ x i = true ∧ x j = true := by
  constructor
  · intro h
    unfold fTheta at h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
    · exact ⟨0, 2, by decide, h.1, h.2⟩
    · exact ⟨2, 3, by decide, h.1, h.2⟩
    · exact ⟨3, 4, by decide, h.1, h.2⟩
    · exact ⟨4, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 5, by decide, h.1, h.2⟩
    · exact ⟨5, 6, by decide, h.1, h.2⟩
    · exact ⟨6, 7, by decide, h.1, h.2⟩
    · exact ⟨7, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 8, by decide, h.1, h.2⟩
    · exact ⟨8, 9, by decide, h.1, h.2⟩
    · exact ⟨9, 10, by decide, h.1, h.2⟩
    · exact ⟨10, 1, by decide, h.1, h.2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hcases : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
        (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨ (i = 4 ∧ j = 1) ∨ (i = 1 ∧ j = 4) ∨
        (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨ (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
        (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨ (i = 7 ∧ j = 1) ∨ (i = 1 ∧ j = 7) ∨
        (i = 0 ∧ j = 8) ∨ (i = 8 ∧ j = 0) ∨ (i = 8 ∧ j = 9) ∨ (i = 9 ∧ j = 8) ∨
        (i = 9 ∧ j = 10) ∨ (i = 10 ∧ j = 9) ∨ (i = 10 ∧ j = 1) ∨ (i = 1 ∧ j = 10) := by
      have key : ∀ a b : Fin 11, thetaRel a b = true →
          (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
          (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 4 ∧ b = 1) ∨ (a = 1 ∧ b = 4) ∨
          (a = 0 ∧ b = 5) ∨ (a = 5 ∧ b = 0) ∨ (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) ∨
          (a = 6 ∧ b = 7) ∨ (a = 7 ∧ b = 6) ∨ (a = 7 ∧ b = 1) ∨ (a = 1 ∧ b = 7) ∨
          (a = 0 ∧ b = 8) ∨ (a = 8 ∧ b = 0) ∨ (a = 8 ∧ b = 9) ∨ (a = 9 ∧ b = 8) ∨
          (a = 9 ∧ b = 10) ∨ (a = 10 ∧ b = 9) ∨ (a = 10 ∧ b = 1) ∨ (a = 1 ∧ b = 10) := by
        decide
      exact key i j ((thetaG_adj_iff i j).1 hij)
    unfold fTheta
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hi, hj]

private theorem fTheta_eq_F : fTheta = F thetaG ∅ := by
  funext x
  rw [Bool.eq_iff_iff, fTheta_eq_true, F_true]
  simp

/-! ## Symmetries of `thetaG` -/

private def pSwap12 : Fin 11 → Fin 11 := ![0, 1, 5, 6, 7, 2, 3, 4, 8, 9, 10]
private def pSwap13 : Fin 11 → Fin 11 := ![0, 1, 8, 9, 10, 5, 6, 7, 2, 3, 4]
private def pRev : Fin 11 → Fin 11 := ![1, 0, 4, 3, 2, 7, 6, 5, 10, 9, 8]
private def pRev12 : Fin 11 → Fin 11 := fun i => pRev (pSwap12 i)
private def pRev13 : Fin 11 → Fin 11 := fun i => pRev (pSwap13 i)

private theorem relabel_update_symm (π : Fin 11 → Fin 11)
    (hinv : ∀ i, π (π i) = i)
    (hpres : ∀ i j, thetaG.Adj (π i) (π j) ↔ thetaG.Adj i j)
    (v : Fin 11) (b : Bool) (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x (π v) b)) s) :
    HasCircuitSize 11 (fun x => fTheta (Function.update x v b)) s := by
  have h1 := relabel_size π _ s hc
  have hfun : (fun x : Fin 11 → Bool => fTheta (Function.update (x ∘ π) (π v) b)) =
      (fun x : Fin 11 → Bool => fTheta (Function.update x v b)) := by
    funext x
    rw [Bool.eq_iff_iff, fTheta_eq_true, fTheta_eq_true]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨π i, π j, (hpres i j).2 hij, ?_, ?_⟩
      · by_cases h : i = π v
        · subst h; rw [hinv]; simpa using hi
        · have h' : π i ≠ v := fun e => h (by rw [← e, hinv])
          rw [Function.update_of_ne h] at hi
          rw [Function.update_of_ne h']
          exact hi
      · by_cases h : j = π v
        · subst h; rw [hinv]; simpa using hj
        · have h' : π j ≠ v := fun e => h (by rw [← e, hinv])
          rw [Function.update_of_ne h] at hj
          rw [Function.update_of_ne h']
          exact hj
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨π i, π j, (hpres i j).2 hij, ?_, ?_⟩
      · by_cases h : i = v
        · subst h; simpa using hi
        · have h' : π i ≠ π v := fun e => h (by have := congrArg π e; rwa [hinv, hinv] at this)
          rw [Function.update_of_ne h] at hi
          rw [Function.update_of_ne h']
          simpa [hinv] using hi
      · by_cases h : j = v
        · subst h; simpa using hj
        · have h' : π j ≠ π v := fun e => h (by have := congrArg π e; rwa [hinv, hinv] at this)
          rw [Function.update_of_ne h] at hj
          rw [Function.update_of_ne h']
          simpa [hinv] using hj
  rwa [hfun] at h1

/-! ## Acyclicity via vertex order and `Peelable` proofs -/

private theorem walk_support_getElem {V : Type*} {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i < p.support.length),
      p.support[i] = p.getVert i
  | _, _, Walk.nil, 0, _ => rfl
  | _, _, Walk.nil, _ + 1, hi => by simp at hi
  | _, _, Walk.cons _ _, 0, _ => rfl
  | _, _, Walk.cons _ p', i + 1, hi => walk_support_getElem p' i (by simpa using hi)

private theorem acyclic_of_order {n : ℕ} (H : SimpleGraph (Fin n)) (ord : Fin n → ℕ)
    (hne : ∀ u v, H.Adj u v → ord u ≠ ord v)
    (huniq : ∀ u v1 v2, H.Adj u v1 → H.Adj u v2 → ord v1 < ord u → ord v2 < ord u → v1 = v2) :
    H.IsAcyclic := by
  intro v c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hneS : (Finset.range c.length).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image (Finset.range c.length)
    (fun i => ord (c.getVert i)) hneS
  have hk : k < c.length := Finset.mem_range.1 hkmem
  let k1 : ℕ := if k + 1 < c.length then k + 1 else 0
  let k2 : ℕ := if k = 0 then c.length - 1 else k - 1
  have hk1_lt : k1 < c.length := by dsimp [k1]; split_ifs <;> omega
  have hk2_lt : k2 < c.length := by dsimp [k2]; split_ifs <;> omega
  have hk12 : k1 ≠ k2 := by dsimp [k1, k2]; split_ifs <;> omega
  have hadj1 : H.Adj (c.getVert k) (c.getVert k1) := by
    have h := c.adj_getVert_succ hk
    dsimp [k1]
    split_ifs with hlt
    · exact h
    · have he : k + 1 = c.length := by omega
      rw [he, Walk.getVert_length] at h
      simpa [c.getVert_zero] using h
  have hadj2 : H.Adj (c.getVert k) (c.getVert k2) := by
    dsimp [k2]
    split_ifs with hz
    · subst hz
      have h := c.adj_getVert_succ (i := c.length - 1) (by omega)
      rw [show c.length - 1 + 1 = c.length by omega, Walk.getVert_length] at h
      simpa [c.getVert_zero] using h.symm
    · have h := c.adj_getVert_succ (i := k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at h
      exact h.symm
  have hord1 : ord (c.getVert k1) < ord (c.getVert k) := by
    have hle := hkmax k1 (Finset.mem_range.2 hk1_lt)
    have hne' := hne _ _ hadj1
    omega
  have hord2 : ord (c.getVert k2) < ord (c.getVert k) := by
    have hle := hkmax k2 (Finset.mem_range.2 hk2_lt)
    have hne' := hne _ _ hadj2
    omega
  have heq : c.getVert k1 = c.getVert k2 := huniq _ _ _ hadj1 hadj2 hord1 hord2
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hsupp_len : c.support.length = c.length + 1 := Walk.length_support c
  have htail_len : c.support.tail.length = c.length := by
    rw [List.length_tail, hsupp_len]; omega
  have htail_get : ∀ i (hi : i < c.length),
      c.support.tail[if i = 0 then c.length - 1 else i - 1]'(by split_ifs <;> omega) =
        c.getVert i := by
    intro i hi
    split_ifs with hz
    · subst hz
      rw [List.getElem_tail, walk_support_getElem, show c.length - 1 + 1 = c.length by omega,
        Walk.getVert_length, c.getVert_zero]
    · rw [List.getElem_tail, walk_support_getElem, show i - 1 + 1 = i by omega]
  have h1 := htail_get k1 hk1_lt
  have h2 := htail_get k2 hk2_lt
  let i1 : Fin c.support.tail.length :=
    ⟨if k1 = 0 then c.length - 1 else k1 - 1, by split_ifs <;> omega⟩
  let i2 : Fin c.support.tail.length :=
    ⟨if k2 = 0 then c.length - 1 else k2 - 1, by split_ifs <;> omega⟩
  have hfin : i1 = i2 := (List.nodup_iff_injective_getElem.1 hnodup) (by
    change c.support.tail[i1.val]'i1.isLt = c.support.tail[i2.val]'i2.isLt
    dsimp [i1, i2]
    rw [h1, h2, heq])
  have hidx_eq : i1.val = i2.val := congrArg Fin.val hfin
  dsimp [i1, i2] at hidx_eq
  split_ifs at hidx_eq <;> omega

private theorem del0_acyclic : (delVerts thetaG {0}).IsAcyclic := by
  let ord : Fin 11 → ℕ := ![4, 0, 3, 2, 1, 3, 2, 1, 3, 2, 1]
  refine acyclic_of_order (delVerts thetaG {0}) ord ?_ ?_
  · have : ∀ u v : Fin 11, (thetaRel u v = true ∧ u ≠ 0 ∧ v ≠ 0) → ord u ≠ ord v := by decide
    intro u v h
    exact this u v ⟨(thetaG_adj_iff u v).1 h.1, by simpa using h.2.1, by simpa using h.2.2⟩
  · have : ∀ u v1 v2 : Fin 11, (thetaRel u v1 = true ∧ u ≠ 0 ∧ v1 ≠ 0) →
        (thetaRel u v2 = true ∧ u ≠ 0 ∧ v2 ≠ 0) → ord v1 < ord u → ord v2 < ord u → v1 = v2 := by
      decide
    intro u v1 v2 h1 h2 ho1 ho2
    exact this u v1 v2 ⟨(thetaG_adj_iff u v1).1 h1.1, by simpa using h1.2.1, by simpa using h1.2.2⟩
      ⟨(thetaG_adj_iff u v2).1 h2.1, by simpa using h2.2.1, by simpa using h2.2.2⟩ ho1 ho2

private theorem del0_peelable : Peelable (delVerts thetaG {0}) :=
  peelable_of_isAcyclic del0_acyclic

private theorem del23v_acyclic (v : Fin 11)
    (hv : v = 0 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 1 ∨ v = 10 ∨ v = 9 ∨ v = 8) :
    (delVerts thetaG {2, 3, v}).IsAcyclic := by
  have go : ∀ ord : Fin 11 → ℕ,
      (∀ u w : Fin 11, (thetaRel u w = true ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ v ∧ w ≠ 2 ∧ w ≠ 3 ∧ w ≠ v) →
        ord u ≠ ord w) →
      (∀ u w1 w2 : Fin 11,
        (thetaRel u w1 = true ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ v ∧ w1 ≠ 2 ∧ w1 ≠ 3 ∧ w1 ≠ v) →
        (thetaRel u w2 = true ∧ u ≠ 2 ∧ u ≠ 3 ∧ u ≠ v ∧ w2 ≠ 2 ∧ w2 ≠ 3 ∧ w2 ≠ v) →
        ord w1 < ord u → ord w2 < ord u → w1 = w2) →
      (delVerts thetaG {2, 3, v}).IsAcyclic := by
    intro ord h1 h2
    refine acyclic_of_order _ ord ?_ ?_
    · intro u w h
      simp only [delVerts_adj, Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact h1 u w ⟨(thetaG_adj_iff u w).1 h.1, h.2.1.1, h.2.1.2.1, h.2.1.2.2,
        h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · intro u w1 w2 ha hb ho1 ho2
      simp only [delVerts_adj, Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
      exact h2 u w1 w2
        ⟨(thetaG_adj_iff u w1).1 ha.1, ha.2.1.1, ha.2.1.2.1, ha.2.1.2.2,
          ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2⟩
        ⟨(thetaG_adj_iff u w2).1 hb.1, hb.2.1.1, hb.2.1.2.1, hb.2.1.2.2,
          hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2⟩ ho1 ho2
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact go ![7, 3, 9, 9, 8, 0, 1, 2, 6, 5, 4] (by decide) (by decide)
  · exact go ![6, 2, 9, 9, 8, 7, 0, 1, 5, 4, 3] (by decide) (by decide)
  · exact go ![5, 1, 9, 9, 8, 6, 7, 0, 4, 3, 2] (by decide) (by decide)
  · exact go ![4, 0, 9, 9, 8, 5, 6, 7, 3, 2, 1] (by decide) (by decide)
  · exact go ![3, 7, 9, 9, 8, 4, 5, 6, 2, 1, 0] (by decide) (by decide)
  · exact go ![2, 6, 9, 9, 8, 3, 4, 5, 1, 0, 7] (by decide) (by decide)
  · exact go ![1, 5, 9, 9, 8, 2, 3, 4, 0, 7, 6] (by decide) (by decide)
  · exact go ![0, 4, 9, 9, 8, 1, 2, 3, 7, 6, 5] (by decide) (by decide)

private theorem del2_peelable : Peelable (delVerts thetaG {2}) := by
  intro X hE
  by_cases h34 : (3 : Fin 11) ∉ X ∧ (4 : Fin 11) ∉ X
  · left
    refine ⟨3, 4, ?_, ?_, Or.inl ⟨1, ?_⟩⟩
    · simp only [delVerts_adj, Finset.mem_singleton]
      exact ⟨⟨by decide, by decide, by decide⟩, h34.1, h34.2⟩
    · intro w hw
      have h3w : thetaRel 3 w = true ∧ w ≠ 2 := by
        simp only [delVerts_adj, Finset.mem_singleton] at hw
        exact ⟨(thetaG_adj_iff 3 w).1 hw.1.1, hw.1.2.2⟩
      have key : ∀ w : Fin 11, (thetaRel 3 w = true ∧ w ≠ 2) → w = 4 := by decide
      exact key w h3w
    · intro w hw
      have h4w : thetaRel 4 w = true := (thetaG_adj_iff 4 w).1 hw.1.1
      have key : ∀ w : Fin 11, thetaRel 4 w = true → w = 3 ∨ w = 1 := by decide
      exact key w h4w
  · by_cases hcyc : (0 : Fin 11) ∈ X ∨ (5 : Fin 11) ∈ X ∨ (6 : Fin 11) ∈ X ∨
        (7 : Fin 11) ∈ X ∨ (1 : Fin 11) ∈ X ∨ (10 : Fin 11) ∈ X ∨ (9 : Fin 11) ∈ X ∨
        (8 : Fin 11) ∈ X
    · left
      have h3or4 : (3 : Fin 11) ∈ X ∨ (4 : Fin 11) ∈ X := by tauto
      have hsub_of : ∀ v : Fin 11, v ∈ X →
          delVerts (delVerts thetaG {2}) X ≤ delVerts thetaG {2, 3, v} := by
        intro v hvX i j hij
        simp only [delVerts_adj, Finset.mem_insert, Finset.mem_singleton, not_or] at hij ⊢
        have hi3 : i ≠ 3 := by
          intro hi
          subst hi
          have hj4 : j = 4 := by
            have key : ∀ w : Fin 11, (thetaRel 3 w = true ∧ w ≠ 2) → w = 4 := by decide
            exact key j ⟨(thetaG_adj_iff 3 j).1 hij.1.1, hij.1.2.2⟩
          subst hj4
          rcases h3or4 with h3 | h4
          · exact hij.2.1 h3
          · exact hij.2.2 h4
        have hj3 : j ≠ 3 := by
          intro hj
          subst hj
          have hi4 : i = 4 := by
            have key : ∀ w : Fin 11, (thetaRel w 3 = true ∧ w ≠ 2) → w = 4 := by decide
            exact key i ⟨(thetaG_adj_iff i 3).1 hij.1.1, hij.1.2.1⟩
          subst hi4
          rcases h3or4 with h3 | h4
          · exact hij.2.2 h3
          · exact hij.2.1 h4
        refine ⟨hij.1.1, ⟨hij.1.2.1, hi3, fun e => hij.2.1 (e ▸ hvX)⟩,
          ⟨hij.1.2.2, hj3, fun e => hij.2.2 (e ▸ hvX)⟩⟩
      have hac : (delVerts (delVerts thetaG {2}) X).IsAcyclic := by
        rcases hcyc with h | h | h | h | h | h | h | h
        · exact (del23v_acyclic 0 (by simp)).anti (hsub_of 0 h)
        · exact (del23v_acyclic 5 (by simp)).anti (hsub_of 5 h)
        · exact (del23v_acyclic 6 (by simp)).anti (hsub_of 6 h)
        · exact (del23v_acyclic 7 (by simp)).anti (hsub_of 7 h)
        · exact (del23v_acyclic 1 (by simp)).anti (hsub_of 1 h)
        · exact (del23v_acyclic 10 (by simp)).anti (hsub_of 10 h)
        · exact (del23v_acyclic 9 (by simp)).anti (hsub_of 9 h)
        · exact (del23v_acyclic 8 (by simp)).anti (hsub_of 8 h)
      exact forest_good_leaf _ hac hE
    · right
      push Not at hcyc
      obtain ⟨h0, h5, h6, h7, h1, h10, h9, h8⟩ := hcyc
      refine ⟨9, 8, 0, 5, 6, 7, by decide, ?_, ?_, ?_, ?_, ⟨10, ?_⟩, ⟨1, ?_⟩⟩
      · intro w
        constructor
        · intro hw
          have key : ∀ w : Fin 11, thetaRel 8 w = true → w = 9 ∨ w = 0 := by decide
          exact key w ((thetaG_adj_iff 8 w).1 hw.1.1)
        · rintro (rfl | rfl)
          · exact ⟨⟨by decide, by decide, by decide⟩, h8, h9⟩
          · exact ⟨⟨by decide, by decide, by decide⟩, h8, h0⟩
      · intro w
        constructor
        · intro hw
          have key : ∀ w : Fin 11, (thetaRel 0 w = true ∧ w ≠ 2) → w = 8 ∨ w = 5 := by decide
          exact key w ⟨(thetaG_adj_iff 0 w).1 hw.1.1, by simpa using hw.1.2.2⟩
        · rintro (rfl | rfl)
          · exact ⟨⟨by decide, by decide, by decide⟩, h0, h8⟩
          · exact ⟨⟨by decide, by decide, by decide⟩, h0, h5⟩
      · intro w
        constructor
        · intro hw
          have key : ∀ w : Fin 11, thetaRel 5 w = true → w = 0 ∨ w = 6 := by decide
          exact key w ((thetaG_adj_iff 5 w).1 hw.1.1)
        · rintro (rfl | rfl)
          · exact ⟨⟨by decide, by decide, by decide⟩, h5, h0⟩
          · exact ⟨⟨by decide, by decide, by decide⟩, h5, h6⟩
      · intro w
        constructor
        · intro hw
          have key : ∀ w : Fin 11, thetaRel 6 w = true → w = 5 ∨ w = 7 := by decide
          exact key w ((thetaG_adj_iff 6 w).1 hw.1.1)
        · rintro (rfl | rfl)
          · exact ⟨⟨by decide, by decide, by decide⟩, h6, h5⟩
          · exact ⟨⟨by decide, by decide, by decide⟩, h6, h7⟩
      · intro w hw
        have key : ∀ w : Fin 11, thetaRel 9 w = true → w = 8 ∨ w = 10 := by decide
        exact key w ((thetaG_adj_iff 9 w).1 hw.1.1)
      · intro w hw
        have key : ∀ w : Fin 11, thetaRel 7 w = true → w = 6 ∨ w = 1 := by decide
        exact key w ((thetaG_adj_iff 7 w).1 hw.1.1)

/-! ## Edge counts and matching lower bounds on vertex cover -/

private theorem card_ge_of_matching {n : ℕ} :
    ∀ (M : List (Fin n × Fin n)) (T : Finset (Fin n)),
      (M.flatMap fun e => [e.1, e.2]).Nodup →
      (∀ e ∈ M, e.1 ∈ T ∨ e.2 ∈ T) →
      M.length ≤ T.card
  | [], _, _, _ => Nat.zero_le _
  | (a, b) :: rest, T, hnd, hcov => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, not_or] at hnd
    obtain ⟨⟨_, ha_rest⟩, hb_rest, hnd_rest⟩ := hnd
    have hcov_rest : ∀ w : Fin n, w ∈ T → w ∉ (rest.flatMap fun e => [e.1, e.2]) →
        ∀ e ∈ rest, e.1 ∈ T.erase w ∨ e.2 ∈ T.erase w := by
      intro w _ hw e he
      have hne1 : e.1 ≠ w := fun h => hw (List.mem_flatMap.2 ⟨e, he, by simp [h]⟩)
      have hne2 : e.2 ≠ w := fun h => hw (List.mem_flatMap.2 ⟨e, he, by simp [h]⟩)
      rcases hcov e (List.mem_cons_of_mem _ he) with h1 | h2
      · exact Or.inl (Finset.mem_erase.2 ⟨hne1, h1⟩)
      · exact Or.inr (Finset.mem_erase.2 ⟨hne2, h2⟩)
    rcases hcov (a, b) (List.mem_cons_self ..) with ha | hb
    · have ih := card_ge_of_matching rest (T.erase a) hnd_rest (hcov_rest a ha ha_rest)
      rw [List.length_cons, ← Finset.card_erase_add_one ha]
      exact Nat.add_le_add_right ih 1
    · have ih := card_ge_of_matching rest (T.erase b) hnd_rest (hcov_rest b hb hb_rest)
      rw [List.length_cons, ← Finset.card_erase_add_one hb]
      exact Nat.add_le_add_right ih 1

private theorem card_ge_four_of_matching {n : ℕ} (T : Finset (Fin n))
    (a1 b1 a2 b2 a3 b3 a4 b4 : Fin n)
    (hnd : [a1, b1, a2, b2, a3, b3, a4, b4].Nodup)
    (h1 : a1 ∈ T ∨ b1 ∈ T) (h2 : a2 ∈ T ∨ b2 ∈ T)
    (h3 : a3 ∈ T ∨ b3 ∈ T) (h4 : a4 ∈ T ∨ b4 ∈ T) : 4 ≤ T.card := by
  have h := card_ge_of_matching [(a1, b1), (a2, b2), (a3, b3), (a4, b4)] T hnd (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption)
  simpa using h

private theorem card_ge_five_of_matching {n : ℕ} (T : Finset (Fin n))
    (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : Fin n)
    (hnd : [a1, b1, a2, b2, a3, b3, a4, b4, a5, b5].Nodup)
    (h1 : a1 ∈ T ∨ b1 ∈ T) (h2 : a2 ∈ T ∨ b2 ∈ T) (h3 : a3 ∈ T ∨ b3 ∈ T)
    (h4 : a4 ∈ T ∨ b4 ∈ T) (h5 : a5 ∈ T ∨ b5 ∈ T) : 5 ≤ T.card := by
  have h := card_ge_of_matching [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5)] T hnd (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> assumption)
  simpa using h

private theorem edgeSet_ncard_ge {n : ℕ} (G : SimpleGraph (Fin n))
    (E : Finset (Sym2 (Fin n))) (hsub : ∀ e ∈ E, e ∈ G.edgeSet) :
    E.card ≤ G.edgeSet.ncard := by
  have h : (E : Set (Sym2 (Fin n))) ⊆ G.edgeSet := fun e he => hsub e he
  have := Set.ncard_le_ncard h (Set.toFinite G.edgeSet)
  rwa [Set.ncard_coe_finset] at this

private theorem ncard_del0 : 9 ≤ (delVerts thetaG {0}).edgeSet.ncard := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(2, 3), s(3, 4), s(4, 1), s(5, 6), s(6, 7), s(7, 1), s(8, 9), s(9, 10), s(10, 1)}
  have hc : E.card = 9 := by decide
  calc
    9 = E.card := hc.symm
    _ ≤ (delVerts thetaG {0}).edgeSet.ncard := edgeSet_ncard_ge _ E (fun e he => by
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide, by decide⟩)

private theorem ncard_del2 : 10 ≤ (delVerts thetaG {2}).edgeSet.ncard := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(3, 4), s(4, 1), s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
  have hc : E.card = 10 := by decide
  calc
    10 = E.card := hc.symm
    _ ≤ (delVerts thetaG {2}).edgeSet.ncard := edgeSet_ncard_ge _ E (fun e he => by
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide, by decide⟩)

private theorem ncard_del23 : 9 ≤ (delVerts thetaG {2, 3}).edgeSet.ncard := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(4, 1), s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
  have hc : E.card = 9 := by decide
  calc
    9 = E.card := hc.symm
    _ ≤ (delVerts thetaG {2, 3}).edgeSet.ncard := edgeSet_ncard_ge _ E (fun e he => by
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide, by decide⟩)

private theorem ncard_del234 : 8 ≤ (delVerts thetaG {2, 3, 4}).edgeSet.ncard := by
  let E : Finset (Sym2 (Fin 11)) :=
    {s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
  have hc : E.card = 8 := by decide
  calc
    8 = E.card := hc.symm
    _ ≤ (delVerts thetaG {2, 3, 4}).edgeSet.ncard := edgeSet_ncard_ge _ E (fun e he => by
      simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by decide, by decide⟩)

/-! ## Residual lower bounds from `L532` -/

private theorem lb_zero_false (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x 0 false)) s) : 12 ≤ s := by
  have hfn : (fun x => fTheta (Function.update x 0 false)) = F (delVerts thetaG {0}) ∅ := by
    funext x
    rw [fTheta_eq_F, Res.ToolRes0_proof 11 thetaG ∅ 0 x (by simp), delV_eq]
  rw [hfn] at hc
  have hb := PEqualNP.MetaComplexity.L532 11 4 s (delVerts thetaG {0}) ∅ del0_peelable
    (fun _ _ _ => by simp)
    (Or.inr ⟨2, 3, by exact ⟨by decide, by decide, by decide⟩⟩)
    (fun T hT => card_ge_four_of_matching T 2 3 4 1 5 6 8 9 (by decide)
      (hT 2 3 ⟨by decide, by decide, by decide⟩)
      (hT 4 1 ⟨by decide, by decide, by decide⟩)
      (hT 5 6 ⟨by decide, by decide, by decide⟩)
      (hT 8 9 ⟨by decide, by decide, by decide⟩))
    hc
  have he := ncard_del0
  simp only [Finset.card_empty, zero_add] at hb
  omega

private theorem lb_two_false (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x 2 false)) s) : 14 ≤ s := by
  have hfn : (fun x => fTheta (Function.update x 2 false)) = F (delVerts thetaG {2}) ∅ := by
    funext x
    rw [fTheta_eq_F, Res.ToolRes0_proof 11 thetaG ∅ 2 x (by simp), delV_eq]
  rw [hfn] at hc
  have hb := PEqualNP.MetaComplexity.L532 11 5 s (delVerts thetaG {2}) ∅ del2_peelable
    (fun _ _ _ => by simp)
    (Or.inr ⟨3, 4, by exact ⟨by decide, by decide, by decide⟩⟩)
    (fun T hT => card_ge_five_of_matching T 3 4 0 5 6 7 8 9 10 1 (by decide)
      (hT 3 4 ⟨by decide, by decide, by decide⟩)
      (hT 0 5 ⟨by decide, by decide, by decide⟩)
      (hT 6 7 ⟨by decide, by decide, by decide⟩)
      (hT 8 9 ⟨by decide, by decide, by decide⟩)
      (hT 10 1 ⟨by decide, by decide, by decide⟩))
    hc
  have he := ncard_del2
  simp only [Finset.card_empty, zero_add] at hb
  omega

private theorem lb_three_false (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x 3 false)) s) : 13 ≤ s := by
  have hfn : (fun x => fTheta (Function.update x 3 false)) = F (delVerts thetaG {3}) ∅ := by
    funext x
    rw [fTheta_eq_F, Res.ToolRes0_proof 11 thetaG ∅ 3 x (by simp), delV_eq]
  rw [hfn] at hc
  have hdep2 : Dep (F (delVerts thetaG {3}) ∅) 2 :=
    F_dep (delVerts thetaG {3}) ∅ 2 0 ⟨by decide, by decide, by decide⟩ (by simp)
  have hnc2 : ∃ x y : Fin 11 → Bool,
      F (delVerts thetaG {3}) ∅ (Function.update x 2 false) ≠
      F (delVerts thetaG {3}) ∅ (Function.update y 2 false) := by
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    have h1 : F (delVerts thetaG {3}) ∅ (Function.update (fun _ => true) 2 false) = true :=
      F_true_of 0 5 ⟨by decide, by decide, by decide⟩ (by simp) (by simp)
    have h0 : F (delVerts thetaG {3}) ∅ (Function.update (fun _ => false) 2 false) = false := by
      have : Function.update (fun _ : Fin 11 => false) 2 false = fun _ => false := by
        funext i; by_cases h : i = 2 <;> simp [h]
      rw [this]; exact F_zero _ _
    rw [h1, h0]; simp
  have hs_pos : 1 ≤ s := by
    have := dep_lower_set 11 (F (delVerts thetaG {3}) ∅) {2, 0} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hdep2
      · exact F_dep (delVerts thetaG {3}) ∅ 0 2 ⟨by decide, by decide, by decide⟩ (by simp)) s hc
    rw [Finset.card_pair (by decide)] at this
    omega
  obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
  have hc1 := one_gate_at 10 (F (delVerts thetaG {3}) ∅) 2 false s0 hdep2 hnc2 hc
  have hfn2 : (fun x => F (delVerts thetaG {3}) ∅ (Function.update x 2 false)) =
      F (delVerts thetaG {2, 3}) ∅ := by
    funext x
    rw [Res.ToolRes0_proof 11 (delVerts thetaG {3}) ∅ 2 x (by simp), delV_eq, delVerts_delVerts]
    have hset : ({3} : Finset (Fin 11)) ∪ {2} = {2, 3} := by decide
    rw [hset]
  rw [hfn2] at hc1
  have hpeel23 : Peelable (delVerts thetaG {2, 3}) := by
    have hset : ({2} : Finset (Fin 11)) ∪ {3} = {2, 3} := by decide
    rw [← hset, ← delVerts_delVerts]
    exact Peelable.delVerts del2_peelable {3}
  have hb := PEqualNP.MetaComplexity.L532 11 4 s0 (delVerts thetaG {2, 3}) ∅ hpeel23
    (fun _ _ _ => by simp)
    (Or.inr ⟨0, 5, by exact ⟨by decide, by decide, by decide⟩⟩)
    (fun T hT => card_ge_four_of_matching T 4 1 0 5 6 7 8 9 (by decide)
      (hT 4 1 ⟨by decide, by decide, by decide⟩)
      (hT 0 5 ⟨by decide, by decide, by decide⟩)
      (hT 6 7 ⟨by decide, by decide, by decide⟩)
      (hT 8 9 ⟨by decide, by decide, by decide⟩))
    hc1
  have he := ncard_del23
  simp only [Finset.card_empty, zero_add] at hb
  omega

private theorem lb_three_true (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x 3 true)) s) : 13 ≤ s := by
  have hfn : (fun x => fTheta (Function.update x 3 true)) =
      F (delVerts thetaG {2, 3, 4}) {2, 4} := by
    funext x
    rw [fTheta_eq_F]
    have h1 := Res.ToolRes1_proof 11 thetaG ∅ 3 {2, 4} x (by simp) (by
      intro w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [thetaG_adj_iff]
      have key : ∀ w : Fin 11, thetaRel 3 w = true ↔ w = 2 ∨ w = 4 := by decide
      exact key w)
    rw [h1, delV_eq]
    have hset : insert (3 : Fin 11) ({2, 4} : Finset (Fin 11)) = {2, 3, 4} := by decide
    have hA : (∅ : Finset (Fin 11)) ∪ {2, 4} = {2, 4} := by decide
    rw [hset, hA]
  rw [hfn] at hc
  have hpeel234 : Peelable (delVerts thetaG {2, 3, 4}) := by
    have hset : ({2} : Finset (Fin 11)) ∪ {3, 4} = {2, 3, 4} := by decide
    rw [← hset, ← delVerts_delVerts]
    exact Peelable.delVerts del2_peelable {3, 4}
  have hb := PEqualNP.MetaComplexity.L532 11 4 s (delVerts thetaG {2, 3, 4}) {2, 4} hpeel234
    (fun i j hij hi => by
      simp only [delVerts_adj, Finset.mem_insert, Finset.mem_singleton, not_or] at hij hi
      rcases hi with rfl | rfl
      · exact hij.2.1.1 rfl
      · exact hij.2.1.2.2 rfl)
    (Or.inl ⟨2, by simp⟩)
    (fun T hT => card_ge_four_of_matching T 0 5 6 7 1 10 9 8 (by decide)
      (hT 0 5 ⟨by decide, by decide, by decide⟩)
      (hT 6 7 ⟨by decide, by decide, by decide⟩)
      (hT 1 10 ⟨by decide, by decide, by decide⟩)
      (hT 9 8 ⟨by decide, by decide, by decide⟩))
    hc
  have he := ncard_del234
  have hAc : ({2, 4} : Finset (Fin 11)).card = 2 := by decide
  rw [hAc] at hb
  omega

private theorem lb_adjBranch_false (y : Fin 11)
    (hy : y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x y false)) s) : 14 ≤ s := by
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_two_false s hc
  · exact lb_two_false s (relabel_update_symm pRev (by decide) (by decide) 2 false s hc)
  · exact lb_two_false s (relabel_update_symm pSwap12 (by decide) (by decide) 2 false s hc)
  · exact lb_two_false s (relabel_update_symm pRev12 (by decide) (by decide) 2 false s hc)
  · exact lb_two_false s (relabel_update_symm pSwap13 (by decide) (by decide) 2 false s hc)
  · exact lb_two_false s (relabel_update_symm pRev13 (by decide) (by decide) 2 false s hc)

private theorem lb_mid_false (y : Fin 11) (hy : y = 3 ∨ y = 6 ∨ y = 9) (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x y false)) s) : 13 ≤ s := by
  rcases hy with rfl | rfl | rfl
  · exact lb_three_false s hc
  · exact lb_three_false s (relabel_update_symm pSwap12 (by decide) (by decide) 3 false s hc)
  · exact lb_three_false s (relabel_update_symm pSwap13 (by decide) (by decide) 3 false s hc)

private theorem lb_mid_true (y : Fin 11) (hy : y = 3 ∨ y = 6 ∨ y = 9) (s : ℕ)
    (hc : HasCircuitSize 11 (fun x => fTheta (Function.update x y true)) s) : 13 ≤ s := by
  rcases hy with rfl | rfl | rfl
  · exact lb_three_true s hc
  · exact lb_three_true s (relabel_update_symm pSwap12 (by decide) (by decide) 3 true s hc)
  · exact lb_three_true s (relabel_update_symm pSwap13 (by decide) (by decide) 3 true s hc)

/-! ## Semantic properties on `D_int = {2, 3, 4, 5, 6, 7, 8, 9, 10}` -/

private def D_int : Finset (Fin 11) := {2, 3, 4, 5, 6, 7, 8, 9, 10}

private theorem theta_nc (y : Fin 11) (b : Bool) :
    ∃ x x' : Fin 11 → Bool,
      fTheta (Function.update x y b) ≠ fTheta (Function.update x' y b) := by
  rw [fTheta_eq_F]
  have h : ∃ i j c : Fin 11, thetaG.Adj i j ∧ i ≠ y ∧ j ≠ y ∧ thetaG.Adj y c := by
    fin_cases y
    · exact ⟨2, 3, 2, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 4, by decide, by decide, by decide, by decide⟩
    · exact ⟨5, 6, 0, by decide, by decide, by decide, by decide⟩
    · exact ⟨5, 6, 2, by decide, by decide, by decide, by decide⟩
    · exact ⟨5, 6, 3, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 0, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 5, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 6, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 0, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 8, by decide, by decide, by decide, by decide⟩
    · exact ⟨2, 3, 9, by decide, by decide, by decide, by decide⟩
  obtain ⟨i, j, c, hij, hi, hj, hyc⟩ := h
  exact nc_of (fun _ _ _ => by simp) hij hi hj hyc b

private theorem theta_dep (y : Fin 11) : Dep fTheta y := by
  rw [fTheta_eq_F]
  have h : ∃ c : Fin 11, thetaG.Adj y c := by
    fin_cases y
    · exact ⟨2, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨5, by decide⟩
    · exact ⟨6, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨8, by decide⟩
    · exact ⟨9, by decide⟩
  obtain ⟨c, hc⟩ := h
  exact F_dep thetaG ∅ y c hc (by simp)

private def nb2 : Fin 11 → Fin 11 × Fin 11 :=
  ![(0, 0), (0, 0), (0, 3), (2, 4), (3, 1), (0, 6), (5, 7), (6, 1), (0, 9), (8, 10), (9, 1)]

private theorem theta_nf_clean (y y' : Fin 11) (hy : y ∈ D_int) (hy' : y' ∈ D_int) (hne : y ≠ y') :
    ¬ PairFunnel fTheta y y' := by
  rw [fTheta_eq_F]
  have hnb : ∀ b : Fin 11, b ∈ D_int → ∀ w : Fin 11, thetaRel b w = true →
      w = (nb2 b).1 ∨ w = (nb2 b).2 := by decide
  have key : ∀ a b : Fin 11, a ∈ D_int → b ∈ D_int → a ≠ b →
      ∃ c ∈ [(nb2 a).1, (nb2 a).2], ∃ c' ∈ [(nb2 b).1, (nb2 b).2],
        thetaRel a c = true ∧ c ≠ b ∧ c ≠ (nb2 b).1 ∧ c ≠ (nb2 b).2 ∧
        thetaRel b c' = true ∧ c' ≠ a := by
    decide
  obtain ⟨c, _, c', _, h1, h2, h4, h5, h6, h7⟩ := key y y' hy hy' hne
  exact nf_of (fun _ _ _ => by simp) hne ((thetaG_adj_iff _ _).2 h1) h2
    (fun w hw => hnb y' hy' w ((thetaG_adj_iff _ _).1 hw)) h4 h5 ((thetaG_adj_iff _ _).2 h6) h7

private theorem theta_zeroOn_false (x : Fin 11 → Bool) :
    fTheta (zeroOn D_int x) = false := by
  rw [fTheta_eq_F]
  refine F_false_of ({0, 1} : Finset (Fin 11)) (fun i hi => ?_) (fun _ ha => by simp at ha) ?_
  · unfold zeroOn at hi
    by_cases h : i ∈ D_int
    · simp [h] at hi
    · have key : ∀ i : Fin 11, i ∉ D_int → i ∈ ({0, 1} : Finset (Fin 11)) := by decide
      exact key i h
  · intro i j hij hi hj
    have key : ∀ i j : Fin 11, i ∈ ({0, 1} : Finset (Fin 11)) → j ∈ ({0, 1} : Finset (Fin 11)) →
        thetaRel i j = false := by decide
    have hrel := (thetaG_adj_iff i j).1 hij
    rw [key i j hi hj] at hrel
    cases hrel

/-! ## Frontier gate without H3 -/

private theorem theta_supp_out {gs : List Gate} {o : ℕ} (L : Least 11 fTheta gs o)
    (y : Fin 11) : y ∈ (suppsFrom gs (inputSupps 11)).getD o ∅ := by
  obtain ⟨x, hx⟩ := theta_dep y
  by_contra hno
  apply hx
  rw [← L.hev, ← L.hev]
  exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _ (agree_inputs _ _)).2.2 o (by
    intro k hk
    have : k ≠ y := fun e => hno (e ▸ hk)
    simp [Function.update_of_ne this])

private theorem theta_nlit (y : Fin 11) (c : Bool) : ¬ ∀ u, fTheta u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := theta_nc y false
  apply hx
  rw [h, h]
  simp

private theorem theta_front_out {gs : List Gate} {o : ℕ} (L : Least 11 fTheta gs o)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (l : ℕ) (hl : l ∈ g.inputs) {y : Fin 11} (c : Bool)
    (hv : ∀ u, vl gs u l = xor (u y) c) : o ≠ 11 + p := by
  intro e
  obtain ⟨x, x', hx⟩ := theta_nc y (xor (fixBit g) c)
  have hc : ∀ z : Fin 11 → Bool, fTheta (Function.update z y (xor (fixBit g) c)) = fixBit g := by
    intro z
    rw [← L.hev, e]
    refine vl_abs gs L.hcl _ p g hg hop l hl ?_
    rw [hv]; simp
  exact hx (by rw [hc, hc])

private theorem theta_front_two {gs : List Gate} {o : ℕ} (L : Least 11 fTheta gs o)
    (OR : OneReader D_int gs) (p : ℕ) (g : Gate) (hg : gs[p]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j k : ℕ) (hin : g.inputs = [j, k])
    (hj : j < 11 + p) (hk : k < 11 + p)
    (yj : Fin 11) (hyj : yj ∈ D_int) (cj : Bool) (hvj : ∀ u, vl gs u j = xor (u yj) cj)
    (hsj : j = yj ∨ ∃ pn, pn < p ∧ j = 11 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yj : ℕ)]⟩)
    (yk : Fin 11) (hyk : yk ∈ D_int) (ck : Bool) (hvk : ∀ u, vl gs u k = xor (u yk) ck)
    (hsk : k = yk ∨ ∃ pn, pn < p ∧ k = 11 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yk : ℕ)]⟩) :
    False := by
  have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
    obtain ⟨x, x', hx⟩ := theta_nc yj false; exact ⟨_, _, hx⟩
  have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin 11), v ∈ D_int → Reads gs p w →
      (w = v ∨ ∃ pn, pn < p ∧ w = 11 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(v : ℕ)]⟩) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → 11 + p' ≠ w → p' = p := by
    intro w v hv hw hs p' a ha hr hne
    rcases hs with e | ⟨r, _, er, hg'⟩
    · have ha' : a = v := by rcases ha with ha | ha; exact ha; rw [ha, e]
      rw [ha'] at hr
      exact OR.1 v hv p' p hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨_, hg', by simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := OR.1 v hv p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr; rw [er] at hw
        exact OR.2 v hv r hg' p' p hr hw
  have hvjk : yj ≠ yk := by
    intro e
    have hjk : j ≠ k := by
      intro e'; subst e'
      exact L.no_alias hfnc p htl j hj (fun u => by
        rw [vl_gate gs L.hcl u p g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, hr1, ej, hg1⟩ <;> rcases hsk with ek | ⟨r2, hr2, ek, hg2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := OR.1 yj hyj p r2 (by rw [← ej]; exact hRj) ⟨_, hg2, by rw [← e]; simp⟩
      omega
    · have := OR.1 yk hyk p r1 (by rw [← ek]; exact hRk) ⟨_, hg1, by rw [e]; simp⟩
      omega
    · have := OR.1 yj hyj r1 r2 ⟨_, hg1, by simp⟩ ⟨_, hg2, by rw [← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  have KC : ∀ u u' : Fin 11 → Bool, (∀ i, i ≠ yj → i ≠ yk → u i = u' i) →
      vl gs u (11 + p) = vl gs u' (11 + p) → fTheta u = fTheta u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e; exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e; exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (11 + p' = (yj : ℕ) ∨ 11 + p' = (yk : ℕ) ∨ 11 + p' = j ∨ 11 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = p := by
        rcases hBa' with e | e | e | e
        · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]; exact hgv
    · intro hB
      have hB' : o = (yj : ℕ) ∨ o = (yk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact theta_nlit yj false (fun x => by rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
      · exact theta_nlit yk false (fun x => by rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
      · exact theta_nlit yj cj (fun x => by rw [← L.hev, e, hvj])
      · exact theta_nlit yk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin 11 → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
      set2 x yj a yk b i = set2 x yj a' yk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
  have hval : ∀ (x : Fin 11 → Bool) (a b : Bool),
      vl gs (set2 x yj a yk b) (11 + p) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ p g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  apply theta_nf_clean yj yk hyj hyk hvjk
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

private theorem theta_get_front {gs : List Gate} {o : ℕ} (L : Least 11 fTheta gs o)
    (OR : OneReader D_int gs) :
    ∃ (p : ℕ) (g : Gate) (y : Fin 11) (l h : ℕ), Front D_int gs p g y l h ∧ o ≠ 11 + p := by
  classical
  have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
    obtain ⟨x, x', hx⟩ := theta_nc 2 false; exact ⟨_, _, hx⟩
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D_int, i ∈ (suppsFrom gs (inputSupps 11)).getD (11 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D_int, i ∉ (suppsFrom gs (inputSupps 11)).getD (11 + r) ∅ :=
      fun r hr g' hg' hop' i hi his => Nat.find_min hex hr ⟨g', hg', hop', i, hi, his⟩
    rcases L.hcl p g hg with ⟨hop2, _⟩ | ⟨_, j, k, hj, hk, hin⟩
    · rcases hop with h | h <;> rw [h] at hop2 <;> cases hop2
    obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl p g hg i).1 his
    rw [hin] at ha
    have hlitof : ∀ (w : ℕ) (y : Fin 11),
        (w = y ∨ ∃ pn, pn < p ∧ w = 11 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) →
        IsLit 11 gs y w := by
      rintro w y (e | ⟨pn, _, e, hpn⟩)
      · exact Or.inl e
      · exact Or.inr ⟨pn, e, hpn⟩
    by_cases mj : ∃ i ∈ D_int, i ∈ (suppsFrom gs (inputSupps 11)).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D_int, i ∈ (suppsFrom gs (inputSupps 11)).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      exact theta_front_two L OR p g hg hop j k hin hj hk yj hyj cj hvj hsj yk hyk ck hvk hsk
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      refine ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩,
        theta_front_out L p g hg hop j (by rw [hin]; simp) c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      refine ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩,
        theta_front_out L p g hg hop k (by rw [hin]; simp) c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D_int, i ∉ (suppsFrom gs (inputSupps 11)).getD (11 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    by_cases hol : o < 11 + gs.length
    · obtain ⟨y, _, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol
        ⟨2, by decide, theta_supp_out L 2⟩
      exact theta_nlit y c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]

/-! ## Pointwise window lemma at a frontier gate -/

private theorem win_pointwise {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin 11} {l h : ℕ}
    (L : Least 11 fTheta gs o) (hO : OneReader D_int gs) (hF : Front D_int gs p g y l h)
    (x x' : Fin 11 → Bool) (hagr : ∀ i, i ∉ D_int → x' i = x i)
    (hF0 : fTheta x' = false) (hF1 : fTheta (Function.update x' y true) = true) :
    vl gs x h ≠ fixBit g := by
  intro hx
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  have hagr1 : ∀ i, i ∉ D_int → x i = x' i := fun i hi => (hagr i hi).symm
  have hagr2 : ∀ i, i ∉ D_int → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hagr i hi]
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (11 + p) = fixBit g :=
    vl_abs gs L.hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr1]; exact hx)
  have hc2 : vl gs (Function.update x' y true) (11 + p) = fixBit g :=
    vl_abs gs L.hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr2]; exact hx)
  have hol : o ≠ l := out_ne_lit L.hcl L.hev y (theta_nc y) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit L.hcl L.hev y (theta_nc y) y (Or.inl rfl)
  have key := agree_B gs L.hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin 11) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ hBq hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by rcases hBa with e | e; exact e; rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            apply hBq; right; rw [el, hq']
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads) ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [L.hev, L.hev, hF0, hF1] at key
  cases key

private theorem front_not_adjBranch {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin 11} {l h : ℕ}
    (L : Least 11 fTheta gs o) (hO : OneReader D_int gs) (hF : Front D_int gs p g y l h)
    (hy : y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) : False := by
  have hall : ∀ x : Fin 11 → Bool, vl gs x h ≠ fixBit g := by
    intro x
    have hwin : ∃ c : Fin 11, c ∈ D_int ∧ thetaG.Adj y c ∧ ∀ w, thetaG.Adj c w → w ∈ D_int := by
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨3, by decide, by decide, by decide⟩
      · exact ⟨3, by decide, by decide, by decide⟩
      · exact ⟨6, by decide, by decide, by decide⟩
      · exact ⟨6, by decide, by decide, by decide⟩
      · exact ⟨9, by decide, by decide, by decide⟩
      · exact ⟨9, by decide, by decide, by decide⟩
    obtain ⟨c, hcD, hyc, hcN⟩ := hwin
    have hx0 : F thetaG ∅ (zeroOn D_int x) = false := by
      rw [← fTheta_eq_F]; exact theta_zeroOn_false x
    obtain ⟨x', hagr, _, hF0, hF1⟩ := win_of (fun _ _ _ => by simp) hF.2.2.2.1 hcD hyc hcN x hx0
    rw [← fTheta_eq_F] at hF0 hF1
    exact win_pointwise L hO hF x x' hagr hF0 hF1
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hF.1).1
  have hlmem : l ∈ g.inputs := by rcases hF.2.2.1 with e | e <;> simp [e]
  have hllt : l < 11 + p := (L.hcl p g hF.1).lt l hlmem
  have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
    obtain ⟨x, x', hx⟩ := theta_nc y false; exact ⟨_, _, hx⟩
  refine L.no_alias hfnc p hp l hllt (fun x => ?_)
  have hne := hall x
  have hbv := vl_bin gs L.hcl x p l h g hF.1 hF.2.2.1
  rcases hF.2.1 with hand | hor
  · have hh : vl gs x h = true := by
      simp only [fixBit, hand] at hne
      cases hv : vl gs x h <;> simp_all
    rw [hbv.2 hand, hh, Bool.and_true]
  · have hh : vl gs x h = false := by
      simp only [fixBit, hor] at hne
      cases hv : vl gs x h <;> simp_all
    rw [hbv.1 hor, hh, Bool.or_false]

private theorem front_mid_partner {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin 11} {l h : ℕ}
    (L : Least 11 fTheta gs o) (hO : OneReader D_int gs) (hF : Front D_int gs p g y l h)
    (hy : y = 3 ∨ y = 6 ∨ y = 9) :
    ∀ x : Fin 11 → Bool, vl gs x h = if (x 0 && x 1) then fixBit g else !(fixBit g) := by
  have hnot11 : ∀ x : Fin 11 → Bool, (x 0 = false ∨ x 1 = false) → vl gs x h = !(fixBit g) := by
    intro x h01
    have hwin : ∃ x' : Fin 11 → Bool, (∀ i, i ∉ D_int → x' i = x i) ∧
        fTheta x' = false ∧ fTheta (Function.update x' y true) = true := by
      rcases h01 with hx0 | hx1
      · have hc : ∃ c : Fin 11, c ∈ D_int ∧ thetaG.Adj y c ∧
            ∀ w, thetaG.Adj c w → w ∈ D_int ∨ w = 0 := by
          rcases hy with rfl | rfl | rfl
          · exact ⟨2, by decide, by decide, by decide⟩
          · exact ⟨5, by decide, by decide, by decide⟩
          · exact ⟨8, by decide, by decide, by decide⟩
        obtain ⟨c, hcD, hyc, hcN⟩ := hc
        refine ⟨Function.update (zeroOn D_int x) c true, fun i hi => ?_, ?_, ?_⟩
        · have hic : i ≠ c := fun e => hi (e ▸ hcD)
          rw [Function.update_of_ne hic]; simp [zeroOn, hi]
        · rw [fTheta_eq_F]
          refine F_false_of ({c, 1} : Finset (Fin 11)) (fun i hi => ?_) (fun _ ha => by simp at ha) ?_
          · by_cases hic : i = c
            · simp [hic]
            · rw [Function.update_of_ne hic] at hi
              by_cases hiD : i ∈ D_int
              · simp [zeroOn, hiD] at hi
              · have h0or1 : i = 0 ∨ i = 1 :=
                  (by decide : ∀ i : Fin 11, i ∉ D_int → i = 0 ∨ i = 1) i hiD
                rcases h0or1 with rfl | rfl
                · simp [zeroOn, hiD, hx0] at hi
                · simp
          · intro i j hij hi hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
            rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
            · exact hij.ne rfl
            · rcases hcN 1 hij with h1D | h10
              · exact absurd h1D (by decide)
              · exact absurd h10 (by decide)
            · rcases hcN 1 hij.symm with h1D | h10
              · exact absurd h1D (by decide)
              · exact absurd h10 (by decide)
            · exact hij.ne rfl
        · rw [fTheta_eq_F]
          exact F_true_of y c hyc (by simp) (by rw [Function.update_of_ne hyc.ne.symm]; simp)
      · have hc : ∃ c : Fin 11, c ∈ D_int ∧ thetaG.Adj y c ∧
            ∀ w, thetaG.Adj c w → w ∈ D_int ∨ w = 1 := by
          rcases hy with rfl | rfl | rfl
          · exact ⟨4, by decide, by decide, by decide⟩
          · exact ⟨7, by decide, by decide, by decide⟩
          · exact ⟨10, by decide, by decide, by decide⟩
        obtain ⟨c, hcD, hyc, hcN⟩ := hc
        refine ⟨Function.update (zeroOn D_int x) c true, fun i hi => ?_, ?_, ?_⟩
        · have hic : i ≠ c := fun e => hi (e ▸ hcD)
          rw [Function.update_of_ne hic]; simp [zeroOn, hi]
        · rw [fTheta_eq_F]
          refine F_false_of ({c, 0} : Finset (Fin 11)) (fun i hi => ?_) (fun _ ha => by simp at ha) ?_
          · by_cases hic : i = c
            · simp [hic]
            · rw [Function.update_of_ne hic] at hi
              by_cases hiD : i ∈ D_int
              · simp [zeroOn, hiD] at hi
              · have h0or1 : i = 0 ∨ i = 1 :=
                  (by decide : ∀ i : Fin 11, i ∉ D_int → i = 0 ∨ i = 1) i hiD
                rcases h0or1 with rfl | rfl
                · simp
                · simp [zeroOn, hiD, hx1] at hi
          · intro i j hij hi hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
            rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
            · exact hij.ne rfl
            · rcases hcN 0 hij with h0D | h01
              · exact absurd h0D (by decide)
              · exact absurd h01 (by decide)
            · rcases hcN 0 hij.symm with h0D | h01
              · exact absurd h0D (by decide)
              · exact absurd h01 (by decide)
            · exact hij.ne rfl
        · rw [fTheta_eq_F]
          exact F_true_of y c hyc (by simp) (by rw [Function.update_of_ne hyc.ne.symm]; simp)
    obtain ⟨x', hagr, hF0, hF1⟩ := hwin
    have hne := win_pointwise L hO hF x x' hagr hF0 hF1
    cases hv : vl gs x h <;> cases hf : fixBit g <;> simp_all
  have h11 : vl gs (fun _ : Fin 11 => true) h = fixBit g := by
    by_contra hne
    have hall : ∀ x : Fin 11 → Bool, vl gs x h = !(fixBit g) := by
      intro x
      by_cases h01 : x 0 = true ∧ x 1 = true
      · have hagr : ∀ i, i ∉ D_int → x i = (fun _ : Fin 11 => true) i := by
          intro i hi
          have : i = 0 ∨ i = 1 := (by decide : ∀ i : Fin 11, i ∉ D_int → i = 0 ∨ i = 1) i hi
          rcases this with rfl | rfl <;> simp [h01.1, h01.2]
        rw [vl_dfree hF.2.2.2.2.2 x (fun _ => true) hagr]
        cases hv : vl gs (fun _ => true) h <;> cases hf : fixBit g <;> simp_all
      · apply hnot11 x
        by_cases hx0 : x 0 = false
        · exact Or.inl hx0
        · right
          have hx0t : x 0 = true := by cases h0 : x 0 <;> simp_all
          cases h1 : x 1 <;> simp_all
    have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hF.1).1
    have hlmem : l ∈ g.inputs := by rcases hF.2.2.1 with e | e <;> simp [e]
    have hllt : l < 11 + p := (L.hcl p g hF.1).lt l hlmem
    have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
      obtain ⟨x, x', hx⟩ := theta_nc y false; exact ⟨_, _, hx⟩
    refine L.no_alias hfnc p hp l hllt (fun x => ?_)
    have hbv := vl_bin gs L.hcl x p l h g hF.1 hF.2.2.1
    rcases hF.2.1 with hand | hor
    · have hh : vl gs x h = true := by rw [hall x]; simp [fixBit, hand]
      rw [hbv.2 hand, hh, Bool.and_true]
    · have hh : vl gs x h = false := by rw [hall x]; simp [fixBit, hor]
      rw [hbv.1 hor, hh, Bool.or_false]
  intro x
  by_cases h01 : x 0 = true ∧ x 1 = true
  · have hagr : ∀ i, i ∉ D_int → x i = (fun _ : Fin 11 => true) i := by
      intro i hi
      have : i = 0 ∨ i = 1 := (by decide : ∀ i : Fin 11, i ∉ D_int → i = 0 ∨ i = 1) i hi
      rcases this with rfl | rfl <;> simp [h01.1, h01.2]
    rw [vl_dfree hF.2.2.2.2.2 x (fun _ => true) hagr, h11]
    simp [h01.1, h01.2]
  · have h01' : x 0 = false ∨ x 1 = false := by
      cases hx0 : x 0 <;> cases hx1 : x 1 <;> simp_all
    rw [hnot11 x h01']
    rcases h01' with hx0 | hx1
    · simp [hx0]
    · simp [hx1]

/-! ## Unshared OR partner drop (dual of `stmtAnd`) -/

private theorem or_unshared_agree (gs : List Gate) (hcl : CleanL 11 gs) (p ph l : ℕ) (g : Gate)
    (y : Fin 11) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, 11 + ph] ∨ g.inputs = [11 + ph, l]) (hlne : l ≠ 11 + ph)
    (hone : ∀ t, Reads gs t (11 + ph) → t = p) (x : Fin 11 → Bool) (hlx : vl gs x l = true) :
    ∀ w, w ≠ 11 + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwk : w < 11
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = 11 + r := ⟨w - 11, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr; cases hr
          have hllt : l < 11 + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = true := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

private theorem or_unshared_core (gs : List Gate) (o p ph l : ℕ) (g : Gate) (y : Fin 11)
    (L : Least 11 fTheta gs o) (b : Bool) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, 11 + ph] ∨ g.inputs = [11 + ph, l]) (hlne : l ≠ 11 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (11 + ph) → t = p) (ho2 : o ≠ 11 + ph)
    (hlx : ∀ x : Fin 11 → Bool, x y = b → vl gs x l = true)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC 10 (andSwap gs ph y) y b q) :
    Drop fTheta y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin 11 → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = fTheta (Function.update x y b) := by
    intro x
    rw [or_unshared_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (Function.update_self y b x)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin 11 → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o ≠
      vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := theta_nc y b
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save 10 (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin 11 → Bool => fTheta (Function.update x y b)) =
      fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x; exact (hag x).symm
  rw [e]; exact hc

private theorem or_unshared_drop (gs : List Gate) (o p ph l : ℕ) (g : Gate) (y : Fin 11)
    (L : Least 11 fTheta gs o) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, 11 + ph] ∨ g.inputs = [11 + ph, l]) (hlit : IsLit 11 gs y l)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (11 + ph) → t = p)
    (ho1 : o ≠ 11 + p) (ho2 : o ≠ 11 + ph) :
    Drop fTheta y true 3 gs.length ∨ Drop fTheta y false 4 gs.length := by
  have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
    obtain ⟨x, x', hx⟩ := theta_nc y false; exact ⟨_, _, hx⟩
  have hlmem : l ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : 11 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : 11 + ph < 11 + p := (L.hcl p g hgp).lt _ hhmem
  have hllt : l < 11 + p := (L.hcl p g hgp).lt _ hlmem
  have hlne : l ≠ 11 + ph := by
    intro e
    apply L.no_alias hfnc p hp (11 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u p g hgp, hop]
    rcases hin with h | h <;> rw [h, ← e] <;> simp [GateOp.eval]
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (11 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p l := ⟨g, hgp', hlmem⟩
  rcases hlit with rfl | ⟨pn, rfl, hpn⟩
  · left
    have hlx : ∀ x : Fin 11 → Bool, x y = true → vl gs x y = true := by
      intro x hx; rw [vl_input gs x y y.isLt]; exact hx
    have hcp : IsC 10 (andSwap gs ph y) y true (11 + p) :=
      isC_reader hcl' y p g hgp' hlmem true (Or.inr (by simp [fixBit, hop]))
    have h3 := or_unshared_core gs o p ph y g y L true hgp hop hin hlne hph hone ho2 hlx
      {ph, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact rc_input true hphR
        · exact rc_input true hpR
        · exact rc_of_reads hSr' hcp)
    rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3
  · right
    have hpnp : pn < p := by omega
    have hpnph : pn ≠ ph := fun e => hlne (by rw [e])
    have hpn' : (andSwap gs ph y)[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
      rw [andSwap_get_ne gs ph y pn hpnph]; exact hpn
    have hlx : ∀ x : Fin 11 → Bool, x y = false → vl gs x (11 + pn) = true := by
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]
      simp [hx]
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) false (Or.inl rfl)
    have hc1 : c = true := by
      have h1 := st_val_const 10 _ hcl' y false _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1
      exact h1
    subst hc1
    have hcp : IsC 10 (andSwap gs ph y) y false (11 + p) :=
      const_read 10 _ hcl' y false p g hgp' (11 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := or_unshared_core gs o p ph (11 + pn) g y L false hgp hop hin hlne hph hone ho2 hlx
      {ph, pn, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact rc_input false hphR
        · exact rc_input false hpnR
        · exact rc_of_reads hpR ⟨true, hc⟩
        · exact rc_of_reads hSr' hcp)
    have hcard : ({ph, pn, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨pn, p, S, by omega, by omega, by omega, rfl⟩]
    rwa [hcard] at h4

/-! ## Constant-wire replacement at `x 0 = false` -/

private def constGate0 (c : Bool) : Gate :=
  if c then ⟨GateOp.not, [0]⟩ else ⟨GateOp.and, [0, 0]⟩

private theorem set_constGate0_clean (gs : List Gate) (hcl : CleanL 11 gs) (idx : ℕ)
    (hidx : idx < gs.length) (c : Bool) : CleanL 11 (gs.set idx (constGate0 c)) := by
  intro j g hj
  by_cases hje : j = idx
  · subst hje
    simp only [List.getElem?_set_self hidx, Option.some.injEq] at hj
    subst hj
    cases c
    · exact Or.inr ⟨Or.inl rfl, 0, 0, by omega, by omega, rfl⟩
    · exact Or.inl ⟨rfl, 0, by omega, rfl⟩
  · rw [List.getElem?_set_ne (Ne.symm hje)] at hj
    exact hcl j g hj

private theorem set_constGate0_agree (gs : List Gate) (hcl : CleanL 11 gs) (idx : ℕ)
    (hidx : idx < gs.length) (c : Bool) (x : Fin 11 → Bool) (hx0 : x 0 = false)
    (hval : vl gs x (11 + idx) = c) :
    ∀ w, vl (gs.set idx (constGate0 c)) x w = vl gs x w := by
  have hcl' := set_constGate0_clean gs hcl idx hidx c
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw11 : w < 11
    · rw [vl_input _ x w hw11, vl_input gs x w hw11]
    · obtain ⟨j, rfl⟩ : ∃ j, w = 11 + j := ⟨w - 11, by omega⟩
      by_cases hji : j = idx
      · subst hji
        have hget : (gs.set j (constGate0 c))[j]? = some (constGate0 c) := by simp [hidx]
        rw [vl_gate _ hcl' x j _ hget, hval]
        cases c
        · simp [constGate0, GateOp.eval, vl_input _ x 0 (by omega), hx0]
        · simp [constGate0, GateOp.eval, vl_input _ x 0 (by omega), hx0]
      · cases hj : gs[j]? with
        | none =>
          have hlen : gs.length ≤ j := List.getElem?_eq_none_iff.1 hj
          rw [vl_beyond _ x _ (by simp; omega), vl_beyond gs x _ (by omega)]
        | some g' =>
          have hj' : (gs.set idx (constGate0 c))[j]? = some g' := by
            rw [List.getElem?_set_ne (Ne.symm hji)]; exact hj
          rw [vl_gate _ hcl' x j g' hj', vl_gate gs hcl x j g' hj]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih a ((hcl j g' hj).lt a ha)

private theorem set_constGate0_isC (gs : List Gate) (hcl : CleanL 11 gs) (idx : ℕ)
    (hidx : idx < gs.length) (c : Bool) :
    IsC 10 (gs.set idx (constGate0 c)) 0 false (11 + idx) := by
  have hcl' := set_constGate0_clean gs hcl idx hidx c
  have hget : (gs.set idx (constGate0 c))[idx]? = some (constGate0 c) := by simp [hidx]
  cases c
  · exact isC_reader hcl' 0 idx _ hget (by simp [constGate0]) false (Or.inr (by simp [constGate0, fixBit]))
  · exact isC_reader hcl' 0 idx _ hget (by simp [constGate0]) false (Or.inl rfl)

private theorem set_constGate0_rc (gs : List Gate) (idx : ℕ) (hidx : idx < gs.length) (c : Bool) :
    RC 10 (gs.set idx (constGate0 c)) 0 false idx := by
  have hget : (gs.set idx (constGate0 c))[idx]? = some (constGate0 c) := by simp [hidx]
  refine rc_input false ⟨constGate0 c, hget, ?_⟩
  cases c <;> simp [constGate0]

/-! ## Shared partner drop at `x 0 = false` -/

private theorem shared_partner_drop {gs : List Gate} {o p ph r : ℕ} {g : Gate} {y : Fin 11}
    {l : ℕ} (L : Least 11 fTheta gs o) (hF : Front D_int gs p g y l (11 + ph))
    (hph : ph < gs.length) (hrp : r ≠ p) (hr : Reads gs r (11 + ph))
    (hval : ∀ x : Fin 11 → Bool, vl gs x (11 + ph) = if (x 0 && x 1) then fixBit g else !(fixBit g)) :
    Drop fTheta 0 false 4 gs.length := by
  have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
    obtain ⟨x, x', hx⟩ := theta_nc 0 false; exact ⟨_, _, hx⟩
  have hph_const : ∀ x : Fin 11 → Bool, vl gs (Function.update x 0 false) (11 + ph) = !(fixBit g) := by
    intro x
    rw [hval]
    simp
  have hphp : ph < p := by
    have hhmem : 11 + ph ∈ g.inputs := by rcases hF.2.2.1 with e | e <;> simp [e]
    have := (L.hcl p g hF.1).lt (11 + ph) hhmem
    omega
  have hphr : ph < r := by
    have := reads_lt L.hcl hr
    omega
  have hrl : r < gs.length := reads_len hr
  have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hF.1).1
  have hp_reads_ph : Reads gs p (11 + ph) :=
    ⟨g, hF.1, by rcases hF.2.2.1 with e | e <;> simp [e]⟩
  set c_h := !(fixBit g)
  set gs1 := gs.set ph (constGate0 c_h) with hgs1_def
  have hcl1 : CleanL 11 gs1 := set_constGate0_clean gs L.hcl ph hph c_h
  have hlen1 : gs1.length = gs.length := by simp [gs1]
  have hag1 : ∀ x : Fin 11 → Bool, ∀ w,
      vl gs1 (Function.update x 0 false) w = vl gs (Function.update x 0 false) w := fun x =>
    set_constGate0_agree gs L.hcl ph hph c_h (Function.update x 0 false) (by simp) (hph_const x)
  by_cases hrc : ∃ c_r : Bool, ∀ x : Fin 11 → Bool, vl gs (Function.update x 0 false) (11 + r) = c_r
  · obtain ⟨c_r, hcr⟩ := hrc
    have hor : o ≠ 11 + r := by
      intro e
      obtain ⟨x, x', hxx⟩ := theta_nc 0 false
      apply hxx
      rw [← L.hev, ← L.hev, e, hcr x, hcr x']
    obtain ⟨S, hrS, hSr⟩ := L.live hfnc r hrl hor
    have hSp : S ≠ p := by
      intro e; subst e
      obtain ⟨gS, hgS, hSm⟩ := hSr
      rw [hF.1] at hgS; cases hgS
      have hin : 11 + r = l ∨ 11 + r = 11 + ph := by
        rcases hF.2.2.1 with e | e <;> rw [e] at hSm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hSm; exact hSm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hSm; exact hSm.symm
      rcases hin with hrl' | hrph
      · rcases hF.2.2.2.2.1 with hly | ⟨pn, hlp, hpn⟩
        · have := y.isLt; omega
        · have hre : r = pn := by omega
          subst hre
          obtain ⟨gr, hgr, hrm⟩ := hr
          rw [hpn] at hgr; cases hgr
          simp only [List.mem_singleton] at hrm
          have := y.isLt; omega
      · omega
    set gs2 := gs1.set r (constGate0 c_r) with hgs2_def
    have hcl2 : CleanL 11 gs2 := set_constGate0_clean gs1 hcl1 r (by omega) c_r
    have hlen2 : gs2.length = gs.length := by simp [gs2, gs1]
    have hag2 : ∀ x : Fin 11 → Bool,
        vl gs2 (Function.update x 0 false) o = fTheta (Function.update x 0 false) := by
      intro x
      have h1 : vl gs1 (Function.update x 0 false) (11 + r) = c_r := by rw [hag1]; exact hcr x
      rw [set_constGate0_agree gs1 hcl1 r (by omega) c_r (Function.update x 0 false) (by simp) h1 o,
        hag1 x o, L.hev]
    have hnc2 : ∃ x x' : Fin 11 → Bool,
        vl gs2 (Function.update x 0 false) o ≠ vl gs2 (Function.update x' 0 false) o := by
      obtain ⟨x, x', h⟩ := theta_nc 0 false
      exact ⟨x, x', by rw [hag2, hag2]; exact h⟩
    have hget_ph2 : gs2[ph]? = some (constGate0 c_h) := by
      rw [hgs2_def, List.getElem?_set_ne (by omega), hgs1_def, List.getElem?_set_self hph]
    have hph_isC : IsC 10 gs2 0 false (11 + ph) := by
      cases hc : c_h
      · rw [hc] at hget_ph2
        exact isC_reader hcl2 0 ph _ hget_ph2 (by simp [constGate0]) false
          (Or.inr (by simp [constGate0, fixBit]))
      · rw [hc] at hget_ph2
        exact isC_reader hcl2 0 ph _ hget_ph2 (by simp [constGate0]) false (Or.inl rfl)
    have hph_rc : RC 10 gs2 0 false ph := by
      refine rc_input false ⟨constGate0 c_h, hget_ph2, ?_⟩
      cases hc : c_h <;> simp [constGate0]
    have hr_isC : IsC 10 gs2 0 false (11 + r) :=
      set_constGate0_isC gs1 hcl1 r (by omega) c_r
    have hr_rc : RC 10 gs2 0 false r := set_constGate0_rc gs1 r (by omega) c_r
    have hp_reads2 : Reads gs2 p (11 + ph) := by
      obtain ⟨gp, hgp, hpm⟩ := hp_reads_ph
      exact ⟨gp, by rw [hgs2_def, List.getElem?_set_ne hrp, hgs1_def,
        List.getElem?_set_ne (by omega)]; exact hgp, hpm⟩
    have hS_reads2 : Reads gs2 S (11 + r) := by
      obtain ⟨gS, hgS, hSm⟩ := hSr
      exact ⟨gS, by rw [hgs2_def, List.getElem?_set_ne (by omega), hgs1_def,
        List.getElem?_set_ne (by omega)]; exact hgS, hSm⟩
    obtain ⟨s', hs', hc⟩ := save 10 (fun x => vl gs2 x o) gs2 o hcl2 (fun _ => rfl) 0 false hnc2
      {ph, r, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hph_rc
        · exact hr_rc
        · exact rc_of_reads hp_reads2 hph_isC
        · exact rc_of_reads hS_reads2 hr_isC)
    have hcard : ({ph, r, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨r, p, S, hrp, by omega, Ne.symm hSp, rfl⟩]
    rw [hcard, hlen2] at hs'
    refine ⟨s', hs', ?_⟩
    have e : (fun x : Fin 11 → Bool => fTheta (Function.update x 0 false)) =
        fun x => (fun x => vl gs2 x o) (Function.update x 0 false) := by
      funext x; exact (hag2 x).symm
    rw [e]; exact hc
  · -- `r` is not semantically constant at `x 0 = false`, so find `q ≠ ph` reading `0`
    have hq_ex : ∃ q, Reads gs q 0 ∧ q ≠ ph := by
      by_contra hno
      push Not at hno
      let u : Fin 11 → Bool := fun i => if i = 2 then true else false
      let u' : Fin 11 → Bool := fun i => if i = 0 ∨ i = 2 then true else false
      have ho0 : o ≠ 0 := out_ne_lit L.hcl L.hev 0 (theta_nc 0) 0 (Or.inl rfl)
      have hagree : vl gs u o = vl gs u' o := by
        refine agree_B gs L.hcl u u' (fun w => w = 0) (o + 1) ?_ ?_ o (by omega) ho0
        · intro a ha hB
          rw [vl_input gs u a ha, vl_input gs u' a ha]
          have ha0 : (⟨a, ha⟩ : Fin 11) ≠ 0 := fun e => hB (congrArg Fin.val e)
          simp [u, u', ha0]
        · intro q g' hq _ _ hr _
          obtain ⟨a, ha, ha0⟩ := hr
          have hqph : q = ph := hno q ⟨g', hq, ha0 ▸ ha⟩
          rw [hqph, hval u, hval u']
          simp [u, u']
      rw [L.hev, L.hev] at hagree
      have hu : fTheta u = false := by decide
      have hu' : fTheta u' = true := by decide
      rw [hu, hu'] at hagree
      cases hagree
    obtain ⟨q, hq0, hqph⟩ := hq_ex
    have hqp : q ≠ p := by
      intro e; subst e
      obtain ⟨gq, hgq, hqm⟩ := hq0
      rw [hF.1] at hgq; cases hgq
      have h0in : 0 = l ∨ 0 = 11 + ph := by
        rcases hF.2.2.1 with e | e <;> rw [e] at hqm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm; exact hqm
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm; exact hqm.symm
      rcases h0in with h0l | h0ph
      · rcases hF.2.2.2.2.1 with hly | ⟨pn, hlp, _⟩
        · have hy0 : y = 0 := Fin.ext (by omega)
          have := hF.2.2.2.1
          rw [hy0] at this
          exact absurd this (by decide)
        · omega
      · omega
    have hqr : q ≠ r := by
      intro e; subst e
      apply hrc
      obtain ⟨gr, hgr, hr0⟩ := hq0
      obtain ⟨gr2, hgr2, hrph⟩ := hr
      rw [hgr] at hgr2; cases hgr2
      rcases L.hcl q gr hgr with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩
      · rw [hin] at hr0 hrph
        simp only [List.mem_singleton] at hr0 hrph
        omega
      · rw [hin] at hr0 hrph
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr0 hrph
        have hjk : (j = 0 ∧ k = 11 + ph) ∨ (j = 11 + ph ∧ k = 0) := by omega
        rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨gr.op.eval [false, c_h], fun x => ?_⟩
          rw [vl_gate gs L.hcl _ q gr hgr, hin]
          simp only [List.map_cons, List.map_nil]
          rw [vl_input gs _ 0 (by omega), hph_const x]
          simp
        · refine ⟨gr.op.eval [c_h, false], fun x => ?_⟩
          rw [vl_gate gs L.hcl _ q gr hgr, hin]
          simp only [List.map_cons, List.map_nil]
          rw [vl_input gs _ 0 (by omega), hph_const x]
          simp
    have hag1o : ∀ x : Fin 11 → Bool,
        vl gs1 (Function.update x 0 false) o = fTheta (Function.update x 0 false) := by
      intro x; rw [hag1 x o, L.hev]
    have hnc1 : ∃ x x' : Fin 11 → Bool,
        vl gs1 (Function.update x 0 false) o ≠ vl gs1 (Function.update x' 0 false) o := by
      obtain ⟨x, x', h⟩ := theta_nc 0 false
      exact ⟨x, x', by rw [hag1o, hag1o]; exact h⟩
    have hph_isC : IsC 10 gs1 0 false (11 + ph) := set_constGate0_isC gs L.hcl ph hph c_h
    have hph_rc : RC 10 gs1 0 false ph := set_constGate0_rc gs ph hph c_h
    have hp_reads1 : Reads gs1 p (11 + ph) := by
      obtain ⟨gp, hgp, hpm⟩ := hp_reads_ph
      exact ⟨gp, by rw [hgs1_def, List.getElem?_set_ne (by omega)]; exact hgp, hpm⟩
    have hr_reads1 : Reads gs1 r (11 + ph) := by
      obtain ⟨gr, hgr, hrm⟩ := hr
      exact ⟨gr, by rw [hgs1_def, List.getElem?_set_ne (by omega)]; exact hgr, hrm⟩
    have hq_reads1 : Reads gs1 q 0 := by
      obtain ⟨gq, hgq, hqm⟩ := hq0
      exact ⟨gq, by rw [hgs1_def, List.getElem?_set_ne (Ne.symm hqph)]; exact hgq, hqm⟩
    obtain ⟨s', hs', hc⟩ := save 10 (fun x => vl gs1 x o) gs1 o hcl1 (fun _ => rfl) 0 false hnc1
      {ph, p, r, q} (by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl
        · exact hph_rc
        · exact rc_of_reads hp_reads1 hph_isC
        · exact rc_of_reads hr_reads1 hph_isC
        · exact rc_input false hq_reads1)
    have hcard : ({ph, p, r, q} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hqph]; omega),
        Finset.card_eq_three.2 ⟨p, r, q, Ne.symm hrp, Ne.symm hqp, Ne.symm hqr, rfl⟩]
    rw [hcard, hlen1] at hs'
    refine ⟨s', hs', ?_⟩
    have e : (fun x : Fin 11 → Bool => fTheta (Function.update x 0 false)) =
        fun x => (fun x => vl gs1 x o) (Function.update x 0 false) := by
      funext x; exact (hag1o x).symm
    rw [e]; exact hc

/-! ## Combining all cases for `16 ≤ s` -/

private theorem pays_gives_16 (y : Fin 11) (hy : y ∈ D_int) (s : ℕ)
    (hp : Pays fTheta y s) : 16 ≤ s := by
  have horb : (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) ∨ (y = 3 ∨ y = 6 ∨ y = 9) := by
    have key : ∀ y : Fin 11, y ∈ D_int →
        (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) ∨ (y = 3 ∨ y = 6 ∨ y = 9) := by
      decide
    exact key y hy
  rcases horb with hadj | hmid
  · rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩
    · have := lb_adjBranch_false y hadj s' h2; omega
    · have := lb_adjBranch_false y hadj s' h2; omega
    · have := lb_adjBranch_false y hadj s' h2; omega
  · rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
    · have := lb_mid_false y hmid s' h2; omega
    · have := lb_mid_false y hmid s' h2; omega
    · have := lb_mid_true y hmid s' h2; omega

private theorem main_lb (s : ℕ) (hC : HasCircuitSize 11 fTheta s) : 16 ≤ s := by
  have hfnc : ∃ x x' : Fin 11 → Bool, fTheta x ≠ fTheta x' := by
    obtain ⟨x, x', hx⟩ := theta_nc 2 false; exact ⟨_, _, hx⟩
  obtain ⟨gs, o, L, hls⟩ := exists_least 11 fTheta s hfnc hC
  suffices h16 : 16 ≤ gs.length by omega
  by_cases hOR : OneReader D_int gs
  · obtain ⟨p, g, y, l, h, hF, hop⟩ := theta_get_front L hOR
    have horb : (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) ∨ (y = 3 ∨ y = 6 ∨ y = 9) := by
      have key : ∀ y : Fin 11, y ∈ D_int →
          (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) ∨ (y = 3 ∨ y = 6 ∨ y = 9) := by
        decide
      exact key y hF.2.2.2.1
    rcases horb with hadj | hmid
    · exact absurd hadj (fun h' => front_not_adjBranch L hOR hF h')
    · have hval := front_mid_partner L hOR hF hmid
      have hh11 : 11 ≤ h := by
        by_contra hlt
        have hlt' : h < 11 := by omega
        have h00 := hval (fun _ => false)
        have h10 := hval (fun i => if i = 0 then true else false)
        have h01 := hval (fun i => if i = 1 then true else false)
        have h11 := hval (fun _ => true)
        rw [vl_input gs _ h hlt'] at h00 h10 h01 h11
        by_cases h0 : h = 0
        · subst h0; simp at h10 h11; rw [h10] at h11; cases fixBit g <;> simp at h11
        · by_cases h1 : h = 1
          · subst h1; simp at h01 h11; rw [h01] at h11; cases fixBit g <;> simp at h11
          · have : (⟨h, hlt'⟩ : Fin 11) ≠ 0 ∧ (⟨h, hlt'⟩ : Fin 11) ≠ 1 :=
              ⟨fun e => h0 (congrArg Fin.val e), fun e => h1 (congrArg Fin.val e)⟩
            have hD' : (⟨h, hlt'⟩ : Fin 11) ∈ D_int := by
              have key : ∀ i : Fin 11, i ≠ 0 → i ≠ 1 → i ∈ D_int := by decide
              exact key ⟨h, hlt'⟩ this.1 this.2
            have := hF.2.2.2.2.2 ⟨h, hlt'⟩ hD'
            rw [front_supp_input gs h hlt'] at this
            exact this (by simp)
      have hhmem : h ∈ g.inputs := by rcases hF.2.2.1 with e | e <;> simp [e]
      have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hF.1).1
      have hhlt : h < 11 + p := (L.hcl p g hF.1).lt h hhmem
      obtain ⟨ph, rfl⟩ : ∃ ph, h = 11 + ph := ⟨h - 11, by omega⟩
      have hph : ph < gs.length := by omega
      have hoh : o ≠ 11 + ph := by
        rintro rfl
        have hy := theta_supp_out L y
        exact hF.2.2.2.2.2 y hF.2.2.2.1 hy
      by_cases hsh : ∃ r, r ≠ p ∧ Reads gs r (11 + ph)
      · obtain ⟨r, hrp, hr⟩ := hsh
        obtain ⟨s', hs', hc'⟩ := shared_partner_drop L hF hph hrp hr hval
        have := lb_zero_false s' hc'
        omega
      · have hone : ∀ t, Reads gs t (11 + ph) → t = p := by
          intro t ht
          by_contra hne
          exact hsh ⟨t, hne, ht⟩
        rcases hF.2.1 with hand | hor
        · have hA := stmtAnd 10 fTheta gs o p ph l g y L (theta_nc y) (theta_dep y)
            hF.1 hand hF.2.2.1 hF.2.2.2.2.1 hph hone hop hoh
          by_cases hl : l = (y : ℕ)
          · obtain ⟨s', hs', hc'⟩ := hA.1 hl
            have := lb_mid_false y hmid s' hc'
            omega
          · obtain ⟨s', hs', hc'⟩ := hA.2 hl
            have := lb_mid_true y hmid s' hc'
            omega
        · rcases or_unshared_drop gs o p ph l g y L hF.1 hor hF.2.2.1 hF.2.2.2.2.1
              hph hone hop hoh with ⟨s', hs', hc'⟩ | ⟨s', hs', hc'⟩
          · have := lb_mid_true y hmid s' hc'
            omega
          · have := lb_mid_false y hmid s' hc'
            omega
  · simp only [OneReader, not_and_or] at hOR
    push Not at hOR
    rcases hOR with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · exact pays_gives_16 y hy gs.length (L.two_readers y (theta_nc y) p q hpq hp hq)
    · obtain ⟨d0, d1⟩ := L.not_two_readers y (theta_nc y) pn _ hpn rfl (by simp) p q hpq hp hq
      exact pays_gives_16 y hy gs.length (Or.inl ⟨d0, d1⟩)

end PEqualNP.Outside.L_meta_657

theorem PEqualNP.Outside.L_meta_657 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 11 (fun x : Fin 11 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)) s → 16 ≤ s :=
  PEqualNP.Outside.L_meta_657.main_lb
