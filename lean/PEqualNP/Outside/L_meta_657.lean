import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L532

namespace PEqualNP.Outside.L_meta_657_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Helpers.Forest PEqualNP.MetaComplexity.EdgeFn
open PEqualNP.MetaComplexity.Loc PEqualNP.Library.Peel PEqualNP.Library.Peel.Scratch
open SimpleGraph

def thetaEdge (i j : Fin 11) : Bool :=
  (i == 0 && j == 2) || (i == 2 && j == 3) || (i == 3 && j == 4) || (i == 4 && j == 1) ||
  (i == 0 && j == 5) || (i == 5 && j == 6) || (i == 6 && j == 7) || (i == 7 && j == 1) ||
  (i == 0 && j == 8) || (i == 8 && j == 9) || (i == 9 && j == 10) || (i == 10 && j == 1)

abbrev G : SimpleGraph (Fin 11) := SimpleGraph.fromRel (fun i j => thetaEdge i j = true)

abbrev target (x : Fin 11 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) ||
  (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) ||
  (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)

theorem thetaEdge_iff : ∀ i j : Fin 11, thetaEdge i j = true ↔
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 1) ∨
    (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 1) ∨
    (i = 0 ∧ j = 8) ∨ (i = 8 ∧ j = 9) ∨ (i = 9 ∧ j = 10) ∨ (i = 10 ∧ j = 1) := by decide

theorem F_eq_target : F G ∅ = target := by
  funext x
  rw [Bool.eq_iff_iff, F_true]
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, target,
    Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases hij with ⟨_, h | h⟩
    · rw [thetaEdge_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hi, hj]
    · rw [thetaEdge_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hi, hj]
  · intro h
    rcases h with (((((((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
      ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
      ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨0, 2, by decide, h1, h2⟩
    · exact ⟨2, 3, by decide, h1, h2⟩
    · exact ⟨3, 4, by decide, h1, h2⟩
    · exact ⟨4, 1, by decide, h1, h2⟩
    · exact ⟨0, 5, by decide, h1, h2⟩
    · exact ⟨5, 6, by decide, h1, h2⟩
    · exact ⟨6, 7, by decide, h1, h2⟩
    · exact ⟨7, 1, by decide, h1, h2⟩
    · exact ⟨0, 8, by decide, h1, h2⟩
    · exact ⟨8, 9, by decide, h1, h2⟩
    · exact ⟨9, 10, by decide, h1, h2⟩
    · exact ⟨10, 1, by decide, h1, h2⟩

def swapHubs (i : Fin 11) : Fin 11 :=
  match i.val with
  | 0 => 1 | 1 => 0
  | 2 => 4 | 3 => 3 | 4 => 2
  | 5 => 7 | 6 => 6 | 7 => 5
  | 8 => 10 | 9 => 9 | _ => 8

def rotPaths (i : Fin 11) : Fin 11 :=
  match i.val with
  | 0 => 0 | 1 => 1
  | 2 => 5 | 3 => 6 | 4 => 7
  | 5 => 8 | 6 => 9 | 7 => 10
  | 8 => 2 | 9 => 3 | _ => 4

def rotPathsInv (i : Fin 11) : Fin 11 := rotPaths (rotPaths i)

theorem swapHubs_inv : ∀ i : Fin 11, swapHubs (swapHubs i) = i := by decide
theorem rotPaths_inv1 : ∀ i : Fin 11, rotPathsInv (rotPaths i) = i := by decide
theorem rotPaths_inv2 : ∀ i : Fin 11, rotPaths (rotPathsInv i) = i := by decide
theorem G_adj_swap : ∀ i j : Fin 11, G.Adj (swapHubs i) (swapHubs j) ↔ G.Adj i j := by decide
theorem G_adj_rot : ∀ i j : Fin 11, G.Adj (rotPaths i) (rotPaths j) ↔ G.Adj i j := by decide
theorem G_adj_rotInv : ∀ i j : Fin 11, G.Adj (rotPathsInv i) (rotPathsInv j) ↔ G.Adj i j := by
  decide

theorem F_comp_aut (π π' : Fin 11 → Fin 11) (_ : ∀ i, π' (π i) = i) (h2 : ∀ i, π (π' i) = i)
    (hadj : ∀ i j, G.Adj (π i) (π j) ↔ G.Adj i j) (x : Fin 11 → Bool) :
    F G ∅ (x ∘ π) = F G ∅ x := by
  apply F_eq
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, Function.comp_apply]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨π i, π j, (hadj i j).2 hij, hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨π' i, π' j, (hadj _ _).1 (by rwa [h2, h2]), by rwa [h2], by rwa [h2]⟩

theorem restrict_aut (π π' : Fin 11 → Fin 11) (h1 : ∀ i, π' (π i) = i) (h2 : ∀ i, π (π' i) = i)
    (hadj : ∀ i j, G.Adj (π i) (π j) ↔ G.Adj i j) (v : Fin 11) (b : Bool) (s' : ℕ)
    (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x (π v) b)) s') :
    HasCircuitSize 11 (fun x => F G ∅ (Function.update x v b)) s' := by
  have h' := relabel_size π' _ s' h
  have heq : (fun x : Fin 11 → Bool => F G ∅ (Function.update (x ∘ π') (π v) b)) =
      fun x => F G ∅ (Function.update x v b) := by
    funext x
    have hupd : Function.update (x ∘ π') (π v) b = (Function.update x v b) ∘ π' := by
      funext j
      by_cases hj : j = π v
      · subst hj; simp [Function.comp_apply, h1]
      · have hj' : π' j ≠ v := fun e => hj (by rw [← e, h2])
        simp [Function.update_of_ne hj, Function.update_of_ne hj', Function.comp_apply]
    rw [hupd]
    exact F_comp_aut π' π h2 h1 (fun i j => by rw [← hadj (π' i) (π' j), h2, h2]) _
  rwa [heq] at h'

theorem isAcyclic_of_depth {n : ℕ} (H : SimpleGraph (Fin n)) (d : Fin n → ℕ)
    (hneq : ∀ u v, H.Adj u v → d u ≠ d v)
    (huniq : ∀ v u1 u2, H.Adj v u1 → H.Adj v u2 → d u1 < d v → d u2 < d v → u1 = u2) :
    H.IsAcyclic := by
  intro v c hc
  have hL : 3 ≤ c.length := hc.three_le_length
  have hne : (Finset.range c.length).Nonempty := ⟨0, Finset.mem_range.2 (by omega)⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range c.length) (fun k => d (c.getVert k)) hne
  have hiL : i < c.length := Finset.mem_range.1 hi
  have hv0L : c.getVert c.length = c.getVert 0 :=
    (Walk.getVert_length c).trans (Walk.getVert_zero c).symm
  have hall : ∀ k ≤ c.length, d (c.getVert k) ≤ d (c.getVert i) := by
    intro k hk
    by_cases hkL : k < c.length
    · exact hmax k (Finset.mem_range.2 hkL)
    · have hk0 : k = c.length := by omega
      subst hk0
      rw [hv0L]
      exact hmax 0 (Finset.mem_range.2 (by omega))
  have hadj1 : H.Adj (c.getVert i) (c.getVert (i + 1)) := c.adj_getVert_succ hiL
  have hlt1 : d (c.getVert (i + 1)) < d (c.getVert i) :=
    lt_of_le_of_ne (hall (i + 1) (by omega)) (Ne.symm (hneq _ _ hadj1))
  have htail : c.support.tail.Nodup := hc.support_nodup
  have hget : ∀ k, k < c.length → c.support.tail[k]? = some (c.getVert (k + 1)) := by
    intro k hk
    have hs : c.support[k + 1]? = some (c.getVert (k + 1)) := by
      rw [List.getElem?_eq_getElem (by rw [Walk.length_support]; omega)]
      exact congrArg some (Walk.getVert_eq_support_getElem c (by omega)).symm
    cases hsup : c.support with
    | nil => simp [Walk.support_ne_nil] at hsup
    | cons a l =>
      rw [hsup] at hs
      simpa using hs
  have hne_get : ∀ a b, a < c.length → b < c.length → a ≠ b →
      c.getVert (a + 1) ≠ c.getVert (b + 1) := by
    intro a b ha hb hab heq
    have ha' : a < c.support.tail.length := by simp [Walk.length_support]; omega
    have hb' : b < c.support.tail.length := by simp [Walk.length_support]; omega
    have h1 := hget a ha
    have h2 := hget b hb
    rw [List.getElem?_eq_getElem ha'] at h1
    rw [List.getElem?_eq_getElem hb'] at h2
    have hval : c.support.tail[a] = c.support.tail[b] := by
      rw [Option.some.inj h1, Option.some.inj h2, heq]
    exact hab ((List.Nodup.getElem_inj_iff htail).1 hval)
  by_cases hi0 : i = 0
  · subst hi0
    have hadj2 : H.Adj (c.getVert 0) (c.getVert (c.length - 1)) := by
      have h := c.adj_getVert_succ (i := c.length - 1) (by omega)
      rw [show c.length - 1 + 1 = c.length by omega, hv0L] at h
      exact h.symm
    have hlt2 : d (c.getVert (c.length - 1)) < d (c.getVert 0) :=
      lt_of_le_of_ne (hall (c.length - 1) (by omega)) (Ne.symm (hneq _ _ hadj2))
    have heq := huniq _ _ _ hadj1 hadj2 hlt1 hlt2
    have hne' := hne_get 0 (c.length - 2) (by omega) (by omega) (by omega)
    rw [show c.length - 2 + 1 = c.length - 1 by omega] at hne'
    exact hne' heq
  · have hadj2 : H.Adj (c.getVert i) (c.getVert (i - 1)) := by
      have h := c.adj_getVert_succ (i := i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at h
      exact h.symm
    have hlt2 : d (c.getVert (i - 1)) < d (c.getVert i) :=
      lt_of_le_of_ne (hall (i - 1) (by omega)) (Ne.symm (hneq _ _ hadj2))
    have heq := huniq _ _ _ hadj1 hadj2 hlt1 hlt2
    by_cases hi1 : i = 1
    · subst hi1
      have hne' := hne_get 1 (c.length - 1) (by omega) (by omega) (by omega)
      rw [show c.length - 1 + 1 = c.length by omega, hv0L] at hne'
      exact hne' heq
    · have hne' := hne_get i (i - 2) (by omega) (by omega) (by omega)
      rw [show i - 2 + 1 = i - 1 by omega] at hne'
      exact hne' heq

theorem edgeSet_ncard_eq_of_finset (H : SimpleGraph (Fin 11)) (E : Finset (Sym2 (Fin 11)))
    (hE : ∀ i j : Fin 11, H.Adj i j ↔ s(i, j) ∈ E) : H.edgeSet.ncard = E.card := by
  have heq : H.edgeSet = (E : Set (Sym2 (Fin 11))) := by
    ext e
    induction e using Sym2.ind with
    | _ i j => exact hE i j
  rw [heq, Set.ncard_coe_finset]

theorem cov_ge_of_matching {k : ℕ} (H : SimpleGraph (Fin 11)) (a b : Fin k → Fin 11)
    (hM : ∀ i : Fin k, H.Adj (a i) (b i))
    (hdisj : ∀ i j : Fin k, i ≠ j →
      a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j)
    (T : Finset (Fin 11)) (hT : ∀ u v : Fin 11, H.Adj u v → u ∈ T ∨ v ∈ T) :
    k ≤ T.card := by
  classical
  have hcard : (Finset.univ : Finset (Fin k)).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun i => if a i ∈ T then a i else b i) ?_ ?_
    · intro i _
      simp only [Finset.mem_coe]
      by_cases h1 : a i ∈ T
      · simp [h1]
      · simp only [h1, ite_false]
        rcases hT (a i) (b i) (hM i) with h | h
        · exact absurd h h1
        · exact h
    · intro i _ j _ heq
      by_contra hne
      obtain ⟨h11, h12, h21, h22⟩ := hdisj i j hne
      by_cases a1 : a i ∈ T <;> by_cases a2 : a j ∈ T <;> simp [a1, a2] at heq
      · exact h11 heq
      · exact h12 heq
      · exact h21 heq
      · exact h22 heq
  simpa using hcard

def depthDel0 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0
  | 4 | 7 | 10 => 1
  | 3 | 6 | 9 => 2
  | 2 | 5 | 8 => 3
  | _ => 0

theorem peelable_del0 : Peelable (delVerts G {0}) :=
  peelable_of_isAcyclic (isAcyclic_of_depth (delVerts G {0}) depthDel0 (by decide) (by decide))

def depthDel23v7 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0 | 4 => 1 | 10 => 1 | 9 => 2 | 8 => 3 | 0 => 4 | 5 => 5 | 6 => 6 | _ => 0

def depthDel23v6 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0 | 4 => 1 | 7 => 1 | 10 => 1 | 9 => 2 | 8 => 3 | 0 => 4 | 5 => 5 | _ => 0

def depthDel23v5 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0 | 4 => 1 | 7 => 1 | 6 => 2 | 10 => 1 | 9 => 2 | 8 => 3 | 0 => 4 | _ => 0

def depthDel23v0 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0 | 4 => 1 | 7 => 1 | 6 => 2 | 5 => 3 | 10 => 1 | 9 => 2 | 8 => 3 | _ => 0

def depthDel23v8 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0 | 4 => 1 | 7 => 1 | 6 => 2 | 5 => 3 | 0 => 4 | 10 => 1 | 9 => 2 | _ => 0

def depthDel23v9 (v : Fin 11) : ℕ :=
  match v.val with
  | 1 => 0 | 4 => 1 | 7 => 1 | 6 => 2 | 5 => 3 | 0 => 4 | 8 => 5 | 10 => 1 | _ => 0

theorem acyclic_del23_of_mem (X : Finset (Fin 11))
    (hmem : (7 : Fin 11) ∈ X ∨ 6 ∈ X ∨ 5 ∈ X ∨ 0 ∈ X ∨ 8 ∈ X ∨ 9 ∈ X) :
    (delVerts (delVerts G {2, 3}) X).IsAcyclic := by
  have hle : ∀ v : Fin 11, v ∈ X → delVerts (delVerts G {2, 3}) X ≤ delVerts (delVerts G {2, 3}) {v} := by
    intro v hv i j h
    exact ⟨h.1, fun hi => h.2.1 (by rw [Finset.mem_singleton] at hi; exact hi ▸ hv),
      fun hj => h.2.2 (by rw [Finset.mem_singleton] at hj; exact hj ▸ hv)⟩
  rcases hmem with hv | hv | hv | hv | hv | hv
  · exact (isAcyclic_of_depth _ depthDel23v7 (by decide) (by decide)).anti (hle 7 hv)
  · exact (isAcyclic_of_depth _ depthDel23v6 (by decide) (by decide)).anti (hle 6 hv)
  · exact (isAcyclic_of_depth _ depthDel23v5 (by decide) (by decide)).anti (hle 5 hv)
  · exact (isAcyclic_of_depth _ depthDel23v0 (by decide) (by decide)).anti (hle 0 hv)
  · exact (isAcyclic_of_depth _ depthDel23v8 (by decide) (by decide)).anti (hle 8 hv)
  · exact (isAcyclic_of_depth _ depthDel23v9 (by decide) (by decide)).anti (hle 9 hv)

theorem peelable_del23 : Peelable (delVerts G {2, 3}) := by
  intro X hE
  by_cases hmem : (7 : Fin 11) ∈ X ∨ 6 ∈ X ∨ 5 ∈ X ∨ 0 ∈ X ∨ 8 ∈ X ∨ 9 ∈ X
  · exact Or.inl (forest_good_leaf _ (acyclic_del23_of_mem X hmem) hE)
  · push Not at hmem
    obtain ⟨h7, h6, h5, h0, h8, h9⟩ := hmem
    right
    refine ⟨7, 6, 5, 0, 8, 9, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w
      simp only [delVerts_adj]
      constructor
      · intro hw
        have : w = 7 ∨ w = 5 := (by decide : ∀ w : Fin 11, (delVerts G {2, 3}).Adj 6 w → w = 7 ∨ w = 5) w hw.1
        exact this
      · rintro (rfl | rfl)
        · exact ⟨by decide, h6, h7⟩
        · exact ⟨by decide, h6, h5⟩
    · intro w
      simp only [delVerts_adj]
      constructor
      · intro hw
        exact (by decide : ∀ w : Fin 11, (delVerts G {2, 3}).Adj 5 w → w = 6 ∨ w = 0) w hw.1
      · rintro (rfl | rfl)
        · exact ⟨by decide, h5, h6⟩
        · exact ⟨by decide, h5, h0⟩
    · intro w
      simp only [delVerts_adj]
      constructor
      · intro hw
        exact (by decide : ∀ w : Fin 11, (delVerts G {2, 3}).Adj 0 w → w = 5 ∨ w = 8) w hw.1
      · rintro (rfl | rfl)
        · exact ⟨by decide, h0, h5⟩
        · exact ⟨by decide, h0, h8⟩
    · intro w
      simp only [delVerts_adj]
      constructor
      · intro hw
        exact (by decide : ∀ w : Fin 11, (delVerts G {2, 3}).Adj 8 w → w = 0 ∨ w = 9) w hw.1
      · rintro (rfl | rfl)
        · exact ⟨by decide, h8, h0⟩
        · exact ⟨by decide, h8, h9⟩
    · refine ⟨1, fun w hw => ?_⟩
      exact (by decide : ∀ w : Fin 11, (delVerts G {2, 3}).Adj 7 w → w = 6 ∨ w = 1) w hw.1
    · refine ⟨10, fun w hw => ?_⟩
      exact (by decide : ∀ w : Fin 11, (delVerts G {2, 3}).Adj 9 w → w = 8 ∨ w = 10) w hw.1

theorem peelable_del234 : Peelable (delVerts G {2, 3, 4}) := by
  have heq : delVerts G {2, 3, 4} = delVerts (delVerts G {2, 3}) {4} := by
    ext i j
    simp only [delVerts_adj, Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  rw [heq]
  exact Peelable.delVerts peelable_del23 {4}

theorem peelable_del2 : Peelable (delVerts G {2}) := by
  intro X hE
  by_cases h34 : (3 : Fin 11) ∉ X ∧ (4 : Fin 11) ∉ X
  · left
    refine ⟨3, 4, ⟨by decide, h34.1, h34.2⟩, ?_, Or.inl ⟨1, ?_⟩⟩
    · intro w hw
      exact (by decide : ∀ w : Fin 11, (delVerts G {2}).Adj 3 w → w = 4) w hw.1
    · intro w hw
      exact (by decide : ∀ w : Fin 11, (delVerts G {2}).Adj 4 w → w = 3 ∨ w = 1) w hw.1
  · have heq : delVerts (delVerts G {2}) X = delVerts (delVerts G {2, 3}) X := by
      ext i j
      simp only [delVerts_adj, Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · rintro ⟨⟨hij, hi2, hj2⟩, hiX, hjX⟩
        refine ⟨⟨hij, ⟨hi2, fun hi3 => ?_⟩, ⟨hj2, fun hj3 => ?_⟩⟩, hiX, hjX⟩
        · subst hi3
          have hj4 : j = 4 := (by decide : ∀ w : Fin 11, G.Adj 3 w → w ≠ 2 → w = 4) j hij hj2
          subst hj4
          exact h34 ⟨hiX, hjX⟩
        · subst hj3
          have hi4 : i = 4 := (by decide : ∀ w : Fin 11, G.Adj w 3 → w ≠ 2 → w = 4) i hij hi2
          subst hi4
          exact h34 ⟨hjX, hiX⟩
      · rintro ⟨⟨hij, ⟨hi2, _⟩, ⟨hj2, _⟩⟩, hiX, hjX⟩
        exact ⟨⟨hij, hi2, hj2⟩, hiX, hjX⟩
    rw [heq] at hE ⊢
    exact peelable_del23 X hE

theorem lb_del0 (s' : ℕ) (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x 0 false)) s') :
    12 ≤ s' := by
  have hr : (fun x => F G ∅ (Function.update x 0 false)) = F (delVerts G {0}) ∅ := by
    funext x
    rw [Res.ToolRes0_proof 11 G ∅ 0 x (by simp), delV_eq]
  rw [hr] at h
  have hE : (delVerts G {0}).edgeSet.ncard = 9 := by
    have h1 := edgeSet_ncard_eq_of_finset (delVerts G {0})
      {s(2, 3), s(3, 4), s(4, 1), s(5, 6), s(6, 7), s(7, 1), s(8, 9), s(9, 10), s(10, 1)}
      (by decide)
    rw [h1]; decide
  have hk : ∀ T : Finset (Fin 11), (∀ i j, (delVerts G {0}).Adj i j → i ∈ T ∨ j ∈ T) → 4 ≤ T.card := by
    intro T hT
    exact cov_ge_of_matching (k := 4) (delVerts G {0}) ![2, 4, 5, 8] ![3, 1, 6, 9]
      (by decide) (by decide) T hT
  have hb := PEqualNP.MetaComplexity.L532 11 4 s' (delVerts G {0}) ∅ peelable_del0
    (by simp) (Or.inr ⟨2, 3, by decide⟩) hk h
  rw [Finset.card_empty, hE] at hb
  omega

theorem lb_del2 (s' : ℕ) (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x 2 false)) s') :
    14 ≤ s' := by
  have hr : (fun x => F G ∅ (Function.update x 2 false)) = F (delVerts G {2}) ∅ := by
    funext x
    rw [Res.ToolRes0_proof 11 G ∅ 2 x (by simp), delV_eq]
  rw [hr] at h
  have hE : (delVerts G {2}).edgeSet.ncard = 10 := by
    have h1 := edgeSet_ncard_eq_of_finset (delVerts G {2})
      {s(3, 4), s(4, 1), s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
      (by decide)
    rw [h1]; decide
  have hk : ∀ T : Finset (Fin 11), (∀ i j, (delVerts G {2}).Adj i j → i ∈ T ∨ j ∈ T) → 5 ≤ T.card := by
    intro T hT
    exact cov_ge_of_matching (k := 5) (delVerts G {2}) ![3, 0, 6, 8, 10] ![4, 5, 7, 9, 1]
      (by decide) (by decide) T hT
  have hb := PEqualNP.MetaComplexity.L532 11 5 s' (delVerts G {2}) ∅ peelable_del2
    (by simp) (Or.inr ⟨3, 4, by decide⟩) hk h
  rw [Finset.card_empty, hE] at hb
  omega

theorem lb_del23 (s' : ℕ) (h : HasCircuitSize 11 (F (delVerts G {2, 3}) ∅) s') : 12 ≤ s' := by
  have hE : (delVerts G {2, 3}).edgeSet.ncard = 9 := by
    have h1 := edgeSet_ncard_eq_of_finset (delVerts G {2, 3})
      {s(4, 1), s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
      (by decide)
    rw [h1]; decide
  have hk : ∀ T : Finset (Fin 11), (∀ i j, (delVerts G {2, 3}).Adj i j → i ∈ T ∨ j ∈ T) →
      4 ≤ T.card := by
    intro T hT
    exact cov_ge_of_matching (k := 4) (delVerts G {2, 3}) ![4, 0, 6, 8] ![1, 5, 7, 9]
      (by decide) (by decide) T hT
  have hb := PEqualNP.MetaComplexity.L532 11 4 s' (delVerts G {2, 3}) ∅ peelable_del23
    (by simp) (Or.inr ⟨4, 1, by decide⟩) hk h
  rw [Finset.card_empty, hE] at hb
  omega

theorem lb_del3_false (s' : ℕ)
    (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x 3 false)) s') : 13 ≤ s' := by
  have hr : (fun x => F G ∅ (Function.update x 3 false)) = F (delVerts G {3}) ∅ := by
    funext x
    rw [Res.ToolRes0_proof 11 G ∅ 3 x (by simp), delV_eq]
  rw [hr] at h
  have hdep2 : ∃ x : Fin 11 → Bool,
      F (delVerts G {3}) ∅ (Function.update x 2 (!x 2)) ≠ F (delVerts G {3}) ∅ x :=
    F_dep (delVerts G {3}) ∅ 2 0 (by decide) (by simp)
  have hdep0 : ∃ x : Fin 11 → Bool,
      F (delVerts G {3}) ∅ (Function.update x 0 (!x 0)) ≠ F (delVerts G {3}) ∅ x :=
    F_dep (delVerts G {3}) ∅ 0 2 (by decide) (by simp)
  have hspos : 1 ≤ s' := by
    have hd := dep_lower_set 11 (F (delVerts G {3}) ∅) {2, 0} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hdep2
      · exact hdep0) s' h
    have hc : ({2, 0} : Finset (Fin 11)).card = 2 := by decide
    omega
  obtain ⟨s0, rfl⟩ : ∃ s0, s' = s0 + 1 := ⟨s' - 1, by omega⟩
  have hres2 : (fun x => F (delVerts G {3}) ∅ (Function.update x 2 false)) =
      F (delVerts G {2, 3}) ∅ := by
    funext x
    rw [Res.ToolRes0_proof 11 (delVerts G {3}) ∅ 2 x (by simp), delV_eq, delVerts_delVerts]
    have hu : ({3} : Finset (Fin 11)) ∪ {2} = {2, 3} := by decide
    rw [hu]
  have hnc2 : ∃ x y : Fin 11 → Bool,
      F (delVerts G {3}) ∅ (Function.update x 2 false) ≠
      F (delVerts G {3}) ∅ (Function.update y 2 false) := by
    obtain ⟨x, y, hxy⟩ := F_nc (delVerts G {2, 3}) ∅ (Or.inr ⟨4, 1, by decide⟩)
    exact ⟨x, y, by rw [congrFun hres2 x, congrFun hres2 y]; exact hxy⟩
  have h' := one_gate_at 10 (F (delVerts G {3}) ∅) 2 false s0 hdep2 hnc2 h
  rw [hres2] at h'
  have := lb_del23 s0 h'
  omega

theorem lb_del3_true (s' : ℕ)
    (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x 3 true)) s') : 13 ≤ s' := by
  have hr : (fun x => F G ∅ (Function.update x 3 true)) = F (delVerts G {2, 3, 4}) {2, 4} := by
    funext x
    rw [Res.ToolRes1_proof 11 G ∅ 3 {2, 4} x (by simp) (by decide), delV_eq]
    have h1 : (insert (3 : Fin 11) {2, 4} : Finset (Fin 11)) = {2, 3, 4} := by decide
    have h2 : (∅ : Finset (Fin 11)) ∪ {2, 4} = {2, 4} := by decide
    rw [h1, h2]
  rw [hr] at h
  have hE : (delVerts G {2, 3, 4}).edgeSet.ncard = 8 := by
    have h1 := edgeSet_ncard_eq_of_finset (delVerts G {2, 3, 4})
      {s(0, 5), s(5, 6), s(6, 7), s(7, 1), s(0, 8), s(8, 9), s(9, 10), s(10, 1)}
      (by decide)
    rw [h1]; decide
  have hk : ∀ T : Finset (Fin 11), (∀ i j, (delVerts G {2, 3, 4}).Adj i j → i ∈ T ∨ j ∈ T) →
      4 ≤ T.card := by
    intro T hT
    exact cov_ge_of_matching (k := 4) (delVerts G {2, 3, 4}) ![0, 6, 1, 9] ![5, 7, 10, 8]
      (by decide) (by decide) T hT
  have hb := PEqualNP.MetaComplexity.L532 11 4 s' (delVerts G {2, 3, 4}) {2, 4} peelable_del234
    (by decide) (Or.inl ⟨2, by decide⟩) hk h
  have hA : ({2, 4} : Finset (Fin 11)).card = 2 := by decide
  rw [hA, hE] at hb
  omega

theorem lb_outer_false (v : Fin 11) (hv : v = 2 ∨ v = 4 ∨ v = 5 ∨ v = 7 ∨ v = 8 ∨ v = 10)
    (s' : ℕ) (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x v false)) s') :
    14 ≤ s' := by
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_del2 s' h
  · exact lb_del2 s' (restrict_aut swapHubs swapHubs swapHubs_inv swapHubs_inv G_adj_swap 2 false s' h)
  · exact lb_del2 s' (restrict_aut rotPaths rotPathsInv rotPaths_inv1 rotPaths_inv2 G_adj_rot 2 false s' h)
  · have h1 := restrict_aut swapHubs swapHubs swapHubs_inv swapHubs_inv G_adj_swap 5 false s' h
    exact lb_del2 s' (restrict_aut rotPaths rotPathsInv rotPaths_inv1 rotPaths_inv2 G_adj_rot 2 false s' h1)
  · exact lb_del2 s' (restrict_aut rotPathsInv rotPaths rotPaths_inv2 rotPaths_inv1 G_adj_rotInv 2 false s' h)
  · have h1 := restrict_aut swapHubs swapHubs swapHubs_inv swapHubs_inv G_adj_swap 8 false s' h
    exact lb_del2 s' (restrict_aut rotPathsInv rotPaths rotPaths_inv2 rotPaths_inv1 G_adj_rotInv 2 false s' h1)

theorem lb_mid_false (m : Fin 11) (hm : m = 3 ∨ m = 6 ∨ m = 9) (s' : ℕ)
    (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x m false)) s') : 13 ≤ s' := by
  rcases hm with rfl | rfl | rfl
  · exact lb_del3_false s' h
  · exact lb_del3_false s' (restrict_aut rotPaths rotPathsInv rotPaths_inv1 rotPaths_inv2 G_adj_rot 3 false s' h)
  · exact lb_del3_false s' (restrict_aut rotPathsInv rotPaths rotPaths_inv2 rotPaths_inv1 G_adj_rotInv 3 false s' h)

theorem lb_mid_true (m : Fin 11) (hm : m = 3 ∨ m = 6 ∨ m = 9) (s' : ℕ)
    (h : HasCircuitSize 11 (fun x => F G ∅ (Function.update x m true)) s') : 13 ≤ s' := by
  rcases hm with rfl | rfl | rfl
  · exact lb_del3_true s' h
  · exact lb_del3_true s' (restrict_aut rotPaths rotPathsInv rotPaths_inv1 rotPaths_inv2 G_adj_rot 3 true s' h)
  · exact lb_del3_true s' (restrict_aut rotPathsInv rotPaths rotPaths_inv2 rotPaths_inv1 G_adj_rotInv 3 true s' h)

def D : Finset (Fin 11) := {2, 3, 4, 5, 6, 7, 8, 9, 10}

theorem afree_G : AFree G ∅ := by intro i j _ hi; simp at hi

theorem hnc_all (y : Fin 11) (b : Bool) :
    ∃ x x' : Fin 11 → Bool,
      F G ∅ (Function.update x y b) ≠ F G ∅ (Function.update x' y b) := by
  have hex : ∀ y : Fin 11, ∃ i j c : Fin 11, G.Adj i j ∧ i ≠ y ∧ j ≠ y ∧ G.Adj y c := by decide
  obtain ⟨i, j, c, hij, hi, hj, hyc⟩ := hex y
  exact nc_of afree_G hij hi hj hyc b

theorem hdep_all (y : Fin 11) : Dep (F G ∅) y := by
  have hex : ∀ y : Fin 11, ∃ c : Fin 11, G.Adj y c := by decide
  obtain ⟨c, hyc⟩ := hex y
  exact F_dep G ∅ y c hyc (by simp)

theorem hnf_D (y : Fin 11) (hy : y ∈ D) (y' : Fin 11) (hy' : y' ∈ D) (hne : y ≠ y') :
    ¬ PairFunnel (F G ∅) y y' := by
  have hex : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' →
      ∃ c c' : Fin 11, G.Adj y c ∧ c ≠ y' ∧ ¬ G.Adj c y' ∧ G.Adj y' c' ∧ c' ≠ y := by decide
  obtain ⟨c, c', hyc, hcy', hncy', hyc', hc'y⟩ := hex y hy y' hy' hne
  have hcy : c ≠ y := hyc.ne.symm
  have hc'y' : c' ≠ y' := hyc'.ne.symm
  have f1 : ∀ d : Fin 11, ∀ z : Fin 11 → Bool, (∀ i, z i = true → i = d) → F G ∅ z = false :=
    fun d z hz => F_false_of {d} (fun i hi => by rw [Finset.mem_singleton]; exact hz i hi)
      (by simp) (fun i j h hi hj => by
        rw [Finset.mem_singleton] at hi hj; exact h.ne (hi.trans hj.symm))
  have T1 : F G ∅ (set2 (pt {c}) y true y' false) = true :=
    F_true_of y c hyc (by simp [set2, hne]) (by simp [set2, pt, hcy, hcy'])
  have T2 : F G ∅ (set2 (pt {c'}) y false y' true) = true :=
    F_true_of y' c' hyc' (by simp [set2]) (by simp [set2, pt, hc'y, hc'y'])
  have Z1 : F G ∅ (set2 (pt {c}) y false y' false) = false := f1 c _ (fun i hi => by
    simp only [set2, Function.update_apply, pt] at hi; split_ifs at hi; simp_all)
  have Z2 : F G ∅ (set2 (pt {c'}) y false y' false) = false := f1 c' _ (fun i hi => by
    simp only [set2, Function.update_apply, pt] at hi; split_ifs at hi; simp_all)
  have Z3 : F G ∅ (set2 (pt {c}) y false y' true) = false := by
    refine F_false_of {c, y'} (fun i hi => ?_) (by simp) (fun i j h hi hj => ?_)
    · simp only [set2, Function.update_apply, pt] at hi; split_ifs at hi <;> simp_all
    · rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact h.ne rfl
      · exact hncy' h
      · exact hncy' h.symm
      · exact h.ne rfl
  rintro ⟨a, b, hab⟩
  cases a <;> cases b
  · have h := (hab (pt {c})).1; simp only [Bool.not_false] at h; rw [T1, Z3] at h; cases h
  · have h := (hab (pt {c})).2; simp only [Bool.not_false, Bool.not_true] at h; rw [Z1, T1] at h; cases h
  · have h := (hab (pt {c'})).1.trans (hab (pt {c'})).2; simp only [Bool.not_false, Bool.not_true] at h; rw [T2, Z2] at h; cases h
  · have h := (hab (pt {c})).2; simp only [Bool.not_true] at h; rw [T1, Z1] at h; cases h

theorem nlit_G (y : Fin 11) (c : Bool) : ¬ ∀ u : Fin 11 → Bool, F G ∅ u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := hnc_all y false
  apply hx
  rw [h, h]
  simp

theorem exists_front_D {gs : List Gate} {o : ℕ} (L : Least 11 (F G ∅) gs o)
    (OR : OneReader D gs) :
    ∃ (p : ℕ) (g : Gate) (y : Fin 11) (l h : ℕ), Front D gs p g y l h ∧ o ≠ 11 + p := by
  classical
  have hfnc : ∃ x x' : Fin 11 → Bool, F G ∅ x ≠ F G ∅ x' := by
    obtain ⟨x, x', h⟩ := hnc_all 3 false
    exact ⟨_, _, h⟩
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps 11)).getD (11 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex with hpdef
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps 11)).getD (11 + r) ∅ :=
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
    have hout : ∀ (l : ℕ) (hl : l ∈ g.inputs) (y : Fin 11) (c : Bool),
        (∀ u, vl gs u l = xor (u y) c) → o ≠ 11 + p := by
      intro l hl y c hv e
      obtain ⟨x, x', hx⟩ := hnc_all y (xor (fixBit g) c)
      have hc : ∀ z : Fin 11 → Bool, F G ∅ (Function.update z y (xor (fixBit g) c)) = fixBit g := by
        intro z
        rw [← L.hev, e]
        refine vl_abs gs L.hcl _ p g hg hop l hl ?_
        rw [hv]; simp
      exact hx (by rw [hc, hc])
    by_cases mj : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps 11)).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps 11)).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
      have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩
      have hopnd : ∀ (w : ℕ) (v : Fin 11), v ∈ D → Reads gs p w →
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
          vl gs u (11 + p) = vl gs u' (11 + p) → F G ∅ u = F G ∅ u' := by
        intro u u' hagr hgv
        rw [← L.hev, ← L.hev]
        refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k)
          (o + 1) ?_ ?_ o (by omega) ?_
        · intro a ha hBa
          rw [vl_input gs u a ha, vl_input gs u' a ha]
          exact hagr _ (fun e => hBa (Or.inl (congrArg Fin.val e)))
            (fun e => hBa (Or.inr (Or.inl (congrArg Fin.val e))))
        · intro p' g' hp' _ hB' hr _
          obtain ⟨a, ha, hBa⟩ := hr
          have hR : Reads gs p' a := ⟨g', hp', ha⟩
          have hpt : p' = p := by
            rcases hBa with e | e | e | e
            · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR (fun e' => hB' (Or.inr (Or.inr (Or.inl e'))))
            · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR (fun e' => hB' (Or.inr (Or.inr (Or.inr e'))))
            · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR (fun e' => hB' (Or.inr (Or.inr (Or.inl e'))))
            · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR (fun e' => hB' (Or.inr (Or.inr (Or.inr e'))))
          rw [hpt]; exact hgv
        · rintro (e | e | e | e)
          · exact nlit_G yj false (fun x => by rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
          · exact nlit_G yk false (fun x => by rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
          · exact nlit_G yj cj (fun x => by rw [← L.hev, e, hvj])
          · exact nlit_G yk ck (fun x => by rw [← L.hev, e, hvk])
      have hag : ∀ (x : Fin 11 → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
          set2 x yj a yk b i = set2 x yj a' yk b' i := fun x a b a' b' i e1 e2 => by
        rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
      have hval : ∀ (x : Fin 11 → Bool) (a b : Bool),
          vl gs (set2 x yj a yk b) (11 + p) = g.op.eval [xor a cj, xor b ck] := by
        intro x a b
        rw [vl_gate gs L.hcl _ p g hg, hin]
        simp only [List.map_cons, List.map_nil]
        rw [hvj, hvk, set2_p x hvjk, set2_q x]
      apply hnf_D yj hyj yk hyk hvjk
      rcases hop with hop | hop
      · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
          rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
      · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
          rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      exact ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩, hout j (by rw [hin]; simp) y c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      exact ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩, hout k (by rw [hin]; simp) y c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps 11)).getD (11 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    have hdep3 : (3 : Fin 11) ∈ (suppsFrom gs (inputSupps 11)).getD o ∅ := by
      obtain ⟨x, hx⟩ := hdep_all 3
      by_contra hno
      apply hx
      rw [← L.hev, ← L.hev]
      exact (agree_wiresFrom (Function.update x 3 (!x 3)) x gs _ _ _
        (agree_inputs _ _)).2.2 o (fun k hk => by
          have : k ≠ 3 := fun e => hno (e ▸ hk)
          simp [Function.update_of_ne this])
    by_cases hol : o < 11 + gs.length
    · obtain ⟨y, _, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol ⟨3, by decide, hdep3⟩
      exact nlit_G y c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]

theorem front_win_at {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin 11} {l h : ℕ}
    (L : Least 11 (F G ∅) gs o) (hO : OneReader D gs) (hF : Front D gs p g y l h)
    (x x' : Fin 11 → Bool) (hagr0 : ∀ i : Fin 11, i ∉ D → x' i = x i)
    (hF0 : F G ∅ x' = false) (hF1 : F G ∅ (Function.update x' y true) = true) :
    vl gs x h ≠ fixBit g := by
  intro hx
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  have hagr1 : ∀ i, i ∉ D → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hagr0 i hi]
  have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hagr0 i hi).symm
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (11 + p) = fixBit g :=
    vl_abs gs L.hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr']; exact hx)
  have hc2 : vl gs (Function.update x' y true) (11 + p) = fixBit g :=
    vl_abs gs L.hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr1]; exact hx)
  have hol : o ≠ l := out_ne_lit L.hcl L.hev y (hnc_all y) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit L.hcl L.hev y (hnc_all y) y (Or.inl rfl)
  have key := agree_B gs L.hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (fun j hj hB => by
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin 11) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (fun q g' hq _ hBq hBa _ => by
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by rcases hBa with e | e; exact e; rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            exact hBq (Or.inr (by rw [el, hq']))
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads) ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [L.hev, L.hev, hF0, hF1] at key
  cases key

theorem front_h_char {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin 11} {l h : ℕ}
    (L : Least 11 (F G ∅) gs o) (hO : OneReader D gs) (hF : Front D gs p g y l h) :
    (y = 3 ∨ y = 6 ∨ y = 9) ∧ 11 ≤ h ∧
      ∀ x : Fin 11 → Bool, vl gs x h = !fixBit g ↔ (x 0 = false ∨ x 1 = false) := by
  have hfnc : ∃ x x' : Fin 11 → Bool, F G ∅ x ≠ F G ∅ x' := by
    obtain ⟨x, x', hx⟩ := hnc_all 3 false; exact ⟨_, _, hx⟩
  have hhlt : h < 11 + p := by
    obtain ⟨hp, _, hin, _, _, _⟩ := hF
    exact (L.hcl p g hp).lt h (by rcases hin with e | e <;> simp [e])
  have hp_len : p < gs.length := (List.getElem?_eq_some_iff.1 hF.1).1
  have hnotconst : ∀ c : Bool, ¬ ∀ x : Fin 11 → Bool, vl gs x h = c := by
    intro c hall
    by_cases h11 : h < 11
    · have h1 := hall (fun _ => !c)
      rw [vl_input gs _ h h11] at h1
      cases c <;> cases h1
    · obtain ⟨ph, rfl⟩ : ∃ ph, h = 11 + ph := ⟨h - 11, by omega⟩
      exact L.no_const hfnc ph (by omega) c hall
  have mkWit : ∀ (b0 b1 : Bool) (c : Fin 11), c ∈ D → c ≠ y → G.Adj c y →
      (b0 = true → ¬ G.Adj 0 c) → (b1 = true → ¬ G.Adj 1 c) →
      ∀ x : Fin 11 → Bool, x 0 = b0 → x 1 = b1 → vl gs x h = !fixBit g := by
    intro b0 b1 c hcD hcy hcyA h0c h1c x hx0 hx1
    let x' : Fin 11 → Bool := fun i =>
      if i = 0 then b0 else if i = 1 then b1 else if i = c then true else false
    have hagr : ∀ i : Fin 11, i ∉ D → x' i = x i := by
      intro i hi
      have h01 : i = 0 ∨ i = 1 := (by decide : ∀ j : Fin 11, j ∉ D → j = 0 ∨ j = 1) i hi
      rcases h01 with rfl | rfl
      · simp [x', hx0]
      · simp [x', hx1]
    have hF0 : F G ∅ x' = false := by
      rw [Bool.eq_false_iff, ne_eq, F_true]
      rintro (⟨a, ha, _⟩ | ⟨i, j, hij, hi, hj⟩)
      · simp at ha
      · have hmem : ∀ w, x' w = true → (w = 0 ∧ b0 = true) ∨ (w = 1 ∧ b1 = true) ∨ w = c := by
          intro w hw
          simp only [x'] at hw
          split_ifs at hw with h0 h1 hc
          · exact Or.inl ⟨h0, hw⟩
          · exact Or.inr (Or.inl ⟨h1, hw⟩)
          · exact Or.inr (Or.inr hc)
        have h01 : ¬ G.Adj 0 1 := by decide
        have hc0 : c ≠ 0 := fun e => by subst e; exact (by decide : (0 : Fin 11) ∉ D) hcD
        have hc1 : c ≠ 1 := fun e => by subst e; exact (by decide : (1 : Fin 11) ∉ D) hcD
        rcases hmem i hi with ⟨rfl, hb0⟩ | ⟨rfl, hb1⟩ | rfl <;>
          rcases hmem j hj with ⟨rfl, hb0'⟩ | ⟨rfl, hb1'⟩ | rfl
        · exact hij.ne rfl
        · exact h01 hij
        · exact h0c hb0 hij
        · exact h01 hij.symm
        · exact hij.ne rfl
        · exact h1c hb1 hij
        · exact h0c hb0' hij.symm
        · exact h1c hb1' hij.symm
        · exact hij.ne rfl
    have hF1 : F G ∅ (Function.update x' y true) = true :=
      F_true_of c y hcyA (by rw [Function.update_of_ne hcy]; simp [x', show c ≠ 0 from fun e => by subst e; exact (by decide : (0 : Fin 11) ∉ D) hcD, show c ≠ 1 from fun e => by subst e; exact (by decide : (1 : Fin 11) ∉ D) hcD]) (by simp)
    have hne := front_win_at L hO hF x x' hagr hF0 hF1
    cases hv : vl gs x h <;> cases hf : fixBit g <;> rw [hv, hf] at hne <;> first | rfl | exact absurd rfl hne
  have hyD : y ∈ D := hF.2.2.2.1
  have hmid : y = 3 ∨ y = 6 ∨ y = 9 := by
    by_contra hnot
    have hex : ∀ y ∈ D, ¬ (y = 3 ∨ y = 6 ∨ y = 9) →
        ∃ c : Fin 11, c ∈ D ∧ c ≠ y ∧ G.Adj c y ∧ ¬ G.Adj 0 c ∧ ¬ G.Adj 1 c := by decide
    obtain ⟨c, hcD, hcy, hcyA, h0c, h1c⟩ := hex y hyD hnot
    exact hnotconst (!fixBit g) (fun x => mkWit (x 0) (x 1) c hcD hcy hcyA
      (fun _ => h0c) (fun _ => h1c) x rfl rfl)
  have h0f : ∀ x : Fin 11 → Bool, (x 0 = false ∨ x 1 = false) → vl gs x h = !fixBit g := by
    intro x h01
    rcases h01 with hx0 | hx1
    · have hex : ∀ m : Fin 11, m = 3 ∨ m = 6 ∨ m = 9 →
          ∃ c : Fin 11, c ∈ D ∧ c ≠ m ∧ G.Adj c m ∧ ¬ G.Adj 1 c := by decide
      obtain ⟨c, hcD, hcy, hcyA, h1c⟩ := hex y hmid
      exact mkWit false (x 1) c hcD hcy hcyA (by intro h; cases h) (fun _ => h1c) x hx0 rfl
    · have hex : ∀ m : Fin 11, m = 3 ∨ m = 6 ∨ m = 9 →
          ∃ c : Fin 11, c ∈ D ∧ c ≠ m ∧ G.Adj c m ∧ ¬ G.Adj 0 c := by decide
      obtain ⟨c, hcD, hcy, hcyA, h0c⟩ := hex y hmid
      exact mkWit (x 0) false c hcD hcy hcyA (fun _ => h0c) (by intro h; cases h) x rfl hx1
  have h11t : ∀ x : Fin 11 → Bool, x 0 = true → x 1 = true → vl gs x h = fixBit g := by
    intro x hx0 hx1
    by_contra hne
    have hv : vl gs x h = !fixBit g := by
      cases e : vl gs x h <;> cases f : fixBit g <;> rw [e, f] at hne <;> first | rfl | exact absurd rfl hne
    apply hnotconst (!fixBit g)
    intro z
    by_cases hz : z 0 = false ∨ z 1 = false
    · exact h0f z hz
    · push Not at hz
      have hz0 : z 0 = true := by cases e : z 0; exact absurd e hz.1; rfl
      have hz1 : z 1 = true := by cases e : z 1; exact absurd e hz.2; rfl
      rw [← hv]
      exact vl_dfree hF.2.2.2.2.2 z x (fun i hi => by
        have h01 : i = 0 ∨ i = 1 := (by decide : ∀ j : Fin 11, j ∉ D → j = 0 ∨ j = 1) i hi
        rcases h01 with rfl | rfl
        · rw [hz0, hx0]
        · rw [hz1, hx1])
  have hge11 : 11 ≤ h := by
    by_contra hlt
    have h11 : h < 11 := by omega
    have h00 := h0f (fun _ => false) (Or.inl rfl)
    have h10 := h0f (pt {0}) (Or.inr (by decide))
    have h01 := h0f (pt {1}) (Or.inl (by decide))
    rw [vl_input gs _ h h11] at h00 h10 h01
    have h01' : (⟨h, h11⟩ : Fin 11) = 0 ∨ (⟨h, h11⟩ : Fin 11) = 1 := by
      by_contra hno
      have hmem : (⟨h, h11⟩ : Fin 11) ∈ D := by
        have : ∀ v : Fin 11, ¬ (v = 0 ∨ v = 1) → v ∈ D := by decide
        exact this _ hno
      exact hF.2.2.2.2.2 ⟨h, h11⟩ hmem (by rw [front_supp_input gs h h11]; simp)
    rcases h01' with e | e
    · rw [e] at h10; simp [pt] at h10; rw [h10] at h00; cases h00
    · rw [e] at h01; simp [pt] at h01; rw [h01] at h00; cases h00
  refine ⟨hmid, hge11, fun x => ⟨fun hv => ?_, h0f x⟩⟩
  by_contra hnot
  push Not at hnot
  have hx0 : x 0 = true := by cases e : x 0; exact absurd e hnot.1; rfl
  have hx1 : x 1 = true := by cases e : x 1; exact absurd e hnot.2; rfl
  have ht := h11t x hx0 hx1
  rw [ht] at hv
  cases e : fixBit g <;> simp [e] at hv

theorem orSwap_agree (gs : List Gate) (hcl : CleanL 11 gs) (p ph l : ℕ) (g : Gate)
    (y : Fin 11) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, 11 + ph] ∨ g.inputs = [11 + ph, l]) (hlne : l ≠ 11 + ph)
    (hone : ∀ t, Reads gs t (11 + ph) → t = p) (x : Fin 11 → Bool) (hlx : vl gs x l = true) :
    ∀ w, w ≠ 11 + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
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
          exact ih a ((hcl r g' hr).lt a ha) (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

theorem or_only_reader_pay {gs : List Gate} {o p ph l : ℕ} {g : Gate} {y : Fin 11}
    (L : Least 11 (F G ∅) gs o) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, 11 + ph] ∨ g.inputs = [11 + ph, l]) (hlit : IsLit 11 gs y l)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (11 + ph) → t = p)
    (ho1 : o ≠ 11 + p) (ho2 : o ≠ 11 + ph) :
    Drop (F G ∅) y true 3 gs.length ∨ Drop (F G ∅) y false 4 gs.length := by
  have hfnc : ∃ x x' : Fin 11 → Bool, F G ∅ x ≠ F G ∅ x' := by
    obtain ⟨x, x', h⟩ := hnc_all y false; exact ⟨_, _, h⟩
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
  have core : ∀ (b : Bool) (hlx : ∀ x : Fin 11 → Bool, x y = b → vl gs x l = true)
      (T : Finset ℕ), (∀ q ∈ T, RC 10 (andSwap gs ph y) y b q) →
      Drop (F G ∅) y b T.card gs.length := by
    intro b hlx T hT
    have hag : ∀ x : Fin 11 → Bool,
        vl (andSwap gs ph y) (Function.update x y b) o = F G ∅ (Function.update x y b) := fun x => by
      rw [orSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _ (hlx _ (by simp)) o ho2, L.hev]
    have hnc' : ∃ x x' : Fin 11 → Bool,
        vl (andSwap gs ph y) (Function.update x y b) o ≠
        vl (andSwap gs ph y) (Function.update x' y b) o := by
      obtain ⟨x, x', h⟩ := hnc_all y b
      exact ⟨x, x', by rw [hag, hag]; exact h⟩
    obtain ⟨s', hs', hc⟩ := save 10 (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o
      hcl' (fun _ => rfl) y b hnc' T hT
    refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
    have e : (fun x : Fin 11 → Bool => F G ∅ (Function.update x y b)) =
        fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := funext fun x => (hag x).symm
    rw [e]; exact hc
  rcases hlit with rfl | ⟨pn, rfl, hpn⟩
  · left
    have hcp : IsC 10 (andSwap gs ph y) y true (11 + p) :=
      isC_reader hcl' y p g hgp' hlmem true (Or.inr (by simp [fixBit, hop]))
    have h3 := core true (fun x hx => by rw [vl_input gs x y y.isLt]; exact hx) {ph, p, S} (by
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
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) false (Or.inl rfl)
    have hc1 : c = true := by
      have h1 := st_val_const 10 _ hcl' y false _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1; exact h1
    subst hc1
    have hcp : IsC 10 (andSwap gs ph y) y false (11 + p) :=
      const_read 10 _ hcl' y false p g hgp' (11 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := core false (fun x hx => by
        rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]; simp [hx])
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

theorem shared_h_pay {gs : List Gate} {o p ph l r : ℕ} {g : Gate} {y : Fin 11}
    (L : Least 11 (F G ∅) gs o) (hF : Front D gs p g y l (11 + ph))
    (hchar : ∀ x : Fin 11 → Bool, vl gs x (11 + ph) = !fixBit g ↔ (x 0 = false ∨ x 1 = false))
    (hrp : r ≠ p) (hrr : Reads gs r (11 + ph)) :
    Drop (F G ∅) 0 false 4 gs.length := by
  have hfnc : ∃ x x' : Fin 11 → Bool, F G ∅ x ≠ F G ∅ x' := by
    obtain ⟨x, x', h⟩ := hnc_all 0 false; exact ⟨_, _, h⟩
  obtain ⟨hgp, hop, hin, hyD, hlit, _⟩ := hF
  have hhmem : 11 + ph ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hphp : ph < p := by have := (L.hcl p g hgp).lt _ hhmem; omega
  have hphr : ph < r := by have := reads_lt L.hcl hrr; omega
  have hp_len : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hph_len : ph < gs.length := by omega
  let g0 : Gate := match g.op with
    | GateOp.or => ⟨GateOp.and, [0, 0]⟩
    | _ => ⟨GateOp.not, [0]⟩
  let gs' : List Gate := gs.set ph g0
  have hlen' : gs'.length = gs.length := by simp [gs']
  have hget_eq : gs'[ph]? = some g0 := by simp [gs', hph_len]
  have hget_ne : ∀ k, k ≠ ph → gs'[k]? = gs[k]? := fun k hk => by simp [gs', Ne.symm hk]
  have hcl' : CleanL 11 gs' := by
    intro k gk hgk
    by_cases hk : k = ph
    · subst hk
      rw [hget_eq] at hgk; cases hgk
      rcases hop with hop1 | hop1
      · simp only [g0, hop1]
        exact Or.inl ⟨rfl, 0, by omega, rfl⟩
      · simp only [g0, hop1]
        exact Or.inr ⟨Or.inl rfl, 0, 0, by omega, by omega, rfl⟩
    · rw [hget_ne k hk] at hgk; exact L.hcl k gk hgk
  have hagree : ∀ x : Fin 11 → Bool, x 0 = false → ∀ w : ℕ, vl gs' x w = vl gs x w := by
    intro x hx0 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hw11 : w < 11
      · rw [vl_input gs' x w hw11, vl_input gs x w hw11]
      · obtain ⟨k, rfl⟩ : ∃ k, w = 11 + k := ⟨w - 11, by omega⟩
        by_cases hk : k = ph
        · subst hk
          have hv := (hchar x).2 (Or.inl hx0)
          rw [hv, vl_gate gs' hcl' x k g0 hget_eq]
          rcases hop with hop1 | hop1 <;>
            simp [g0, hop1, fixBit, GateOp.eval, vl_input gs' x 0 (by omega), hx0]
        · cases hg' : gs[k]? with
          | none =>
            have hkl : gs.length ≤ k := List.getElem?_eq_none_iff.1 hg'
            rw [vl_beyond gs' x _ (by omega), vl_beyond gs x _ (by omega)]
          | some gk =>
            have hgk' : gs'[k]? = some gk := by rw [hget_ne k hk]; exact hg'
            rw [vl_gate gs' hcl' x k gk hgk', vl_gate gs L.hcl x k gk hg']
            congr 1
            exact List.map_congr_left fun a ha => ih a ((L.hcl k gk hg').lt a ha)
  have hph_rc : RC 10 gs' 0 false ph := by
    refine rc_input false ⟨g0, hget_eq, ?_⟩
    rcases hop with hop1 | hop1 <;> simp [g0, hop1]
  have hph_isc : IsC 10 gs' 0 false (11 + ph) := by
    rcases hop with hop1 | hop1
    · exact isC_reader hcl' 0 ph g0 hget_eq (by simp [g0, hop1]) false
        (Or.inl (by simp [g0, hop1]))
    · exact isC_reader hcl' 0 ph g0 hget_eq (by simp [g0, hop1]) false
        (Or.inr (by simp [g0, hop1, fixBit]))
  have hp_reads' : Reads gs' p (11 + ph) := ⟨g, by rw [hget_ne p (by omega)]; exact hgp, hhmem⟩
  have hr_reads' : Reads gs' r (11 + ph) := by
    obtain ⟨gr, hgr, hmr⟩ := hrr
    exact ⟨gr, by rw [hget_ne r (by omega)]; exact hgr, hmr⟩
  have hsave : ∀ T : Finset ℕ, (∀ k ∈ T, RC 10 gs' 0 false k) →
      Drop (F G ∅) 0 false T.card gs.length := by
    intro T hT
    have hag : ∀ x : Fin 11 → Bool,
        vl gs' (Function.update x 0 false) o = F G ∅ (Function.update x 0 false) := fun x => by
      rw [hagree _ (by simp) o, L.hev]
    have hnc' : ∃ x x' : Fin 11 → Bool,
        vl gs' (Function.update x 0 false) o ≠ vl gs' (Function.update x' 0 false) o := by
      obtain ⟨x, x', h⟩ := hnc_all 0 false
      exact ⟨x, x', by rw [hag, hag]; exact h⟩
    obtain ⟨s', hs', hc⟩ := save 10 (fun x => vl gs' x o) gs' o hcl' (fun _ => rfl) 0 false
      hnc' T hT
    refine ⟨s', by rw [hlen'] at hs'; exact hs', ?_⟩
    have e : (fun x : Fin 11 → Bool => F G ∅ (Function.update x 0 false)) =
        fun x => (fun x => vl gs' x o) (Function.update x 0 false) := funext fun x => (hag x).symm
    rw [e]; exact hc
  -- input 0 cannot be read only by ph
  have hexq : ∃ q, q ≠ ph ∧ Reads gs q 0 := by
    by_contra hno
    push Not at hno
    have ho0 : o ≠ 0 := by
      intro e
      have h1 := L.hev (pt {0})
      rw [e, vl_input gs _ 0 (by omega)] at h1
      have h2 : F G ∅ (pt {0}) = false :=
        F_false_of {0} (fun i hi => by simp [pt] at hi; simp [hi]) (by simp)
          (fun i j h hi hj => by simp at hi hj; subst hi; subst hj; exact h.ne rfl)
      simp [pt] at h1; rw [h2] at h1; cases h1
    have hEq := agree_B gs L.hcl (pt {2}) (pt {0, 2}) (fun a => a = 0) (o + 1)
      (fun a ha hBa => by
        rw [vl_input gs _ a ha, vl_input gs _ a ha]
        have ha0 : (⟨a, ha⟩ : Fin 11) ≠ 0 := fun e => hBa (congrArg Fin.val e)
        simp [pt, ha0])
      (fun k gk hk _ _ hBa _ => by
        obtain ⟨a, ha, rfl⟩ := hBa
        have hkph : k = ph := by
          by_contra hne
          exact hno k hne ⟨gk, hk, ha⟩
        subst hkph
        rw [(hchar (pt {2})).2 (Or.inr (by decide)), (hchar (pt {0, 2})).2 (Or.inr (by decide))])
      o (by omega) ho0
    rw [L.hev, L.hev] at hEq
    have hf : F G ∅ (pt {2}) = false :=
      F_false_of {2} (fun i hi => by simp [pt] at hi; simp [hi]) (by simp)
        (fun i j h hi hj => by simp at hi hj; subst hi; subst hj; exact h.ne rfl)
    have ht : F G ∅ (pt {0, 2}) = true := F_true_of 0 2 (by decide) (by decide) (by decide)
    rw [hf, ht] at hEq; cases hEq
  obtain ⟨q, hqph, hqr0⟩ := hexq
  have hqp : q ≠ p := by
    rintro rfl
    obtain ⟨g', hg', hm0⟩ := hqr0
    have := gate_eq hgp hg' rfl; subst this
    have : (0 : ℕ) = l ∨ (0 : ℕ) = 11 + ph := by
      rcases hin with e | e <;> rw [e] at hm0 <;> simp at hm0 <;> omega
    rcases this with e | e
    · rcases hlit with el | ⟨pn, el, _⟩
      · have hy0 : y ≠ 0 := fun e' => (by decide : (0 : Fin 11) ∉ D) (e' ▸ hyD)
        exact hy0 (Fin.ext (by omega))
      · omega
    · omega
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨gr, hgr, hmr0⟩ := hqr0
    obtain ⟨gr', hgr', hmrph⟩ := hrr
    have := gate_eq hgr hgr' rfl; subst this
    have hgr' : gs'[q]? = some gr := by rw [hget_ne q hqph]; exact hgr
    have hq_isc : IsC 10 gs' 0 false (11 + q) := by
      refine st_allconst 10 gs' hcl' 0 false q gr hgr' (fun a ha => ?_)
      rcases two_inputs (hcl' q gr hgr') 0 (11 + ph) a hmr0 hmrph (by omega) ha with rfl | rfl
      · exact ⟨false, stF_self 10 gs' 0 false⟩
      · exact hph_isc
    have hoq : o ≠ 11 + q := by
      intro e
      obtain ⟨c, hc⟩ := hq_isc
      obtain ⟨x, x', hxx⟩ := hnc_all 0 false
      apply hxx
      have h1 : ∀ z, F G ∅ (Function.update z 0 false) = c := fun z => by
        rw [← L.hev, ← hagree _ (by simp) o, e, upd_ins]
        exact st_val_const 10 gs' hcl' 0 false (11 + q) c hc _
      rw [h1 x, h1 x']
    obtain ⟨S, hqS, hSr⟩ := L.live hfnc q (List.getElem?_eq_some_iff.1 hgr).1 hoq
    have hSr' : Reads gs' S (11 + q) := by
      obtain ⟨gS, hgS, hmS⟩ := hSr
      exact ⟨gS, by rw [hget_ne S (by omega)]; exact hgS, hmS⟩
    have hSp : S ≠ p := by
      rintro rfl
      obtain ⟨gS, hgS, hmS⟩ := hSr
      have := gate_eq hgp hgS rfl; subst this
      have hm : 11 + q = l ∨ 11 + q = 11 + ph := by
        rcases hin with e | e <;> rw [e] at hmS <;> simp at hmS <;> omega
      rcases hm with e | e
      · rcases hlit with el | ⟨pn, el, hpn⟩
        · have := y.isLt; omega
        · have hqpn : q = pn := by omega
          subst hqpn
          have := gate_eq hgr hpn rfl; subst this
          simp at hmrph; have := y.isLt; omega
      · omega
    have h4 := hsave {ph, p, q, S} (fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hph_rc
      · exact rc_of_reads hp_reads' hph_isc
      · exact rc_of_reads hr_reads' hph_isc
      · exact rc_of_reads hSr' hq_isc)
    have hcard : ({ph, p, q, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨p, q, S, Ne.symm hrp, Ne.symm hSp, by omega, rfl⟩]
    rwa [hcard] at h4
  · have hq_reads' : Reads gs' q 0 := by
      obtain ⟨gq, hgq, hmq⟩ := hqr0
      exact ⟨gq, by rw [hget_ne q hqph]; exact hgq, hmq⟩
    have h4 := hsave {ph, p, r, q} (fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hph_rc
      · exact rc_of_reads hp_reads' hph_isc
      · exact rc_of_reads hr_reads' hph_isc
      · exact rc_input false hq_reads')
    have hcard : ({ph, p, r, q} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨p, r, q, Ne.symm hrp, Ne.symm hqp, Ne.symm hqr, rfl⟩]
    rwa [hcard] at h4

theorem lb_of_drop_D (y : Fin 11) (hy : y ∈ D) (s : ℕ) (hp : Pays (F G ∅) y s) : 16 ≤ s := by
  have hor : (y = 3 ∨ y = 6 ∨ y = 9) ∨ (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) :=
    (by decide : ∀ w : Fin 11, w ∈ D →
      (w = 3 ∨ w = 6 ∨ w = 9) ∨ (w = 2 ∨ w = 4 ∨ w = 5 ∨ w = 7 ∨ w = 8 ∨ w = 10)) y hy
  rcases hor with hm | ho
  · rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
    · have := lb_mid_false y hm s' h2; omega
    · have := lb_mid_false y hm s' h2; omega
    · have := lb_mid_true y hm s' h2; omega
  · rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩
    · have := lb_outer_false y ho s' h2; omega
    · have := lb_outer_false y ho s' h2; omega
    · have := lb_outer_false y ho s' h2; omega

theorem main (s : ℕ) (hC : HasCircuitSize 11 (F G ∅) s) : 16 ≤ s := by
  classical
  have hfnc : ∃ x x' : Fin 11 → Bool, F G ∅ x ≠ F G ∅ x' := by
    obtain ⟨x, x', h⟩ := hnc_all 3 false; exact ⟨_, _, h⟩
  obtain ⟨gs, o, L, hls⟩ := exists_least 11 (F G ∅) s hfnc hC
  by_cases hO : OneReader D gs
  · obtain ⟨p, g, y, l, h, hF, hop⟩ := exists_front_D L hO
    obtain ⟨hmid, hge11, hchar⟩ := front_h_char L hO hF
    obtain ⟨ph, rfl⟩ : ∃ ph, h = 11 + ph := ⟨h - 11, by omega⟩
    have hhmem : 11 + ph ∈ g.inputs := by rcases hF.2.2.1 with e | e <;> simp [e]
    have hphp : ph < p := by have := (L.hcl p g hF.1).lt _ hhmem; omega
    have hph_len : ph < gs.length := by
      have := (List.getElem?_eq_some_iff.1 hF.1).1; omega
    by_cases hsec : ∃ r, r ≠ p ∧ Reads gs r (11 + ph)
    · obtain ⟨r, hrp, hrr⟩ := hsec
      obtain ⟨s', h1, h2⟩ := shared_h_pay L hF hchar hrp hrr
      have := lb_del0 s' h2
      omega
    · push Not at hsec
      have hone : ∀ t, Reads gs t (11 + ph) → t = p := fun t ht => by
        by_contra hne; exact hsec t hne ht
      have hoh : o ≠ 11 + ph := by
        rintro rfl
        obtain ⟨x, hx⟩ := hdep_all y
        apply hx
        rw [← L.hev, ← L.hev]
        exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
          (agree_inputs _ _)).2.2 (11 + ph) (fun k hk => by
            have : k ≠ y := fun e => hF.2.2.2.2.2 y hF.2.2.2.1 (e ▸ hk)
            simp [Function.update_of_ne this])
      rcases hF.2.1 with hand | hor
      · have hA := stmtAnd 10 (F G ∅) gs o p ph l g y L (hnc_all y) (hdep_all y) hF.1 hand
          hF.2.2.1 hF.2.2.2.2.1 hph_len hone hop hoh
        by_cases hl : l = (y : ℕ)
        · obtain ⟨s', h1, h2⟩ := hA.1 hl
          have := lb_mid_false y hmid s' h2; omega
        · obtain ⟨s', h1, h2⟩ := hA.2 hl
          have := lb_mid_true y hmid s' h2; omega
      · rcases or_only_reader_pay L hF.1 hor hF.2.2.1 hF.2.2.2.2.1 hph_len hone hop hoh with
          ⟨s', h1, h2⟩ | ⟨s', h1, h2⟩
        · have := lb_mid_true y hmid s' h2; omega
        · have := lb_mid_false y hmid s' h2; omega
  · simp only [OneReader, not_and_or] at hO
    push Not at hO
    rcases hO with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · have h16 := lb_of_drop_D y hy gs.length (L.two_readers y (hnc_all y) p q hpq hp hq)
      omega
    · obtain ⟨⟨s', h1, h2⟩, _⟩ := L.not_two_readers y (hnc_all y) pn _ hpn rfl (by simp) p q hpq hp hq
      have hor : (y = 3 ∨ y = 6 ∨ y = 9) ∨ (y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 ∨ y = 8 ∨ y = 10) :=
        (by decide : ∀ w : Fin 11, w ∈ D →
          (w = 3 ∨ w = 6 ∨ w = 9) ∨ (w = 2 ∨ w = 4 ∨ w = 5 ∨ w = 7 ∨ w = 8 ∨ w = 10)) y hy
      rcases hor with hm | ho
      · have := lb_mid_false y hm s' h2; omega
      · have := lb_outer_false y ho s' h2; omega

end PEqualNP.Outside.L_meta_657_aux

theorem PEqualNP.Outside.L_meta_657 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 11 (fun x : Fin 11 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)) s → 16 ≤ s := by
  intro s h
  change PEqualNP.MetaComplexity.HasCircuitSize 11 PEqualNP.Outside.L_meta_657_aux.target s at h
  rw [← PEqualNP.Outside.L_meta_657_aux.F_eq_target] at h
  exact PEqualNP.Outside.L_meta_657_aux.main s h
