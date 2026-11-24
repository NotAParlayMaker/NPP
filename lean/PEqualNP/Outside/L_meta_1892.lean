import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1892

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def diffList : List ℕ := [0, 5, 7, 17, 20]

def targetList : List ℕ := [0, 1, 2, 6, 8, 18, 24, 31, 33, 37]

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def inc (u v : Fin 42) : Bool :=
  decide (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ diffList)

def adj (u v : Fin 42) : Bool :=
  inc u v || inc v u

def mkEdge (u v : Fin 42) : Fin 42 × Fin 42 :=
  if u.val < 21 then (u, v) else (v, u)

def allEdges : Finset (Fin 42 × Fin 42) :=
  Finset.univ.filter (fun e => inc e.1 e.2 = true)

def targetSet (x : Fin 42) : Bool :=
  decide (x.val ∈ targetList)

def singleVec (u : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = u)

def pairVec (u v : Fin 42) : Fin 42 → Bool :=
  fun i => decide (i = u ∨ i = v)

def edgeVec (e : Fin 42 × Fin 42) : Fin 42 → Bool :=
  pairVec e.1 e.2

def computesF (C : Circuit) : Prop :=
  ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 42, inc u v = true ∧ x u = true ∧ x v = true

def diffFin : Fin 5 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 7
  | ⟨3, _⟩ => 17
  | ⟨4, _⟩ => 20

lemma diffFin_mem (k : Fin 5) : diffFin k ∈ diffList := by
  fin_cases k <;> decide

lemma mem_diffList_iff (d : ℕ) : d ∈ diffList ↔ ∃ k : Fin 5, diffFin k = d := by
  constructor
  · intro h
    simp only [diffList, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨0, by omega⟩, rfl⟩
    · exact ⟨⟨1, by omega⟩, rfl⟩
    · exact ⟨⟨2, by omega⟩, rfl⟩
    · exact ⟨⟨3, by omega⟩, rfl⟩
    · exact ⟨⟨4, by omega⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact diffFin_mem k

lemma diffFin_inj : Function.Injective diffFin := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [diffFin] at h ⊢

lemma card_allEdges : allEdges.card = 105 := by
  let f : Fin 21 × Fin 5 → Fin 42 × Fin 42 := fun pk =>
    (⟨pk.1.val, by omega⟩, ⟨21 + (pk.1.val + diffFin pk.2) % 21, by omega⟩)
  have hfinj : Function.Injective f := by
    rintro ⟨p1, k1⟩ ⟨p2, k2⟩ h
    have hp : p1.val = p2.val := congrArg (fun x => x.1.val) h
    have hp' : p1 = p2 := Fin.ext hp
    subst hp'
    have hl : (p1.val + diffFin k1) % 21 = (p1.val + diffFin k2) % 21 := by
      have := congrArg (fun x => x.2.val) h
      dsimp [f] at this
      omega
    have hd1 : diffFin k1 < 21 := by fin_cases k1 <;> decide
    have hd2 : diffFin k2 < 21 := by fin_cases k2 <;> decide
    have hdeq : diffFin k1 = diffFin k2 := by omega
    exact Prod.ext rfl (diffFin_inj hdeq)
  have himg : Finset.univ.image f = allEdges := by
    ext ⟨u, v⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, allEdges, Finset.mem_filter,
      inc, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨p, k⟩, h⟩
      have hu : u.val = p.val := (congrArg (fun x => x.1.val) h).symm
      have hv : v.val = 21 + (p.val + diffFin k) % 21 := (congrArg (fun x => x.2.val) h).symm
      have hd : diffFin k < 21 := by fin_cases k <;> decide
      refine ⟨by omega, by omega, ?_⟩
      have hmod : (v.val + 21 - u.val) % 21 = diffFin k := by omega
      rw [hmod]
      exact diffFin_mem k
    · rintro ⟨hu, hv, hmem⟩
      obtain ⟨k, hk⟩ := (mem_diffList_iff _).mp hmem
      refine ⟨(⟨u.val, hu⟩, k), ?_⟩
      apply Prod.ext
      · apply Fin.ext; rfl
      · apply Fin.ext; dsimp [f]; omega
  rw [← himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

lemma adj_irrefl (u : Fin 42) : adj u u = false := by
  simp only [adj, inc, Bool.or_self, decide_eq_false_iff_not]
  omega

lemma adj_symm (u v : Fin 42) : adj u v = adj v u := by
  simp [adj, Bool.or_comm]

lemma inc_bounds {u v : Fin 42} (h : inc u v = true) :
    u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ diffList := by
  simpa [inc] using h

lemma mkEdge_symm {u v : Fin 42} (h : adj u v = true) : mkEdge u v = mkEdge v u := by
  simp only [adj, Bool.or_eq_true] at h
  rcases h with h | h
  · have hb := inc_bounds h
    simp [mkEdge, hb.1, show ¬ v.val < 21 by omega]
  · have hb := inc_bounds h
    simp [mkEdge, hb.1, show ¬ u.val < 21 by omega]

lemma mkEdge_eq_of_inc {u v : Fin 42} (h : inc u v = true) : mkEdge u v = (u, v) := by
  have hb := inc_bounds h
  simp [mkEdge, hb.1]

lemma mkEdge_swap_of_inc {u v : Fin 42} (h : inc u v = true) : mkEdge v u = (u, v) := by
  have hb := inc_bounds h
  simp [mkEdge, show ¬ v.val < 21 by omega]

lemma inc_mkEdge {u v : Fin 42} (h : adj u v = true) :
    inc (mkEdge u v).1 (mkEdge u v).2 = true := by
  simp only [adj, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [mkEdge_eq_of_inc h]; exact h
  · rw [mkEdge_swap_of_inc h]; exact h

lemma deg_le_five (u : Fin 42) :
    (Finset.univ.filter (fun v : Fin 42 => adj u v = true)).card ≤ 5 := by
  by_cases hu : u.val < 21
  · let g : Fin 5 → Fin 42 := fun k => ⟨21 + (u.val + diffFin k) % 21, by omega⟩
    have hsub : Finset.univ.filter (fun v : Fin 42 => adj u v = true) ⊆ Finset.univ.image g := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, adj, Bool.or_eq_true] at hv
      have hinc : inc u v = true := by
        rcases hv with h | h
        · exact h
        · exfalso; have := inc_bounds h; omega
      have hb := inc_bounds hinc
      obtain ⟨k, hk⟩ := (mem_diffList_iff _).mp hb.2.2
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨k, ?_⟩
      apply Fin.ext; dsimp [g]; omega
    calc (Finset.univ.filter (fun v : Fin 42 => adj u v = true)).card
        ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
      _ = 5 := by simp
  · let g : Fin 5 → Fin 42 := fun k => ⟨(u.val + 21 - diffFin k) % 21, by omega⟩
    have hsub : Finset.univ.filter (fun v : Fin 42 => adj u v = true) ⊆ Finset.univ.image g := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, adj, Bool.or_eq_true] at hv
      have hinc : inc v u = true := by
        rcases hv with h | h
        · exfalso; have := inc_bounds h; omega
        · exact h
      have hb := inc_bounds hinc
      obtain ⟨k, hk⟩ := (mem_diffList_iff _).mp hb.2.2
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨k, ?_⟩
      have hd : diffFin k < 21 := by fin_cases k <;> decide
      apply Fin.ext; dsimp [g]; omega
    calc (Finset.univ.filter (fun v : Fin 42 => adj u v = true)).card
        ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
      _ = 5 := by simp

lemma diff_unique_aux :
    ∀ a ∈ diffList, ∀ b ∈ diffList, ∀ c ∈ diffList, ∀ d ∈ diffList,
      a ≠ b → (a + 21 - b) % 21 = (c + 21 - d) % 21 → a = c ∧ b = d := by
  decide

lemma c4_free {u1 u2 v1 v2 : Fin 42} (hu : u1 ≠ u2) (hv : v1 ≠ v2)
    (h11 : adj u1 v1 = true) (h12 : adj u1 v2 = true)
    (h21 : adj u2 v1 = true) (h22 : adj u2 v2 = true) : False := by
  have hcase : ∀ (p1 p2 l1 l2 : Fin 42), p1 ≠ p2 → l1 ≠ l2 →
      inc p1 l1 = true → inc p1 l2 = true → inc p2 l1 = true → inc p2 l2 = true → False := by
    intro p1 p2 l1 l2 hp hl i11 i12 i21 i22
    have b11 := inc_bounds i11
    have b12 := inc_bounds i12
    have b21 := inc_bounds i21
    have b22 := inc_bounds i22
    set a := (l1.val + 21 - p1.val) % 21
    set b := (l1.val + 21 - p2.val) % 21
    set c := (l2.val + 21 - p1.val) % 21
    set d := (l2.val + 21 - p2.val) % 21
    have hab : a ≠ b := by
      intro heq
      apply hp
      apply Fin.ext
      omega
    have hmod : (a + 21 - b) % 21 = (c + 21 - d) % 21 := by
      omega
    have hac := (diff_unique_aux a b11.2.2 b b21.2.2 c b12.2.2 d b22.2.2 hab hmod).1
    apply hl
    apply Fin.ext
    omega
  simp only [adj, Bool.or_eq_true] at h11 h12 h21 h22
  rcases h11 with h11 | h11
  · have b11 := inc_bounds h11
    have h12' : inc u1 v2 = true := by
      rcases h12 with h | h
      · exact h
      · exfalso; have := inc_bounds h; omega
    have h21' : inc u2 v1 = true := by
      rcases h21 with h | h
      · exact h
      · exfalso; have := inc_bounds h; omega
    have h22' : inc u2 v2 = true := by
      rcases h22 with h | h
      · exact h
      · exfalso; have := inc_bounds h; have := inc_bounds h21'; omega
    exact hcase u1 u2 v1 v2 hu hv h11 h12' h21' h22'
  · have b11 := inc_bounds h11
    have h12' : inc v2 u1 = true := by
      rcases h12 with h | h
      · exfalso; have := inc_bounds h; omega
      · exact h
    have h21' : inc v1 u2 = true := by
      rcases h21 with h | h
      · exfalso; have := inc_bounds h; omega
      · exact h
    have h22' : inc v2 u2 = true := by
      rcases h22 with h | h
      · exfalso; have := inc_bounds h; have := inc_bounds h21'; omega
      · exact h
    exact hcase v1 v2 u1 u2 hv hu h11 h21' h12' h22'

lemma unique_common_nbr {s : Finset (Fin 42)} (hs : 2 ≤ s.card)
    {u1 u2 : Fin 42} (h1 : ∀ v ∈ s, adj u1 v = true) (h2 : ∀ v ∈ s, adj u2 v = true) :
    u1 = u2 := by
  by_contra hne
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  exact c4_free hne hvne (h1 v1 hv1) (h1 v2 hv2) (h2 v1 hv1) (h2 v2 hv2)

-- Automorphisms of PG(2,4)

def shiftAut (c : Fin 21) (x : Fin 42) : Fin 42 :=
  if x.val < 21 then ⟨(x.val + c.val) % 21, by omega⟩
  else ⟨21 + (x.val - 21 + c.val) % 21, by omega⟩

def polAut (c : Fin 21) (x : Fin 42) : Fin 42 :=
  if x.val < 21 then ⟨21 + (21 - x.val + c.val) % 21, by omega⟩
  else ⟨(21 - (x.val - 21) + c.val) % 21, by omega⟩

lemma shiftAut_inc (c : Fin 21) (u v : Fin 42) :
    inc (shiftAut c u) (shiftAut c v) = inc u v := by
  by_cases hu : u.val < 21 <;> by_cases hv : v.val < 21
  · simp [inc, shiftAut, hu, hv, show ¬ (21 ≤ (v.val + c.val) % 21) by omega]
  · simp only [inc, shiftAut, hu, hv, ↓reduceIte]
    have h1 : (u.val + c.val) % 21 < 21 := Nat.mod_lt _ (by omega)
    have h2 : 21 ≤ 21 + (v.val - 21 + c.val) % 21 := by omega
    have h3 : (21 + (v.val - 21 + c.val) % 21 + 21 - (u.val + c.val) % 21) % 21 =
        (v.val + 21 - u.val) % 21 := by omega
    simp [show 21 ≤ v.val by omega, h1, h2, h3]
  · simp [inc, shiftAut, hu, hv, show ¬ (21 + (u.val - 21 + c.val) % 21 < 21) by omega]
  · simp [inc, shiftAut, hu, hv, show ¬ (21 + (u.val - 21 + c.val) % 21 < 21) by omega]

lemma polAut_inc (c : Fin 21) (u v : Fin 42) :
    inc (polAut c v) (polAut c u) = inc u v := by
  by_cases hu : u.val < 21 <;> by_cases hv : v.val < 21
  · simp [inc, polAut, hu, hv, show ¬ (21 ≤ v.val) by omega,
      show ¬ (21 + (21 - v.val + c.val) % 21 < 21) by omega]
  · simp only [inc, polAut, hu, hv, ↓reduceIte]
    have h1 : (21 - (v.val - 21) + c.val) % 21 < 21 := Nat.mod_lt _ (by omega)
    have h2 : 21 ≤ 21 + (21 - u.val + c.val) % 21 := by omega
    have h3 : (21 + (21 - u.val + c.val) % 21 + 21 - (21 - (v.val - 21) + c.val) % 21) % 21 =
        (v.val + 21 - u.val) % 21 := by omega
    simp [show 21 ≤ v.val by omega, h1, h2, h3]
  · simp [inc, polAut, hu, hv, show ¬ (21 + (21 - v.val + c.val) % 21 < 21) by omega]
  · simp [inc, polAut, hu, hv, show ¬ (21 ≤ (21 - (u.val - 21) + c.val) % 21) by omega]

lemma polAut_inv (c : Fin 21) (x : Fin 42) :
    polAut c (polAut c x) = x := by
  by_cases hx : x.val < 21
  · simp only [polAut, hx, ↓reduceIte, show ¬ (21 + (21 - x.val + c.val) % 21 < 21) by omega]
    apply Fin.ext; dsimp; omega
  · simp only [polAut, hx, ↓reduceIte, show (21 - (x.val - 21) + c.val) % 21 < 21 by omega]
    apply Fin.ext; dsimp; omega

lemma shiftAut_preserves_f (c : Fin 21) (y : Fin 42 → Bool) :
    (∃ u v : Fin 42, inc u v = true ∧ y (shiftAut c u) = true ∧ y (shiftAut c v) = true) ↔
    (∃ u v : Fin 42, inc u v = true ∧ y u = true ∧ y v = true) := by
  constructor
  · rintro ⟨u, v, hinc, hu, hv⟩
    exact ⟨shiftAut c u, shiftAut c v, by rw [shiftAut_inc]; exact hinc, hu, hv⟩
  · rintro ⟨u, v, hinc, hu, hv⟩
    let c' : Fin 21 := ⟨(21 - c.val) % 21, Nat.mod_lt _ (by omega)⟩
    refine ⟨shiftAut c' u, shiftAut c' v, by rw [shiftAut_inc]; exact hinc, ?_, ?_⟩
    · have hsc : shiftAut c (shiftAut c' u) = u := by
        by_cases hx : u.val < 21
        · simp only [shiftAut, c', hx, ↓reduceIte, show (u.val + (21 - c.val) % 21) % 21 < 21 by omega]
          apply Fin.ext; dsimp; omega
        · simp only [shiftAut, c', hx, ↓reduceIte,
            show ¬ (21 + (u.val - 21 + (21 - c.val) % 21) % 21 < 21) by omega]
          apply Fin.ext; dsimp; omega
      rw [hsc]; exact hu
    · have hsc : shiftAut c (shiftAut c' v) = v := by
        by_cases hx : v.val < 21
        · simp only [shiftAut, c', hx, ↓reduceIte, show (v.val + (21 - c.val) % 21) % 21 < 21 by omega]
          apply Fin.ext; dsimp; omega
        · simp only [shiftAut, c', hx, ↓reduceIte,
            show ¬ (21 + (v.val - 21 + (21 - c.val) % 21) % 21 < 21) by omega]
          apply Fin.ext; dsimp; omega
      rw [hsc]; exact hv

lemma polAut_preserves_f (c : Fin 21) (y : Fin 42 → Bool) :
    (∃ u v : Fin 42, inc u v = true ∧ y (polAut c u) = true ∧ y (polAut c v) = true) ↔
    (∃ u v : Fin 42, inc u v = true ∧ y u = true ∧ y v = true) := by
  constructor
  · rintro ⟨u, v, hinc, hu, hv⟩
    exact ⟨polAut c v, polAut c u, by rw [polAut_inc]; exact hinc, hv, hu⟩
  · rintro ⟨u, v, hinc, hu, hv⟩
    refine ⟨polAut c v, polAut c u, ?_, by rw [polAut_inv]; exact hv, by rw [polAut_inv]; exact hu⟩
    have h := polAut_inc c (polAut c v) (polAut c u)
    rw [polAut_inv, polAut_inv] at h
    rw [← h]
    exact hinc

lemma shift_cover_pp :
    ∀ d : Fin 21, ∃ p : Fin 21,
      p.val ∈ targetList ∧ (p.val + d.val) % 21 ∈ targetList := by
  decide

lemma shift_cover_pl :
    ∀ d : Fin 21, d.val ∉ diffList → ∃ p : Fin 21,
      p.val ∈ targetList ∧ 21 + (p.val + d.val) % 21 ∈ targetList := by
  decide

lemma exists_aut_to_target (u v : Fin 42) (h : adj u v = false) :
    (∃ c : Fin 21, targetSet (shiftAut c u) = true ∧ targetSet (shiftAut c v) = true) ∨
    (∃ c : Fin 21, targetSet (polAut c u) = true ∧ targetSet (polAut c v) = true) := by
  by_cases hu : u.val < 21 <;> by_cases hv : v.val < 21
  · left
    obtain ⟨p, hp1, hp2⟩ := shift_cover_pp ⟨(v.val + 21 - u.val) % 21, Nat.mod_lt _ (by omega)⟩
    refine ⟨⟨(p.val + 21 - u.val) % 21, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · simp only [targetSet, shiftAut, hu, ↓reduceIte, decide_eq_true_eq]
      have : (u.val + (p.val + 21 - u.val) % 21) % 21 = p.val := by omega
      rw [this]; exact hp1
    · simp only [targetSet, shiftAut, hv, ↓reduceIte, decide_eq_true_eq]
      have : (v.val + (p.val + 21 - u.val) % 21) % 21 = (p.val + (v.val + 21 - u.val) % 21) % 21 := by omega
      rw [this]; exact hp2
  · left
    have hnd : (v.val + 21 - u.val) % 21 ∉ diffList := by
      intro hmem
      have hinc : inc u v = true := by simp [inc, hu, show 21 ≤ v.val by omega, hmem]
      simp [adj, hinc] at h
    obtain ⟨p, hp1, hp2⟩ := shift_cover_pl ⟨(v.val + 21 - u.val) % 21, Nat.mod_lt _ (by omega)⟩ hnd
    refine ⟨⟨(p.val + 21 - u.val) % 21, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · simp only [targetSet, shiftAut, hu, ↓reduceIte, decide_eq_true_eq]
      have : (u.val + (p.val + 21 - u.val) % 21) % 21 = p.val := by omega
      rw [this]; exact hp1
    · simp only [targetSet, shiftAut, hv, ↓reduceIte, decide_eq_true_eq]
      have : 21 + (v.val - 21 + (p.val + 21 - u.val) % 21) % 21 =
          21 + (p.val + (v.val + 21 - u.val) % 21) % 21 := by omega
      rw [this]; exact hp2
  · left
    have hnd : (u.val + 21 - v.val) % 21 ∉ diffList := by
      intro hmem
      have hinc : inc v u = true := by simp [inc, hv, show 21 ≤ u.val by omega, hmem]
      simp [adj, hinc] at h
    obtain ⟨p, hp1, hp2⟩ := shift_cover_pl ⟨(u.val + 21 - v.val) % 21, Nat.mod_lt _ (by omega)⟩ hnd
    refine ⟨⟨(p.val + 21 - v.val) % 21, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · simp only [targetSet, shiftAut, hu, ↓reduceIte, decide_eq_true_eq]
      have : 21 + (u.val - 21 + (p.val + 21 - v.val) % 21) % 21 =
          21 + (p.val + (u.val + 21 - v.val) % 21) % 21 := by omega
      rw [this]; exact hp2
    · simp only [targetSet, shiftAut, hv, ↓reduceIte, decide_eq_true_eq]
      have : (v.val + (p.val + 21 - v.val) % 21) % 21 = p.val := by omega
      rw [this]; exact hp1
  · right
    set u' : ℕ := (21 - (u.val - 21)) % 21
    set v' : ℕ := (21 - (v.val - 21)) % 21
    obtain ⟨p, hp1, hp2⟩ := shift_cover_pp ⟨(v' + 21 - u') % 21, Nat.mod_lt _ (by omega)⟩
    refine ⟨⟨(p.val + 21 - u') % 21, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · simp only [targetSet, polAut, hu, ↓reduceIte, decide_eq_true_eq]
      have : (21 - (u.val - 21) + (p.val + 21 - u') % 21) % 21 = p.val := by omega
      rw [this]; exact hp1
    · simp only [targetSet, polAut, hv, ↓reduceIte, decide_eq_true_eq]
      have : (21 - (v.val - 21) + (p.val + 21 - u') % 21) % 21 =
          (p.val + (v' + 21 - u') % 21) % 21 := by omega
      rw [this]; exact hp2

-- List and circuit wire helpers

lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_of_ge {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_singleton_zero {α : Type} (x d : α) : ([x] : List α).getD 0 d = x := rfl

lemma ofFn_getD {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresAux (gs : List Gate) (init : List Bool) : List Bool :=
  gs.foldl stepWire init

lemma wires_eq_wiresAux (C : Circuit) (x : List Bool) :
    C.wires x = wiresAux C.gates x := rfl

lemma wiresAux_nil (init : List Bool) : wiresAux [] init = init := rfl

lemma wiresAux_append (gs1 gs2 : List Gate) (init : List Bool) :
    wiresAux (gs1 ++ gs2) init = wiresAux gs2 (wiresAux gs1 init) := by
  simp [wiresAux, List.foldl_append]

lemma wiresAux_concat (gs : List Gate) (g : Gate) (init : List Bool) :
    wiresAux (gs ++ [g]) init = stepWire (wiresAux gs init) g := by
  simp [wiresAux, List.foldl_append]

lemma wiresAux_length (gs : List Gate) (init : List Bool) :
    (wiresAux gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [wiresAux]
  | cons g rest ih =>
    simp only [wiresAux, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [stepWire]
    omega

lemma wiresAux_prefix_getD (gs : List Gate) (init : List Bool) (i : ℕ) (hi : i < init.length) :
    (wiresAux gs init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [wiresAux, List.foldl_cons] at ih ⊢
    have hi' : i < (stepWire init g).length := by simp [stepWire]; omega
    rw [ih (stepWire init g) hi']
    exact getD_append_left init _ i false hi

lemma wiresAux_take_getD (gs : List Gate) (init : List Bool) (k i : ℕ)
    (hi : i < init.length + k) :
    (wiresAux gs init).getD i false = (wiresAux (gs.take k) init).getD i false := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_lhs => rw [hsplit]
  rw [wiresAux_append]
  by_cases hk : k ≤ gs.length
  · apply wiresAux_prefix_getD
    rw [wiresAux_length, List.length_take, Nat.min_eq_left hk]
    exact hi
  · have hdrop : gs.drop k = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, wiresAux_nil]

lemma wiresAux_gate_getD (gs : List Gate) (init : List Bool) (k : ℕ) (g : Gate)
    (hg : gs[k]? = some g) :
    (wiresAux gs init).getD (init.length + k) false =
      g.op.eval (g.inputs.map fun i => (wiresAux (gs.take k) init).getD i false) := by
  have hk : k < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have htake : gs.take (k + 1) = gs.take k ++ [g] := by
    rw [List.take_add_one, hg, Option.toList_some]
  have h1 := wiresAux_take_getD gs init (k + 1) (init.length + k) (by omega)
  rw [h1, htake, wiresAux_concat, stepWire]
  have hlen : (wiresAux (gs.take k) init).length = init.length + k := by
    rw [wiresAux_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, getD_singleton_zero]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ i, l1.getD i false = true → l2.getD i false = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi1 : i < l1.length := by omega
    have h1i : l1[i] = true := h1 l1[i] (List.getElem_mem hi1)
    have hd : l1.getD i false = true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, h1i]
    have hd2 := hle i hd
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hd2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have hi2 : i < l2.length := by omega
    have hd : l1.getD i false = true := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hbi]
    have hd2 := hle i hd
    refine ⟨l2[i], List.getElem_mem hi2, ?_⟩
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2] using hd2

lemma wiresAux_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    ∀ i, (wiresAux gs w1).getD i false = true → (wiresAux gs w2).getD i false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g rest ih =>
    simp only [wiresAux, List.foldl_cons] at ih ⊢
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg'))
    · simp [stepWire, hlen]
    · intro i hi
      by_cases hil : i < w1.length
      · rw [stepWire, getD_append_left w1 _ i false hil] at hi
        rw [stepWire, getD_append_left w2 _ i false (by omega)]
        exact hle i hi
      · by_cases hieq : i = w1.length
        · subst hieq
          rw [stepWire, getD_append_right w1 _ _ false (le_refl _), Nat.sub_self,
              getD_singleton_zero] at hi
          rw [stepWire, getD_append_right w2 _ _ false (by omega), ← hlen, Nat.sub_self,
              getD_singleton_zero]
          refine gateOp_eval_mono g.op (hmono g (List.mem_cons_self ..))
            (g.inputs.map fun j => w1.getD j false)
            (g.inputs.map fun j => w2.getD j false)
            (by simp) ?_ hi
          intro j hj
          by_cases hjl : j < g.inputs.length
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hjl, Option.map_some, Option.getD_some] at hj ⊢
            exact hle g.inputs[j] hj
          · rw [getD_of_ge _ _ false (by simp; omega)] at hj
            cases hj
        · rw [stepWire, getD_of_ge _ _ false (by simp; omega)] at hi
          cases hi

-- Circuit input permutation

def remapWire (σ : Fin 42 → Fin 42) (i : ℕ) : ℕ :=
  if h : i < 42 then (σ ⟨i, h⟩).val else i

def permuteGate (σ : Fin 42 → Fin 42) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (remapWire σ) }

def permuteCircuit (σ : Fin 42 → Fin 42) (C : Circuit) : Circuit :=
  { gates := C.gates.map (permuteGate σ), output := remapWire σ C.output }

lemma permuteCircuit_monotone2 (σ : Fin 42 → Fin 42) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (permuteCircuit σ C) := by
  intro g hg
  simp only [permuteCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have h0 := hm g0 hg0
  exact ⟨h0.1, by simp [permuteGate, h0.2]⟩

lemma permuteCircuit_size (σ : Fin 42 → Fin 42) (C : Circuit) :
    (permuteCircuit σ C).size = C.size := by
  simp [Circuit.size, permuteCircuit]

lemma permuteCircuit_wiresAux (σ : Fin 42 → Fin 42) (gs : List Gate) (y : Fin 42 → Bool)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h42 : 42 ≤ w1.length)
    (hin : ∀ i (hi : i < 42), w1.getD i false = y (σ ⟨i, hi⟩) ∧ w2.getD i false = y ⟨i, hi⟩)
    (hge : ∀ j, 42 ≤ j → w1.getD j false = w2.getD j false) :
    (∀ i (hi : i < 42),
      (wiresAux gs w1).getD i false = y (σ ⟨i, hi⟩) ∧
      (wiresAux (gs.map (permuteGate σ)) w2).getD i false = y ⟨i, hi⟩) ∧
    (∀ j, 42 ≤ j →
      (wiresAux gs w1).getD j false = (wiresAux (gs.map (permuteGate σ)) w2).getD j false) := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨hin, hge⟩
  | cons g rest ih =>
    simp only [List.map_cons, wiresAux, List.foldl_cons] at ih ⊢
    have hval : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        (permuteGate σ g).op.eval ((permuteGate σ g).inputs.map fun i => w2.getD i false) := by
      simp only [permuteGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro idx _
      simp only [Function.comp_apply, remapWire]
      split_ifs with hlt
      · rw [(hin idx hlt).1, (hin (σ ⟨idx, hlt⟩).val (σ ⟨idx, hlt⟩).isLt).2]
      · exact hge idx (by omega)
    apply ih (stepWire w1 g) (stepWire w2 (permuteGate σ g))
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro i hi
      rw [stepWire, getD_append_left w1 _ i false (by omega),
          stepWire, getD_append_left w2 _ i false (by omega)]
      exact hin i hi
    · intro j hj
      by_cases hjl : j < w1.length
      · rw [stepWire, getD_append_left w1 _ j false hjl,
            stepWire, getD_append_left w2 _ j false (by omega)]
        exact hge j hj
      · by_cases hjeq : j = w1.length
        · subst hjeq
          rw [stepWire, getD_append_right w1 _ _ false (le_refl _), Nat.sub_self,
              getD_singleton_zero,
              stepWire, getD_append_right w2 _ _ false (by omega), ← hlen, Nat.sub_self,
              getD_singleton_zero]
          exact hval
        · rw [stepWire, getD_of_ge _ _ false (by simp; omega),
              stepWire, getD_of_ge _ _ false (by simp; omega)]

lemma permuteCircuit_wires_ge (σ : Fin 42 → Fin 42) (C : Circuit) (y : Fin 42 → Bool)
    (j : ℕ) (hj : 42 ≤ j) :
    ((permuteCircuit σ C).wires (List.ofFn y)).getD j false =
      (C.wires (List.ofFn (fun i => y (σ i)))).getD j false := by
  have h := permuteCircuit_wiresAux σ C.gates y
    (List.ofFn (fun i => y (σ i))) (List.ofFn y)
    (by simp) (by simp)
    (by
      intro i hi
      exact ⟨ofFn_getD (fun k => y (σ k)) i false hi, ofFn_getD y i false hi⟩)
    (by
      intro m hm
      rw [getD_of_ge _ _ false (by rw [List.length_ofFn]; omega),
          getD_of_ge _ _ false (by rw [List.length_ofFn]; omega)])
  exact (h.2 j hj).symm

lemma permuteCircuit_eval (σ : Fin 42 → Fin 42) (C : Circuit) (y : Fin 42 → Bool) :
    (permuteCircuit σ C).eval (List.ofFn y) = C.eval (List.ofFn (fun i => y (σ i))) := by
  simp only [Circuit.eval, permuteCircuit, remapWire]
  have h := permuteCircuit_wiresAux σ C.gates y
    (List.ofFn (fun i => y (σ i))) (List.ofFn y)
    (by simp) (by simp)
    (by
      intro i hi
      exact ⟨ofFn_getD (fun k => y (σ k)) i false hi, ofFn_getD y i false hi⟩)
    (by
      intro m hm
      rw [getD_of_ge _ _ false (by rw [List.length_ofFn]; omega),
          getD_of_ge _ _ false (by rw [List.length_ofFn]; omega)])
  split_ifs with hlt
  · change (wiresAux (C.gates.map (permuteGate σ)) (List.ofFn y)).getD (σ ⟨C.output, hlt⟩).val false =
      (wiresAux C.gates (List.ofFn (fun i => y (σ i)))).getD C.output false
    rw [(h.1 C.output hlt).1, (h.1 (σ ⟨C.output, hlt⟩).val (σ ⟨C.output, hlt⟩).isLt).2]
  · exact (h.2 C.output (by omega)).symm

-- Case 1: Some AND gate evaluates to true on an independent set

lemma or_path_witness (C : Circuit) (hm : Monotone2 C) (k : ℕ) (x : Fin 42 → Bool)
    (hno : ∀ j < k, ∀ g, C.gates[j]? = some g → g.op = GateOp.and →
      (C.wires (List.ofFn x)).getD (42 + j) false = false) :
    ∀ w < 42 + k, (C.wires (List.ofFn x)).getD w false = true →
      ∃ u : Fin 42, x u = true ∧
        ∀ y : Fin 42 → Bool, y u = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwk htrue
    by_cases hw42 : w < 42
    · refine ⟨⟨w, hw42⟩, ?_, ?_⟩
      · have h1 := wiresAux_prefix_getD C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw42)
        rw [wires_eq_wiresAux, h1, ofFn_getD x w false hw42] at htrue
        exact htrue
      · intro y hy
        rw [wires_eq_wiresAux,
            wiresAux_prefix_getD C.gates (List.ofFn y) w (by rw [List.length_ofFn]; exact hw42),
            ofFn_getD y w false hw42]
        exact hy
    · set j := w - 42
      have hwj : w = 42 + j := by omega
      have hjk : j < k := by omega
      cases hgj : C.gates[j]? with
      | none =>
        have hlen : C.gates.length ≤ j := by
          by_contra hlt
          rw [List.getElem?_eq_getElem (by omega)] at hgj
          cases hgj
        rw [wires_eq_wiresAux, getD_of_ge _ _ false (by rw [wiresAux_length, List.length_ofFn]; omega)] at htrue
        cases htrue
      | some gj =>
        have hmem : gj ∈ C.gates := List.mem_of_getElem? hgj
        have hop := (hm gj hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor
        · have hf := hno j hjk gj hgj hand
          rw [hwj] at htrue
          rw [hf] at htrue
          cases htrue
        · have hgate := wiresAux_gate_getD C.gates (List.ofFn x) j gj hgj
          simp only [List.length_ofFn] at hgate
          rw [hwj, wires_eq_wiresAux, hgate, hor] at htrue
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrue
          obtain ⟨_, ⟨a, ha_in, rfl⟩, ha_true⟩ := htrue
          have ha_lt : a < 42 + j := by
            by_contra hge
            have hlen : (wiresAux (C.gates.take j) (List.ofFn x)).length ≤ a := by
              rw [wiresAux_length, List.length_ofFn, List.length_take]
              omega
            rw [getD_of_ge _ _ false hlen] at ha_true
            cases ha_true
          have ha_full : (C.wires (List.ofFn x)).getD a false = true := by
            rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn x) j a (by rw [List.length_ofFn]; omega)]
            exact ha_true
          obtain ⟨u, hxu, hyu⟩ := ih a (by omega) (by omega) ha_full
          refine ⟨u, hxu, ?_⟩
          intro y hy
          have hgatey := wiresAux_gate_getD C.gates (List.ofFn y) j gj hgj
          simp only [List.length_ofFn] at hgatey
          rw [hwj, wires_eq_wiresAux, hgatey, hor]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          refine ⟨true, ⟨a, ha_in, ?_⟩, rfl⟩
          have ha_y := hyu y hy
          rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn y) j a (by rw [List.length_ofFn]; omega)] at ha_y
          exact ha_y

lemma case1_solve (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 124) (hc : computesF C)
    (hex : ∃ k : ℕ, ∃ g : Gate, C.gates[k]? = some g ∧ g.op = GateOp.and ∧
      ∃ x : Fin 42 → Bool,
        (¬ ∃ u v : Fin 42, inc u v = true ∧ x u = true ∧ x v = true) ∧
        (C.wires (List.ofFn x)).getD (42 + k) false = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 124 ∧ computesF D ∧
      ∃ k g, D.gates[k]? = some g ∧ g.op = GateOp.and ∧
        (D.wires (List.ofFn targetSet)).getD (42 + k) false = true := by
  classical
  let P : ℕ → Prop := fun k => ∃ g : Gate, C.gates[k]? = some g ∧ g.op = GateOp.and ∧
    ∃ x : Fin 42 → Bool,
      (¬ ∃ u v : Fin 42, inc u v = true ∧ x u = true ∧ x v = true) ∧
      (C.wires (List.ofFn x)).getD (42 + k) false = true
  let k := Nat.find hex
  have hk : P k := Nat.find_spec hex
  have hmin : ∀ j < k, ¬ P j := fun j hj => Nat.find_min hex hj
  obtain ⟨g, hgk, hgop, x, hx_ind, hx_true⟩ := hk
  have hno : ∀ j < k, ∀ gj, C.gates[j]? = some gj → gj.op = GateOp.and →
      (C.wires (List.ofFn x)).getD (42 + j) false = false := by
    intro j hj gj hgj hgjop
    cases hval : (C.wires (List.ofFn x)).getD (42 + j) false
    · rfl
    · exfalso
      exact hmin j hj ⟨gj, hgj, hgjop, x, hx_ind, hval⟩
  have hlen_in : g.inputs.length ≤ 2 := (hm g (List.mem_of_getElem? hgk)).2
  have hgate_x := wiresAux_gate_getD C.gates (List.ofFn x) k g hgk
  simp only [List.length_ofFn] at hgate_x
  rw [wires_eq_wiresAux, hgate_x, hgop] at hx_true
  have finish_pair : ∀ (u v : Fin 42), adj u v = false →
      (∀ y : Fin 42 → Bool, y u = true → y v = true →
        (C.wires (List.ofFn y)).getD (42 + k) false = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 124 ∧ computesF D ∧
        ∃ k' g', D.gates[k']? = some g' ∧ g'.op = GateOp.and ∧
          (D.wires (List.ofFn targetSet)).getD (42 + k') false = true := by
    intro u v hadj hfire
    rcases exists_aut_to_target u v hadj with ⟨c, htu, htv⟩ | ⟨c, htu, htv⟩
    · refine ⟨permuteCircuit (shiftAut c) C, permuteCircuit_monotone2 _ C hm,
        by rw [permuteCircuit_size]; exact hs, ?_, k, permuteGate (shiftAut c) g, ?_, hgop, ?_⟩
      · intro y
        rw [permuteCircuit_eval, hc, shiftAut_preserves_f]
      · simp [permuteCircuit, hgk]
      · rw [permuteCircuit_wires_ge _ C targetSet (42 + k) (by omega)]
        exact hfire (fun i => targetSet (shiftAut c i)) htu htv
    · refine ⟨permuteCircuit (polAut c) C, permuteCircuit_monotone2 _ C hm,
        by rw [permuteCircuit_size]; exact hs, ?_, k, permuteGate (polAut c) g, ?_, hgop, ?_⟩
      · intro y
        rw [permuteCircuit_eval, hc, polAut_preserves_f]
      · simp [permuteCircuit, hgk]
      · rw [permuteCircuit_wires_ge _ C targetSet (42 + k) (by omega)]
        exact hfire (fun i => targetSet (polAut c i)) htu htv
  cases hin : g.inputs with
  | nil =>
    refine ⟨C, hm, hs, hc, k, g, hgk, hgop, ?_⟩
    have hgt := wiresAux_gate_getD C.gates (List.ofFn targetSet) k g hgk
    simp only [List.length_ofFn] at hgt
    rw [wires_eq_wiresAux, hgt, hgop, hin]
    rfl
  | cons a rest =>
    cases rest with
    | nil =>
      rw [hin] at hx_true
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id_eq] at hx_true
      have ha_lt : a < 42 + k := by
        by_contra hge
        have hlen : (wiresAux (C.gates.take k) (List.ofFn x)).length ≤ a := by
          rw [wiresAux_length, List.length_ofFn, List.length_take]; omega
        rw [getD_of_ge _ _ false hlen] at hx_true
        cases hx_true
      have ha_full : (C.wires (List.ofFn x)).getD a false = true := by
        rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn x) k a (by rw [List.length_ofFn]; omega)]
        exact hx_true
      obtain ⟨u, _, hyu⟩ := or_path_witness C hm k x hno a ha_lt ha_full
      apply finish_pair u u (adj_irrefl u)
      intro y hy _
      have hgy := wiresAux_gate_getD C.gates (List.ofFn y) k g hgk
      simp only [List.length_ofFn] at hgy
      rw [wires_eq_wiresAux, hgy, hgop, hin]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      have ha_y := hyu y hy
      rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn y) k a (by rw [List.length_ofFn]; omega)] at ha_y
      exact ha_y
    | cons b rest2 =>
      cases rest2 with
      | cons _ _ =>
        rw [hin] at hlen_in
        simp at hlen_in
      | nil =>
        rw [hin] at hx_true
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, Bool.and_eq_true, id_eq] at hx_true
        obtain ⟨ha_true, hb_true⟩ := hx_true
        have ha_lt : a < 42 + k := by
          by_contra hge
          have hlen : (wiresAux (C.gates.take k) (List.ofFn x)).length ≤ a := by
            rw [wiresAux_length, List.length_ofFn, List.length_take]; omega
          rw [getD_of_ge _ _ false hlen] at ha_true
          cases ha_true
        have hb_lt : b < 42 + k := by
          by_contra hge
          have hlen : (wiresAux (C.gates.take k) (List.ofFn x)).length ≤ b := by
            rw [wiresAux_length, List.length_ofFn, List.length_take]; omega
          rw [getD_of_ge _ _ false hlen] at hb_true
          cases hb_true
        have ha_full : (C.wires (List.ofFn x)).getD a false = true := by
          rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn x) k a (by rw [List.length_ofFn]; omega)]
          exact ha_true
        have hb_full : (C.wires (List.ofFn x)).getD b false = true := by
          rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn x) k b (by rw [List.length_ofFn]; omega)]
          exact hb_true
        obtain ⟨u, hxu, hyu⟩ := or_path_witness C hm k x hno a ha_lt ha_full
        obtain ⟨v, hxv, hyv⟩ := or_path_witness C hm k x hno b hb_lt hb_full
        have hadj : adj u v = false := by
          cases h : adj u v
          · rfl
          · exfalso
            simp only [adj, Bool.or_eq_true] at h
            rcases h with h | h
            · exact hx_ind ⟨u, v, h, hxu, hxv⟩
            · exact hx_ind ⟨v, u, h, hxv, hxu⟩
        apply finish_pair u v hadj
        intro y hyu_t hyv_t
        have hgy := wiresAux_gate_getD C.gates (List.ofFn y) k g hgk
        simp only [List.length_ofFn] at hgy
        rw [wires_eq_wiresAux, hgy, hgop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, Bool.and_eq_true, id_eq]
        have ha_y := hyu y hyu_t
        have hb_y := hyv y hyv_t
        rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn y) k a (by rw [List.length_ofFn]; omega)] at ha_y
        rw [wires_eq_wiresAux, wiresAux_take_getD C.gates (List.ofFn y) k b (by rw [List.length_ofFn]; omega)] at hb_y
        exact ⟨ha_y, hb_y⟩

-- Case 2: Every AND gate is false on every independent set

def prodEdges (va vb : Finset (Fin 42)) : Finset (Fin 42 × Fin 42) :=
  va.biUnion fun u => vb.image fun v => mkEdge u v

noncomputable def edgeSetOf (s : Finset (Fin 42)) : Finset (Fin 42 × Fin 42) :=
  @dite _ (∃ u : Fin 42, ∀ v ∈ s, adj u v = true) (Classical.propDecidable _)
    (fun h => s.image (fun v => mkEdge (Classical.choose h) v))
    (fun _ => ∅)

noncomputable def Tof (p : Finset (Fin 42) × Finset (Fin 42 × Fin 42)) :
    Finset ((Fin 42 × Fin 42) ⊕ Fin 42) :=
  p.2.image Sum.inl ∪
    if p.1.card = 1 then p.1.image Sum.inr
    else if 2 ≤ p.1.card then (edgeSetOf p.1).image Sum.inl
    else ∅

def initVF : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)) :=
  List.ofFn (fun i : Fin 42 => ({i}, ∅))

def stepVFEntry (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (g : Gate) :
    Finset (Fin 42) × Finset (Fin 42 × Fin 42) :=
  let getV (i : ℕ) := (st.getD i (∅, ∅)).1
  let getF (i : ℕ) := (st.getD i (∅, ∅)).2
  match g.op, g.inputs with
  | GateOp.or, [] => (∅, ∅)
  | GateOp.or, [a] => (getV a, getF a)
  | GateOp.or, [a, b] => (getV a ∪ getV b, getF a ∪ getF b)
  | GateOp.and, [a] => (∅, getF a)
  | GateOp.and, [a, b] =>
    if getV a = ∅ then (∅, getF a)
    else if getV b = ∅ then (∅, getF b)
    else (∅, getF a ∪ getF b ∪ prodEdges (getV a) (getV b))
  | _, _ => (∅, ∅)

def stepVF (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (g : Gate) :
    List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)) :=
  st ++ [stepVFEntry st g]

def runVF (gs : List Gate) : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)) :=
  gs.foldl stepVF initVF

def qOf (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (W : Finset ℕ) : ℕ :=
  (W.filter (fun w => (st.getD w (∅, ∅)).1.card ≠ 1)).card +
  (W.biUnion (fun w => if (st.getD w (∅, ∅)).1.card = 1 then (st.getD w (∅, ∅)).1 else ∅)).card

lemma initVF_length : initVF.length = 42 := by
  simp [initVF]

lemma initVF_getD_lt (w : ℕ) (hw : w < 42) :
    initVF.getD w (∅, ∅) = ({⟨w, hw⟩}, ∅) := by
  exact ofFn_getD
    (fun i : Fin 42 => (({i} : Finset (Fin 42)), (∅ : Finset (Fin 42 × Fin 42))))
    w (∅, ∅) hw

lemma runVF_length (gs : List Gate) : (runVF gs).length = 42 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runVF, initVF_length]
  | append_singleton gs g ih =>
    simp only [runVF, List.foldl_append, List.foldl_cons, List.foldl_nil, stepVF,
      List.length_append, List.length_singleton] at ih ⊢
    omega

lemma runVF_concat (gs : List Gate) (g : Gate) :
    runVF (gs ++ [g]) = stepVF (runVF gs) g := by
  simp [runVF, List.foldl_append]

lemma singleVec_indep (u : Fin 42) :
    ¬ ∃ a b : Fin 42, inc a b = true ∧ singleVec u a = true ∧ singleVec u b = true := by
  rintro ⟨a, b, hinc, ha, hb⟩
  simp only [singleVec, decide_eq_true_eq] at ha hb
  rw [ha, hb] at hinc
  have := adj_irrefl u
  simp [adj, hinc] at this

lemma zeroVec_indep :
    ¬ ∃ a b : Fin 42, inc a b = true ∧ (fun _ : Fin 42 => false) a = true ∧
      (fun _ : Fin 42 => false) b = true := by
  rintro ⟨_, _, _, ha, _⟩
  cases ha

lemma hsafe_prefix {gs : List Gate} {g : Gate}
    (hsafe : ∀ k g', (gs ++ [g])[k]? = some g' → g'.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux (gs ++ [g]) (List.ofFn x)).getD (42 + k) false = false) :
    ∀ k g', gs[k]? = some g' → g'.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux gs (List.ofFn x)).getD (42 + k) false = false := by
  intro k g' hgk hop x hx
  have hkl : k < gs.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hgk
    cases hgk
  have hgk' : (gs ++ [g])[k]? = some g' := by
    rw [List.getElem?_append_left hkl]; exact hgk
  have h := hsafe k g' hgk' hop x hx
  have htake : (gs ++ [g]).take (k + 1) = gs.take (k + 1) :=
    List.take_append_of_le_length (by omega)
  have hlenx : (List.ofFn x).length = 42 := List.length_ofFn
  rw [wiresAux_take_getD (gs ++ [g]) (List.ofFn x) (k + 1) (42 + k) (by omega), htake] at h
  rw [wiresAux_take_getD gs (List.ofFn x) (k + 1) (42 + k) (by omega)]
  exact h

lemma runVF_getV_iff (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsafe : ∀ k g, gs[k]? = some g → g.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux gs (List.ofFn x)).getD (42 + k) false = false) :
    ∀ (w : ℕ) (u : Fin 42),
      u ∈ ((runVF gs).getD w (∅, ∅)).1 ↔ (wiresAux gs (List.ofFn (singleVec u))).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w u
    by_cases hw : w < 42
    · rw [show runVF [] = initVF from rfl, initVF_getD_lt w hw,
          wiresAux_nil, ofFn_getD (singleVec u) w false hw]
      simp [singleVec, eq_comm]
    · rw [show runVF [] = initVF from rfl, getD_of_ge _ _ _ (by rw [initVF_length]; omega),
          wiresAux_nil, getD_of_ge _ _ _ (by rw [List.length_ofFn]; omega)]
      simp
  | append_singleton gs g ih =>
    have hmono_pre : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have ih' := ih hmono_pre (hsafe_prefix hsafe)
    intro w u
    rw [runVF_concat, wiresAux_concat]
    have hlen1 : (runVF gs).length = 42 + gs.length := runVF_length gs
    have hlen2 : (wiresAux gs (List.ofFn (singleVec u))).length = 42 + gs.length := by
      rw [wiresAux_length, List.length_ofFn]
    by_cases hwlt : w < 42 + gs.length
    · rw [stepVF, getD_append_left _ _ w _ (by omega),
          stepWire, getD_append_left _ _ w _ (by omega)]
      exact ih' w u
    · by_cases hweq : w = 42 + gs.length
      · subst hweq
        rw [stepVF, getD_append_right _ _ _ _ (by omega), hlen1, Nat.sub_self, getD_singleton_zero,
            stepWire, getD_append_right _ _ _ _ (by omega), hlen2, Nat.sub_self, getD_singleton_zero]
        have hg_m := hmono g (List.mem_append_right _ (List.mem_singleton_self g))
        rcases hg_m.1 with hand | hor
        · have hgk : (gs ++ [g])[gs.length]? = some g := by
            rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl
          have hf := hsafe gs.length g hgk hand (singleVec u) (singleVec_indep u)
          rw [wiresAux_concat, stepWire, getD_append_right _ _ _ _ (by omega), hlen2, Nat.sub_self,
              getD_singleton_zero] at hf
          rw [hf]
          simp only [stepVFEntry, hand]
          cases hin : g.inputs with
          | nil => simp
          | cons a rest =>
            cases rest with
            | nil => simp
            | cons b rest2 =>
              cases rest2 with
              | nil => dsimp only; split_ifs <;> simp
              | cons _ _ => simp
        · simp only [stepVFEntry, hor]
          cases hin : g.inputs with
          | nil => simp [GateOp.eval]
          | cons a rest =>
            cases rest with
            | nil =>
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                Bool.or_false, id_eq]
              exact ih' a u
            | cons b rest2 =>
              cases rest2 with
              | nil =>
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  Bool.or_false, Bool.or_eq_true, id_eq, Finset.mem_union]
                rw [ih' a u, ih' b u]
              | cons _ _ =>
                rw [hin] at hg_m; simp at hg_m
      · rw [stepVF, getD_of_ge _ _ _ (by rw [List.length_append, List.length_singleton, hlen1]; omega),
            stepWire, getD_of_ge _ _ _ (by rw [List.length_append, List.length_singleton, hlen2]; omega)]
        simp

lemma biclique_of_and (gs : List Gate) (g : Gate)
    (hmono : ∀ g' ∈ gs ++ [g], (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)
    (hsafe : ∀ k g', (gs ++ [g])[k]? = some g' → g'.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux (gs ++ [g]) (List.ofFn x)).getD (42 + k) false = false)
    (hand : g.op = GateOp.and) (a b : ℕ) (hin : g.inputs = [a, b]) :
    ∀ u ∈ ((runVF gs).getD a (∅, ∅)).1, ∀ v ∈ ((runVF gs).getD b (∅, ∅)).1,
      adj u v = true := by
  have hmono_pre : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => hmono g' (List.mem_append_left _ hg')
  have hV := runVF_getV_iff gs hmono_pre (hsafe_prefix hsafe)
  intro u hu v hv
  have hua := (hV a u).mp hu
  have hvb := (hV b v).mp hv
  have hua' : (wiresAux gs (List.ofFn (pairVec u v))).getD a false = true := by
    apply wiresAux_mono gs (fun g' hg' => (hmono_pre g' hg').1)
      (List.ofFn (singleVec u)) (List.ofFn (pairVec u v)) (by simp)
    · intro i hi
      by_cases hi42 : i < 42
      · rw [ofFn_getD (singleVec u) i false hi42] at hi
        rw [ofFn_getD (pairVec u v) i false hi42]
        simp only [singleVec, pairVec, decide_eq_true_eq] at hi ⊢
        left; exact hi
      · rw [getD_of_ge _ _ false (by rw [List.length_ofFn]; omega)] at hi
        cases hi
    · exact hua
  have hvb' : (wiresAux gs (List.ofFn (pairVec u v))).getD b false = true := by
    apply wiresAux_mono gs (fun g' hg' => (hmono_pre g' hg').1)
      (List.ofFn (singleVec v)) (List.ofFn (pairVec u v)) (by simp)
    · intro i hi
      by_cases hi42 : i < 42
      · rw [ofFn_getD (singleVec v) i false hi42] at hi
        rw [ofFn_getD (pairVec u v) i false hi42]
        simp only [singleVec, pairVec, decide_eq_true_eq] at hi ⊢
        right; exact hi
      · rw [getD_of_ge _ _ false (by rw [List.length_ofFn]; omega)] at hi
        cases hi
    · exact hvb
  have hgk : (gs ++ [g])[gs.length]? = some g := by
    rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl
  have hlenp : (wiresAux gs (List.ofFn (pairVec u v))).length = 42 + gs.length := by
    rw [wiresAux_length, List.length_ofFn]
  have hfire : (wiresAux (gs ++ [g]) (List.ofFn (pairVec u v))).getD (42 + gs.length) false = true := by
    rw [wiresAux_concat, stepWire, getD_append_right _ _ _ _ (by omega), hlenp, Nat.sub_self,
        getD_singleton_zero, hand, hin]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, Bool.and_eq_true, id_eq]
    exact ⟨hua', hvb'⟩
  cases hadj : adj u v
  · exfalso
    have hind : ¬ ∃ p l : Fin 42, inc p l = true ∧ pairVec u v p = true ∧ pairVec u v l = true := by
      rintro ⟨p, l, hinc, hp, hl⟩
      simp only [pairVec, decide_eq_true_eq] at hp hl
      rcases hp with hp | hp <;> rcases hl with hl | hl
      · rw [hp, hl] at hinc; have := adj_irrefl u; simp [adj, hinc] at this
      · rw [hp, hl] at hinc; simp [adj, hinc] at hadj
      · rw [hp, hl] at hinc; simp [adj, hinc] at hadj
      · rw [hp, hl] at hinc; have := adj_irrefl v; simp [adj, hinc] at this
    have hf := hsafe gs.length g hgk hand (pairVec u v) hind
    rw [hf] at hfire
    cases hfire
  · rfl

lemma runVF_edge_sound (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsafe : ∀ k g, gs[k]? = some g → g.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux gs (List.ofFn x)).getD (42 + k) false = false) :
    ∀ (w : ℕ) (e : Fin 42 × Fin 42), inc e.1 e.2 = true →
      (wiresAux gs (List.ofFn (edgeVec e))).getD w false = true →
      e ∈ ((runVF gs).getD w (∅, ∅)).2 ∨
      e.1 ∈ ((runVF gs).getD w (∅, ∅)).1 ∨
      e.2 ∈ ((runVF gs).getD w (∅, ∅)).1 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w e _ hw
    by_cases hw42 : w < 42
    · rw [wiresAux_nil, ofFn_getD (edgeVec e) w false hw42] at hw
      simp only [edgeVec, pairVec, decide_eq_true_eq] at hw
      rw [show runVF [] = initVF from rfl, initVF_getD_lt w hw42]
      simp only [Finset.mem_singleton]
      rcases hw with h | h
      · right; left; exact h.symm
      · right; right; exact h.symm
    · rw [wiresAux_nil, getD_of_ge _ _ _ (by rw [List.length_ofFn]; omega)] at hw
      cases hw
  | append_singleton gs g ih =>
    have hmono_pre : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have ih' := ih hmono_pre (hsafe_prefix hsafe)
    have hV_pre := runVF_getV_iff gs hmono_pre (hsafe_prefix hsafe)
    intro w e hinc hw
    rw [runVF_concat]
    rw [wiresAux_concat] at hw
    have hlen1 : (runVF gs).length = 42 + gs.length := runVF_length gs
    have hlen2 : (wiresAux gs (List.ofFn (edgeVec e))).length = 42 + gs.length := by
      rw [wiresAux_length, List.length_ofFn]
    by_cases hwlt : w < 42 + gs.length
    · rw [stepVF, getD_append_left _ _ w _ (by omega)]
      rw [stepWire, getD_append_left _ _ w _ (by omega)] at hw
      exact ih' w e hinc hw
    · by_cases hweq : w = 42 + gs.length
      · subst hweq
        rw [stepVF, getD_append_right _ _ _ _ (by omega), hlen1, Nat.sub_self, getD_singleton_zero]
        rw [stepWire, getD_append_right _ _ _ _ (by omega), hlen2, Nat.sub_self, getD_singleton_zero] at hw
        have hg_m := hmono g (List.mem_append_right _ (List.mem_singleton_self g))
        rcases hg_m.1 with hand | hor
        · have hgk : (gs ++ [g])[gs.length]? = some g := by
            rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl
          rw [hand] at hw
          simp only [stepVFEntry, hand]
          cases hin : g.inputs with
          | nil =>
            exfalso
            have hf := hsafe gs.length g hgk hand (fun _ => false) zeroVec_indep
            have hlen0 : (wiresAux gs (List.ofFn (fun _ : Fin 42 => false))).length = 42 + gs.length := by
              rw [wiresAux_length, List.length_ofFn]
            rw [wiresAux_concat, stepWire, getD_append_right _ _ _ _ (by omega), hlen0, Nat.sub_self,
                getD_singleton_zero, hand, hin] at hf
            simp [GateOp.eval] at hf
          | cons a rest =>
            cases rest with
            | nil =>
              rw [hin] at hw
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                Bool.and_true, id_eq] at hw
              have ha := ih' a e hinc hw
              have hno1 : e.1 ∉ ((runVF gs).getD a (∅, ∅)).1 := by
                intro hm1
                have ht1 := (hV_pre a e.1).mp hm1
                have hf := hsafe gs.length g hgk hand (singleVec e.1) (singleVec_indep e.1)
                have hlens : (wiresAux gs (List.ofFn (singleVec e.1))).length = 42 + gs.length := by
                  rw [wiresAux_length, List.length_ofFn]
                rw [wiresAux_concat, stepWire, getD_append_right _ _ _ _ (by omega), hlens, Nat.sub_self,
                    getD_singleton_zero, hand, hin] at hf
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  Bool.and_true, id_eq] at hf
                rw [ht1] at hf; cases hf
              have hno2 : e.2 ∉ ((runVF gs).getD a (∅, ∅)).1 := by
                intro hm2
                have ht2 := (hV_pre a e.2).mp hm2
                have hf := hsafe gs.length g hgk hand (singleVec e.2) (singleVec_indep e.2)
                have hlens : (wiresAux gs (List.ofFn (singleVec e.2))).length = 42 + gs.length := by
                  rw [wiresAux_length, List.length_ofFn]
                rw [wiresAux_concat, stepWire, getD_append_right _ _ _ _ (by omega), hlens, Nat.sub_self,
                    getD_singleton_zero, hand, hin] at hf
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  Bool.and_true, id_eq] at hf
                rw [ht2] at hf; cases hf
              rcases ha with h | h | h
              · left; exact h
              · exact absurd h hno1
              · exact absurd h hno2
            | cons b rest2 =>
              cases rest2 with
              | cons _ _ =>
                rw [hin] at hg_m; simp at hg_m
              | nil =>
                rw [hin] at hw
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  Bool.and_true, Bool.and_eq_true, id_eq] at hw
                have ha := ih' a e hinc hw.1
                have hb := ih' b e hinc hw.2
                have hbic := biclique_of_and gs g hmono hsafe hand a b hin
                left
                dsimp only
                split_ifs with hva hvb
                · rw [hva] at ha
                  rcases ha with h | h | h
                  · exact h
                  · simp at h
                  · simp at h
                · rw [hvb] at hb
                  rcases hb with h | h | h
                  · exact h
                  · simp at h
                  · simp at h
                · rcases ha with ha | ha1 | ha2
                  · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
                  · rcases hb with hb | hb1 | hb2
                    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb)
                    · exfalso
                      have := hbic e.1 ha1 e.1 hb1
                      rw [adj_irrefl] at this; cases this
                    · apply Finset.mem_union_right
                      simp only [prodEdges, Finset.mem_biUnion, Finset.mem_image]
                      exact ⟨e.1, ha1, e.2, hb2, mkEdge_eq_of_inc hinc⟩
                  · rcases hb with hb | hb1 | hb2
                    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb)
                    · apply Finset.mem_union_right
                      simp only [prodEdges, Finset.mem_biUnion, Finset.mem_image]
                      exact ⟨e.2, ha2, e.1, hb1, mkEdge_swap_of_inc hinc⟩
                    · exfalso
                      have := hbic e.2 ha2 e.2 hb2
                      rw [adj_irrefl] at this; cases this
        · rw [hor] at hw
          simp only [stepVFEntry, hor]
          cases hin : g.inputs with
          | nil =>
            rw [hin] at hw; simp [GateOp.eval] at hw
          | cons a rest =>
            cases rest with
            | nil =>
              rw [hin] at hw
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                Bool.or_false, id_eq] at hw
              exact ih' a e hinc hw
            | cons b rest2 =>
              cases rest2 with
              | cons _ _ =>
                rw [hin] at hg_m; simp at hg_m
              | nil =>
                rw [hin] at hw
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  Bool.or_false, Bool.or_eq_true, id_eq] at hw
                rcases hw with hwa | hwb
                · rcases ih' a e hinc hwa with h | h | h
                  · left; exact Finset.mem_union_left _ h
                  · right; left; exact Finset.mem_union_left _ h
                  · right; right; exact Finset.mem_union_left _ h
                · rcases ih' b e hinc hwb with h | h | h
                  · left; exact Finset.mem_union_right _ h
                  · right; left; exact Finset.mem_union_right _ h
                  · right; right; exact Finset.mem_union_right _ h
      · rw [stepWire, getD_of_ge _ _ _ (by rw [List.length_append, List.length_singleton, hlen2]; omega)] at hw
        cases hw

-- Biclique cardinality bound: |prodEdges va vb| <= 5

lemma biclique_card_le_five {va vb : Finset (Fin 42)}
    (hbic : ∀ u ∈ va, ∀ v ∈ vb, adj u v = true) :
    (prodEdges va vb).card ≤ 5 := by
  have hside : va.card ≤ 1 ∨ vb.card ≤ 1 := by
    by_contra h
    push Not at h
    obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp h.1
    obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp h.2
    exact c4_free hune hvne (hbic u1 hu1 v1 hv1) (hbic u1 hu1 v2 hv2)
      (hbic u2 hu2 v1 hv1) (hbic u2 hu2 v2 hv2)
  rcases hside with ha | hb
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha0 | ha1
    · rw [Finset.card_eq_zero.mp ha0]; simp [prodEdges]
    · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp ha1
      have hsub : vb ⊆ Finset.univ.filter (fun v : Fin 42 => adj u v = true) := by
        intro v hv
        simp [hbic u (Finset.mem_singleton_self u) v hv]
      calc (prodEdges {u} vb).card
          = (vb.image (mkEdge u)).card := by simp [prodEdges]
        _ ≤ vb.card := Finset.card_image_le
        _ ≤ (Finset.univ.filter (fun v : Fin 42 => adj u v = true)).card := Finset.card_le_card hsub
        _ ≤ 5 := deg_le_five u
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
    · rw [Finset.card_eq_zero.mp hb0]
      have hpe : prodEdges va ∅ = ∅ := by ext x; simp [prodEdges]
      rw [hpe]; simp
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hb1
      have hsub : va ⊆ Finset.univ.filter (fun u : Fin 42 => adj v u = true) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [adj_symm]
        exact hbic u hu v (Finset.mem_singleton_self v)
      have heq : prodEdges va {v} = va.image (fun u => mkEdge u v) := by
        ext x
        simp only [prodEdges, Finset.mem_biUnion, Finset.image_singleton, Finset.mem_singleton,
          Finset.mem_image]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
        · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
      calc (prodEdges va {v}).card
          = (va.image (fun u => mkEdge u v)).card := by rw [heq]
        _ ≤ va.card := Finset.card_image_le
        _ ≤ (Finset.univ.filter (fun u : Fin 42 => adj v u = true)).card := Finset.card_le_card hsub
        _ ≤ 5 := deg_le_five v

-- AND count lower bound (>= 21)

def allF (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) : Finset (Fin 42 × Fin 42) :=
  (Finset.range st.length).biUnion fun w => (st.getD w (∅, ∅)).2

lemma mem_allF_of_mem (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (w : ℕ)
    (e : Fin 42 × Fin 42) (he : e ∈ (st.getD w (∅, ∅)).2) : e ∈ allF st := by
  by_cases hw : w < st.length
  · simp only [allF, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨w, hw, he⟩
  · rw [getD_of_ge _ _ _ (by omega)] at he
    simp at he

lemma allF_append_subset (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (p : Finset (Fin 42) × Finset (Fin 42 × Fin 42)) :
    allF (st ++ [p]) ⊆ allF st ∪ p.2 := by
  intro e he
  simp only [allF, Finset.mem_biUnion, Finset.mem_range, List.length_append,
    List.length_singleton] at he
  obtain ⟨w, hw, hwe⟩ := he
  by_cases hlt : w < st.length
  · rw [getD_append_left _ _ w _ hlt] at hwe
    exact Finset.mem_union_left _ (mem_allF_of_mem st w e hwe)
  · have hweq : w = st.length := by omega
    subst hweq
    rw [getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, getD_singleton_zero] at hwe
    exact Finset.mem_union_right _ hwe

lemma card_allF_le (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsafe : ∀ k g, gs[k]? = some g → g.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux gs (List.ofFn x)).getD (42 + k) false = false) :
    (allF (runVF gs)).card ≤ 5 * (gs.countP (fun g => isAnd g.op)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    have hempty : allF (runVF []) = ∅ := by
      ext e
      simp only [allF, Finset.mem_biUnion, Finset.mem_range, Finset.notMem_empty,
        iff_false, not_exists, not_and]
      intro w hw
      rw [show runVF [] = initVF from rfl] at hw ⊢
      rw [initVF_length] at hw
      rw [initVF_getD_lt w hw]
      simp
    rw [hempty]
    simp
  | append_singleton gs g ih =>
    have hmono_pre : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have ih' := ih hmono_pre (hsafe_prefix hsafe)
    rw [runVF_concat, List.countP_append, List.countP_cons, List.countP_nil]
    have hg_m := hmono g (List.mem_append_right _ (List.mem_singleton_self g))
    rcases hg_m.1 with hand | hor
    · simp only [hand, isAnd, ↓reduceIte, Nat.zero_add]
      let extra : Finset (Fin 42 × Fin 42) :=
        match g.inputs with
        | [a, b] => prodEdges ((runVF gs).getD a (∅, ∅)).1 ((runVF gs).getD b (∅, ∅)).1
        | _ => ∅
      have hsub : allF (stepVF (runVF gs) g) ⊆ allF (runVF gs) ∪ extra := by
        refine Finset.Subset.trans (allF_append_subset (runVF gs) (stepVFEntry (runVF gs) g)) ?_
        intro e he
        rcases Finset.mem_union.mp he with h | h
        · exact Finset.mem_union_left _ h
        · simp only [stepVFEntry, hand] at h
          cases hin : g.inputs with
          | nil => rw [hin] at h; simp at h
          | cons a rest =>
            cases rest with
            | nil =>
              rw [hin] at h
              exact Finset.mem_union_left _ (mem_allF_of_mem _ a e h)
            | cons b rest2 =>
              cases rest2 with
              | cons _ _ => rw [hin] at h; simp at h
              | nil =>
                rw [hin] at h
                dsimp only at h
                split_ifs at h with hva hvb
                · exact Finset.mem_union_left _ (mem_allF_of_mem _ a e h)
                · exact Finset.mem_union_left _ (mem_allF_of_mem _ b e h)
                · rcases Finset.mem_union.mp h with hab | hp
                  · rcases Finset.mem_union.mp hab with ha | hb
                    · exact Finset.mem_union_left _ (mem_allF_of_mem _ a e ha)
                    · exact Finset.mem_union_left _ (mem_allF_of_mem _ b e hb)
                  · apply Finset.mem_union_right
                    simp only [extra, hin]
                    exact hp
      have hcard_extra : extra.card ≤ 5 := by
        dsimp only [extra]
        cases hin : g.inputs with
        | nil => simp
        | cons a rest =>
          cases rest with
          | nil => simp
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              exact biclique_card_le_five (biclique_of_and gs g hmono hsafe hand a b hin)
            | cons _ _ => simp
      calc (allF (stepVF (runVF gs) g)).card
          ≤ (allF (runVF gs) ∪ extra).card := Finset.card_le_card hsub
        _ ≤ (allF (runVF gs)).card + extra.card := Finset.card_union_le _ _
        _ ≤ 5 * gs.countP (fun g => isAnd g.op) + 5 := by omega
        _ = 5 * (gs.countP (fun g => isAnd g.op) + 1) := by omega
    · simp only [hor, isAnd, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hsub : allF (stepVF (runVF gs) g) ⊆ allF (runVF gs) := by
        refine Finset.Subset.trans (allF_append_subset (runVF gs) (stepVFEntry (runVF gs) g)) ?_
        intro e he
        rcases Finset.mem_union.mp he with h | h
        · exact h
        · simp only [stepVFEntry, hor] at h
          cases hin : g.inputs with
          | nil => rw [hin] at h; simp at h
          | cons a rest =>
            cases rest with
            | nil =>
              rw [hin] at h; exact mem_allF_of_mem _ a e h
            | cons b rest2 =>
              cases rest2 with
              | cons _ _ => rw [hin] at h; simp at h
              | nil =>
                rw [hin] at h
                rcases Finset.mem_union.mp h with ha | hb
                · exact mem_allF_of_mem _ a e ha
                · exact mem_allF_of_mem _ b e hb
      exact le_trans (Finset.card_le_card hsub) ih'

-- Golden Invariant for OR count lower bound (>= 104)

def Uof (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (W : Finset ℕ) :
    Finset (Fin 42) :=
  W.biUnion (fun w => if (st.getD w (∅, ∅)).1.card = 1 then (st.getD w (∅, ∅)).1 else ∅)

def Wne1 (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (W : Finset ℕ) :
    Finset ℕ :=
  W.filter (fun w => (st.getD w (∅, ∅)).1.card ≠ 1)

noncomputable def unionT (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (W : Finset ℕ) :
    Finset ((Fin 42 × Fin 42) ⊕ Fin 42) :=
  W.biUnion (fun w => Tof (st.getD w (∅, ∅)))

lemma qOf_eq (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (W : Finset ℕ) :
    qOf st W = (Wne1 st W).card + (Uof st W).card := rfl

lemma inr_mem_Tof_iff (p : Finset (Fin 42) × Finset (Fin 42 × Fin 42)) (u : Fin 42) :
    Sum.inr u ∈ Tof p ↔ p.1.card = 1 ∧ u ∈ p.1 := by
  simp only [Tof, Finset.mem_union, Finset.mem_image, reduceCtorEq, and_false, exists_false,
    false_or]
  split_ifs with h1 h2
  · simp [h1]
  · simp [h1]
  · simp [h1]

lemma inr_mem_unionT_iff (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (W : Finset ℕ) (u : Fin 42) :
    Sum.inr u ∈ unionT st W ↔ u ∈ Uof st W := by
  simp only [unionT, Uof, Finset.mem_biUnion, inr_mem_Tof_iff]
  constructor
  · rintro ⟨w, hw, h1, hu⟩
    refine ⟨w, hw, ?_⟩
    rw [if_pos h1]
    exact hu
  · rintro ⟨w, hw, hu⟩
    split_ifs at hu with h1
    · exact ⟨w, hw, h1, hu⟩
    · simp at hu

lemma edgeSetOf_eq_of_common {s : Finset (Fin 42)} (hs : 2 ≤ s.card) {u : Fin 42}
    (hu : ∀ v ∈ s, adj u v = true) :
    edgeSetOf s = s.image (fun v => mkEdge u v) := by
  have hex : ∃ u' : Fin 42, ∀ v ∈ s, adj u' v = true := ⟨u, hu⟩
  unfold edgeSetOf
  rw [dif_pos hex]
  have heq : Classical.choose hex = u := unique_common_nbr hs (Classical.choose_spec hex) hu
  rw [heq]

lemma qOf_insert_ne1 (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (W : Finset ℕ) (a : ℕ) (ha : (st.getD a (∅, ∅)).1.card ≠ 1) :
    qOf st (insert a W) ≤ qOf st W + 1 := by
  rw [qOf_eq, qOf_eq]
  have h1 : (Wne1 st (insert a W)).card ≤ (Wne1 st W).card + 1 := by
    have : Wne1 st (insert a W) ⊆ insert a (Wne1 st W) := by
      intro x hx
      simp only [Wne1, Finset.mem_filter, Finset.mem_insert] at hx ⊢
      rcases hx.1 with rfl | hxw
      · left; rfl
      · right; exact ⟨hxw, hx.2⟩
    exact le_trans (Finset.card_le_card this) (Finset.card_insert_le a _)
  have h2 : Uof st (insert a W) = Uof st W := by
    ext u
    simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro ⟨w, rfl | hw, hu⟩
      · rw [if_neg ha] at hu; simp at hu
      · exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      exact ⟨w, Or.inr hw, hu⟩
  rw [h2]
  omega

lemma qOf_insert_eq1_mem (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (W : Finset ℕ) (a : ℕ) (u : Fin 42) (ha : (st.getD a (∅, ∅)).1 = {u})
    (hu : u ∈ Uof st W) :
    qOf st (insert a W) = qOf st W := by
  rw [qOf_eq, qOf_eq]
  have hcard : (st.getD a (∅, ∅)).1.card = 1 := by rw [ha]; simp
  have h1 : Wne1 st (insert a W) = Wne1 st W := by
    ext x
    simp only [Wne1, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hne⟩
      · exact absurd hcard hne
      · exact ⟨hx, hne⟩
    · rintro ⟨hx, hne⟩
      exact ⟨Or.inr hx, hne⟩
  have h2 : Uof st (insert a W) = Uof st W := by
    ext x
    simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro ⟨w, rfl | hw, hx⟩
      · rw [if_pos hcard, ha, Finset.mem_singleton] at hx
        subst hx
        simpa [Uof, Finset.mem_biUnion] using hu
      · exact ⟨w, hw, hx⟩
    · rintro ⟨w, hw, hx⟩
      exact ⟨w, Or.inr hw, hx⟩
  rw [h1, h2]

lemma qOf_insert_eq1_le (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (W : Finset ℕ) (a : ℕ) (u : Fin 42) (ha : (st.getD a (∅, ∅)).1 = {u}) :
    qOf st (insert a W) ≤ qOf st W + 1 := by
  rw [qOf_eq, qOf_eq]
  have hcard : (st.getD a (∅, ∅)).1.card = 1 := by rw [ha]; simp
  have h1 : Wne1 st (insert a W) = Wne1 st W := by
    ext x
    simp only [Wne1, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hne⟩
      · exact absurd hcard hne
      · exact ⟨hx, hne⟩
    · rintro ⟨hx, hne⟩
      exact ⟨Or.inr hx, hne⟩
  have h2 : Uof st (insert a W) ⊆ insert u (Uof st W) := by
    intro x hx
    simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at hx ⊢
    rcases hx with ⟨w, rfl | hw, hxu⟩
    · rw [if_pos hcard, ha, Finset.mem_singleton] at hxu
      left; exact hxu
    · right; exact ⟨w, hw, hxu⟩
  rw [h1]
  have hc2 := le_trans (Finset.card_le_card h2) (Finset.card_insert_le u _)
  omega

lemma qOf_insert_not_mem_ne1 (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (W : Finset ℕ) (m : ℕ) (hm : m ∉ W) (hc : (st.getD m (∅, ∅)).1.card ≠ 1) :
    qOf st (insert m W) = qOf st W + 1 := by
  rw [qOf_eq, qOf_eq]
  have h1 : Wne1 st (insert m W) = insert m (Wne1 st W) := by
    ext x
    simp only [Wne1, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hne⟩
      · left; rfl
      · right; exact ⟨hx, hne⟩
    · rintro (rfl | ⟨hx, hne⟩)
      · exact ⟨Or.inl rfl, hc⟩
      · exact ⟨Or.inr hx, hne⟩
  have hm' : m ∉ Wne1 st W := by simp [Wne1, hm]
  have h2 : Uof st (insert m W) = Uof st W := by
    ext x
    simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro ⟨w, rfl | hw, hx⟩
      · rw [if_neg hc] at hx; simp at hx
      · exact ⟨w, hw, hx⟩
    · rintro ⟨w, hw, hx⟩
      exact ⟨w, Or.inr hw, hx⟩
  rw [h1, Finset.card_insert_of_notMem hm', h2]
  omega

lemma card_le_sub_one_of_mem {α : Type} [DecidableEq α] {A B : Finset α} {x : α}
    (hsub : A ⊆ B) (hxB : x ∈ B) (hxA : x ∉ A) : A.card + 1 ≤ B.card := by
  have : insert x A ⊆ B := Finset.insert_subset_iff.mpr ⟨hxB, hsub⟩
  have hc := Finset.card_le_card this
  rw [Finset.card_insert_of_notMem hxA] at hc
  exact hc

lemma card_le_sub_two_of_mem {α : Type} [DecidableEq α] {A B : Finset α} {x y : α}
    (hxy : x ≠ y) (hsub : A ⊆ B) (hxB : x ∈ B) (hyB : y ∈ B)
    (hxA : x ∉ A) (hyA : y ∉ A) : A.card + 2 ≤ B.card := by
  have : insert x (insert y A) ⊆ B :=
    Finset.insert_subset_iff.mpr ⟨hxB, Finset.insert_subset_iff.mpr ⟨hyB, hsub⟩⟩
  have hc := Finset.card_le_card this
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxA]),
      Finset.card_insert_of_notMem hyA] at hc
  exact hc

lemma unionT_congr_of_not_mem (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (g : Gate) (W : Finset ℕ) (hm : st.length ∉ W) :
    unionT (stepVF st g) W = unionT st W := by
  have hget : ∀ w ∈ W, (stepVF st g).getD w (∅, ∅) = st.getD w (∅, ∅) := by
    intro w hw
    have hne : w ≠ st.length := fun h => hm (h ▸ hw)
    by_cases hlt : w < st.length
    · exact getD_append_left st _ w (∅, ∅) hlt
    · rw [stepVF, getD_of_ge _ w _ (by simp; omega), getD_of_ge _ w _ (by omega)]
  ext z
  simp only [unionT, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hz⟩
    rw [hget w hw] at hz
    exact ⟨w, hw, hz⟩
  · rintro ⟨w, hw, hz⟩
    exact ⟨w, hw, by rw [hget w hw]; exact hz⟩

lemma Uof_congr_of_not_mem (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (g : Gate) (W : Finset ℕ) (hm : st.length ∉ W) :
    Uof (stepVF st g) W = Uof st W := by
  have hget : ∀ w ∈ W, (stepVF st g).getD w (∅, ∅) = st.getD w (∅, ∅) := by
    intro w hw
    have hne : w ≠ st.length := fun h => hm (h ▸ hw)
    by_cases hlt : w < st.length
    · exact getD_append_left st _ w (∅, ∅) hlt
    · rw [stepVF, getD_of_ge _ w _ (by simp; omega), getD_of_ge _ w _ (by omega)]
  ext u
  simp only [Uof, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hu⟩
    rw [hget w hw] at hu
    exact ⟨w, hw, hu⟩
  · rintro ⟨w, hw, hu⟩
    exact ⟨w, hw, by rw [hget w hw]; exact hu⟩

lemma qOf_congr_of_not_mem (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (g : Gate) (W : Finset ℕ) (hm : st.length ∉ W) :
    qOf (stepVF st g) W = qOf st W := by
  have hget : ∀ w ∈ W, (stepVF st g).getD w (∅, ∅) = st.getD w (∅, ∅) := by
    intro w hw
    have hne : w ≠ st.length := fun h => hm (h ▸ hw)
    by_cases hlt : w < st.length
    · exact getD_append_left st _ w (∅, ∅) hlt
    · rw [stepVF, getD_of_ge _ w _ (by simp; omega), getD_of_ge _ w _ (by omega)]
  rw [qOf_eq, qOf_eq, Uof_congr_of_not_mem st g W hm]
  congr 1
  congr 1
  ext w
  simp only [Wne1, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hne⟩
    rw [hget w hw] at hne
    exact ⟨hw, hne⟩
  · rintro ⟨hw, hne⟩
    exact ⟨hw, by rw [hget w hw]; exact hne⟩

lemma stepVF_getD_last (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42))) (g : Gate) :
    (stepVF st g).getD st.length (∅, ∅) = stepVFEntry st g := by
  rw [stepVF, getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, getD_singleton_zero]

lemma unionT_insert (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (a : ℕ) (W : Finset ℕ) :
    unionT st (insert a W) = Tof (st.getD a (∅, ∅)) ∪ unionT st W :=
  Finset.biUnion_insert ..

lemma inl_mem_Tof {p : Finset (Fin 42) × Finset (Fin 42 × Fin 42)} {e : Fin 42 × Fin 42}
    (he : e ∈ p.2) : Sum.inl e ∈ Tof p :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem Sum.inl he)

lemma inl_mem_Tof_of_edgeSetOf {p : Finset (Fin 42) × Finset (Fin 42 × Fin 42)}
    (hp : 2 ≤ p.1.card) {e : Fin 42 × Fin 42} (he : e ∈ edgeSetOf p.1) :
    Sum.inl e ∈ Tof p := by
  rw [Tof, if_neg (by omega), if_pos hp]
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem Sum.inl he)

lemma Tof_empty : Tof (∅, ∅) = ∅ := by
  simp [Tof]

lemma Tof_union_card_one (va vb : Finset (Fin 42)) (fa fb : Finset (Fin 42 × Fin 42))
    (u : Fin 42) (huv : va ∪ vb = {u}) :
    Tof (va ∪ vb, fa ∪ fb) = Tof (va, fa) ∪ Tof (vb, fb) := by
  have hva : va = ∅ ∨ va = {u} := Finset.subset_singleton_iff.mp (by rw [← huv]; exact Finset.subset_union_left)
  have hvb : vb = ∅ ∨ vb = {u} := Finset.subset_singleton_iff.mp (by rw [← huv]; exact Finset.subset_union_right)
  have hne : ¬ (va = ∅ ∧ vb = ∅) := by
    rintro ⟨h1, h2⟩; rw [h1, h2, Finset.empty_union] at huv; exact Finset.singleton_ne_empty u huv.symm
  have hT0 : ∀ (f : Finset (Fin 42 × Fin 42)), Tof (∅, f) = f.image Sum.inl := by
    intro f; simp [Tof]
  have hT1 : ∀ (f : Finset (Fin 42 × Fin 42)), Tof ({u}, f) = f.image Sum.inl ∪ {Sum.inr u} := by
    intro f; simp [Tof]
  rw [huv, hT1]
  rcases hva with rfl | rfl <;> rcases hvb with rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ hne
  · rw [hT0, hT1, Finset.image_union, Finset.union_assoc]
  · rw [hT1, hT0, Finset.image_union, Finset.union_right_comm]
  · rw [hT1, hT1, Finset.image_union, Finset.union_union_union_comm, Finset.union_idempotent]

lemma golden_and_1_ge2 (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (r : ℕ) (ih : ∀ W : Finset ℕ, (unionT st W).card ≤ r + qOf st W)
    (W' : Finset ℕ) (x y : ℕ)
    (hx1 : (st.getD x (∅, ∅)).1.card = 1) (hy2 : 2 ≤ (st.getD y (∅, ∅)).1.card)
    (hxy : ∀ u ∈ (st.getD x (∅, ∅)).1, ∀ v ∈ (st.getD y (∅, ∅)).1, adj u v = true) :
    (((st.getD x (∅, ∅)).2 ∪ (st.getD y (∅, ∅)).2 ∪
      prodEdges (st.getD x (∅, ∅)).1 (st.getD y (∅, ∅)).1).image Sum.inl ∪
      unionT st W').card ≤ r + qOf st W' + 1 := by
  obtain ⟨u, hxu⟩ := Finset.card_eq_one.mp hx1
  have hprod_eq : prodEdges (st.getD x (∅, ∅)).1 (st.getD y (∅, ∅)).1 =
      edgeSetOf (st.getD y (∅, ∅)).1 := by
    rw [hxu, edgeSetOf_eq_of_common hy2 (fun v hv => hxy u (by rw [hxu]; simp) v hv)]
    simp [prodEdges]
  have hy_ne1 : (st.getD y (∅, ∅)).1.card ≠ 1 := by omega
  have hsub : (((st.getD x (∅, ∅)).2 ∪ (st.getD y (∅, ∅)).2 ∪
      prodEdges (st.getD x (∅, ∅)).1 (st.getD y (∅, ∅)).1).image Sum.inl ∪
      unionT st W') ⊆ unionT st (insert x (insert y W')) := by
    intro z hz
    rw [unionT_insert, unionT_insert]
    rcases Finset.mem_union.mp hz with hl | hr
    · rw [Finset.mem_image] at hl
      obtain ⟨e, he, rfl⟩ := hl
      rcases Finset.mem_union.mp he with he1 | hep
      · rcases Finset.mem_union.mp he1 with hex | hey
        · exact Finset.mem_union_left _ (inl_mem_Tof hex)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof hey))
      · rw [hprod_eq] at hep
        exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof_of_edgeSetOf hy2 hep))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
  by_cases huW : u ∈ Uof st W'
  · have hqy := qOf_insert_ne1 st W' y hy_ne1
    have hqx : qOf st (insert x (insert y W')) = qOf st (insert y W') := by
      apply qOf_insert_eq1_mem st (insert y W') x u hxu
      have : Uof st (insert y W') = Uof st W' := by
        ext v; simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
        constructor
        · rintro ⟨w, rfl | hw, hv⟩
          · rw [if_neg hy_ne1] at hv; simp at hv
          · exact ⟨w, hw, hv⟩
        · rintro ⟨w, hw, hv⟩; exact ⟨w, Or.inr hw, hv⟩
      rw [this]; exact huW
    have := ih (insert x (insert y W'))
    have := Finset.card_le_card hsub
    omega
  · have hnot_mem : Sum.inr u ∉ (((st.getD x (∅, ∅)).2 ∪ (st.getD y (∅, ∅)).2 ∪
        prodEdges (st.getD x (∅, ∅)).1 (st.getD y (∅, ∅)).1).image Sum.inl ∪
        unionT st W') := by
      simp only [Finset.mem_union, Finset.mem_image, reduceCtorEq, and_false,
        exists_false, false_or, inr_mem_unionT_iff]
      exact huW
    have hmem : Sum.inr u ∈ unionT st (insert x (insert y W')) := by
      rw [unionT_insert]
      apply Finset.mem_union_left
      rw [inr_mem_Tof_iff]
      exact ⟨hx1, by rw [hxu]; simp⟩
    have hc1 := card_le_sub_one_of_mem hsub hmem hnot_mem
    have hqx := qOf_insert_eq1_le st (insert y W') x u hxu
    have hqy := qOf_insert_ne1 st W' y hy_ne1
    have := ih (insert x (insert y W'))
    omega

lemma golden_step_and (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (r : ℕ) (ih : ∀ W : Finset ℕ, (unionT st W).card ≤ r + qOf st W)
    (g : Gate) (hand : g.op = GateOp.and) (hlen : g.inputs.length ≤ 2)
    (hbic : ∀ a b, g.inputs = [a, b] →
      ∀ u ∈ (st.getD a (∅, ∅)).1, ∀ v ∈ (st.getD b (∅, ∅)).1, adj u v = true) :
    ∀ W : Finset ℕ, (unionT (stepVF st g) W).card ≤ r + qOf (stepVF st g) W := by
  intro W
  set m := st.length
  set st' := stepVF st g
  have hnew_V : (st'.getD m (∅, ∅)).1 = ∅ := by
    rw [stepVF_getD_last]
    simp only [stepVFEntry, hand]
    cases hin : g.inputs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest2 =>
        cases rest2 with
        | nil => dsimp only; split_ifs <;> rfl
        | cons _ _ => rfl
  by_cases hmW : m ∉ W
  · rw [unionT_congr_of_not_mem st g W hmW, qOf_congr_of_not_mem st g W hmW]
    exact ih W
  · push Not at hmW
    set W' := W.erase m
    have hmW' : m ∉ W' := Finset.notMem_erase m W
    have hW_eq : W = insert m W' := (Finset.insert_erase hmW).symm
    have hqW : qOf st' W = qOf st W' + 1 := by
      rw [hW_eq, qOf_insert_not_mem_ne1 st' W' m hmW' (by rw [hnew_V]; simp),
          qOf_congr_of_not_mem st g W' hmW']
    have huW : unionT st' W = Tof (st'.getD m (∅, ∅)) ∪ unionT st W' := by
      rw [hW_eq, unionT_insert, unionT_congr_of_not_mem st g W' hmW']
    rw [hqW, huW]
    have hTm : Tof (st'.getD m (∅, ∅)) = (st'.getD m (∅, ∅)).2.image Sum.inl := by
      rw [Tof, hnew_V]; simp
    rw [hTm, stepVF_getD_last]
    simp only [stepVFEntry, hand]
    cases hin : g.inputs with
    | nil =>
      simp only [Finset.image_empty, Finset.empty_union]
      have := ih W'; omega
    | cons a rest =>
      cases rest with
      | nil =>
        dsimp only
        have hsub : (st.getD a (∅, ∅)).2.image Sum.inl ∪ unionT st W' ⊆
            unionT st (insert a W') := by
          rw [unionT_insert]
          exact Finset.union_subset_union_left (fun z hz => by
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz; exact inl_mem_Tof he)
        have hqa : qOf st (insert a W') ≤ qOf st W' + 1 := by
          by_cases h1 : (st.getD a (∅, ∅)).1.card = 1
          · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
            exact qOf_insert_eq1_le st W' a u hu
          · exact qOf_insert_ne1 st W' a h1
        have := ih (insert a W')
        have := Finset.card_le_card hsub
        omega
      | cons b rest2 =>
        cases rest2 with
        | cons _ _ => rw [hin] at hlen; simp at hlen
        | nil =>
          dsimp only
          split_ifs with hva hvb
          · dsimp only
            have hsub : (st.getD a (∅, ∅)).2.image Sum.inl ∪ unionT st W' ⊆
                unionT st (insert a W') := by
              rw [unionT_insert]
              exact Finset.union_subset_union_left (fun z hz => by
                obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz; exact inl_mem_Tof he)
            have hqa := qOf_insert_ne1 st W' a (by rw [hva]; simp)
            have := ih (insert a W'); have := Finset.card_le_card hsub; omega
          · dsimp only
            have hsub : (st.getD b (∅, ∅)).2.image Sum.inl ∪ unionT st W' ⊆
                unionT st (insert b W') := by
              rw [unionT_insert]
              exact Finset.union_subset_union_left (fun z hz => by
                obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz; exact inl_mem_Tof he)
            have hqb := qOf_insert_ne1 st W' b (by rw [hvb]; simp)
            have := ih (insert b W'); have := Finset.card_le_card hsub; omega
          · dsimp only
            have hbic' := hbic a b hin
            set va := (st.getD a (∅, ∅)).1
            set vb := (st.getD b (∅, ∅)).1
            set fa := (st.getD a (∅, ∅)).2
            set fb := (st.getD b (∅, ∅)).2
            have hva_pos : 1 ≤ va.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hva)
            have hvb_pos : 1 ≤ vb.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hvb)
            have hside : va.card = 1 ∨ vb.card = 1 := by
              by_contra h
              push Not at h
              obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp (by omega : 1 < va.card)
              obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp (by omega : 1 < vb.card)
              exact c4_free hune hvne (hbic' u1 hu1 v1 hv1) (hbic' u1 hu1 v2 hv2)
                (hbic' u2 hu2 v1 hv1) (hbic' u2 hu2 v2 hv2)
            by_cases ha1 : va.card = 1
            · by_cases hb1 : vb.card = 1
              · obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
                obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp hb1
                have hadj_uv : adj u v = true :=
                  hbic' u (by rw [hau]; simp) v (by rw [hbv]; simp)
                have huv : u ≠ v := by
                  intro heq; subst heq; rw [adj_irrefl] at hadj_uv; cases hadj_uv
                have hprod_sing : prodEdges va vb = {mkEdge u v} := by
                  rw [hau, hbv]; ext e; simp [prodEdges]
                set e0 := mkEdge u v
                set LHS := ((fa ∪ fb ∪ prodEdges va vb).image Sum.inl ∪ unionT st W')
                set LHS0 := ((fa ∪ fb).image Sum.inl ∪ unionT st W')
                have hLHS_sub : LHS ⊆ insert (Sum.inl e0) LHS0 := by
                  intro z hz
                  rcases Finset.mem_union.mp hz with hl | hr
                  · rw [Finset.mem_image] at hl
                    obtain ⟨e, he, rfl⟩ := hl
                    rcases Finset.mem_union.mp he with he1 | hep
                    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he1))
                    · rw [hprod_sing, Finset.mem_singleton] at hep
                      rw [hep]; exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)
                have hcard_step : LHS.card ≤ LHS0.card + 1 :=
                  le_trans (Finset.card_le_card hLHS_sub) (Finset.card_insert_le _ _)
                have hLHS0_sub : LHS0 ⊆ unionT st (insert a (insert b W')) := by
                  intro z hz
                  rw [unionT_insert, unionT_insert]
                  rcases Finset.mem_union.mp hz with hl | hr
                  · rw [Finset.mem_image] at hl
                    obtain ⟨e, he, rfl⟩ := hl
                    rcases Finset.mem_union.mp he with hea | heb
                    · exact Finset.mem_union_left _ (inl_mem_Tof hea)
                    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof heb))
                  · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
                have hmem_u : Sum.inr u ∈ unionT st (insert a (insert b W')) := by
                  rw [unionT_insert]
                  exact Finset.mem_union_left _ ((inr_mem_Tof_iff _ u).mpr ⟨ha1, show u ∈ va by rw [hau]; simp⟩)
                have hmem_v : Sum.inr v ∈ unionT st (insert a (insert b W')) := by
                  rw [unionT_insert, unionT_insert]
                  exact Finset.mem_union_right _
                    (Finset.mem_union_left _ ((inr_mem_Tof_iff _ v).mpr ⟨hb1, show v ∈ vb by rw [hbv]; simp⟩))
                have hIH := ih (insert a (insert b W'))
                by_cases huW : u ∈ Uof st W' <;> by_cases hvW : v ∈ Uof st W'
                · have hqb := qOf_insert_eq1_mem st W' b v hbv hvW
                  have hqa : qOf st (insert a (insert b W')) = qOf st (insert b W') := by
                    apply qOf_insert_eq1_mem st (insert b W') a u hau
                    simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at huW ⊢
                    obtain ⟨w, hw, hu⟩ := huW; exact ⟨w, Or.inr hw, hu⟩
                  have := Finset.card_le_card hLHS0_sub
                  omega
                · have hqb := qOf_insert_eq1_le st W' b v hbv
                  have hqa : qOf st (insert a (insert b W')) = qOf st (insert b W') := by
                    apply qOf_insert_eq1_mem st (insert b W') a u hau
                    simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at huW ⊢
                    obtain ⟨w, hw, hu⟩ := huW; exact ⟨w, Or.inr hw, hu⟩
                  have hnot_v : Sum.inr v ∉ LHS0 := by
                    simp [LHS0, inr_mem_unionT_iff, hvW]
                  have := card_le_sub_one_of_mem hLHS0_sub hmem_v hnot_v
                  omega
                · have hqb := qOf_insert_eq1_mem st W' b v hbv hvW
                  have hqa := qOf_insert_eq1_le st (insert b W') a u hau
                  have hnot_u : Sum.inr u ∉ LHS0 := by
                    simp [LHS0, inr_mem_unionT_iff, huW]
                  have := card_le_sub_one_of_mem hLHS0_sub hmem_u hnot_u
                  omega
                · have hqb := qOf_insert_eq1_le st W' b v hbv
                  have hqa := qOf_insert_eq1_le st (insert b W') a u hau
                  have hnot_u : Sum.inr u ∉ LHS0 := by
                    simp [LHS0, inr_mem_unionT_iff, huW]
                  have hnot_v : Sum.inr v ∉ LHS0 := by
                    simp [LHS0, inr_mem_unionT_iff, hvW]
                  have := card_le_sub_two_of_mem (by intro h; exact huv (Sum.inr.inj h))
                    hLHS0_sub hmem_u hmem_v hnot_u hnot_v
                  omega
              · exact golden_and_1_ge2 st r ih W' a b ha1 (show 2 ≤ vb.card by omega) hbic'
            · have hb1 : vb.card = 1 := by rcases hside with h | h; exact absurd h ha1; exact h
              have hcomm : (fa ∪ fb ∪ prodEdges va vb) = (fb ∪ fa ∪ prodEdges vb va) := by
                ext e
                simp only [Finset.mem_union, prodEdges, Finset.mem_biUnion, Finset.mem_image]
                constructor
                · rintro ((h | h) | ⟨u, hu, v, hv, rfl⟩)
                  · left; right; exact h
                  · left; left; exact h
                  · right; exact ⟨v, hv, u, hu, (mkEdge_symm (hbic' u hu v hv)).symm⟩
                · rintro ((h | h) | ⟨v, hv, u, hu, rfl⟩)
                  · left; right; exact h
                  · left; left; exact h
                  · right; exact ⟨u, hu, v, hv, mkEdge_symm (hbic' u hu v hv)⟩
              rw [hcomm]
              exact golden_and_1_ge2 st r ih W' b a hb1 (show 2 ≤ va.card by omega)
                (fun v hv u hu => by rw [adj_symm]; exact hbic' u hu v hv)

lemma golden_step_or (st : List (Finset (Fin 42) × Finset (Fin 42 × Fin 42)))
    (r : ℕ) (ih : ∀ W : Finset ℕ, (unionT st W).card ≤ r + qOf st W)
    (g : Gate) (hor : g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, (unionT (stepVF st g) W).card ≤ (r + 1) + qOf (stepVF st g) W := by
  intro W
  set m := st.length
  set st' := stepVF st g
  by_cases hmW : m ∉ W
  · rw [unionT_congr_of_not_mem st g W hmW, qOf_congr_of_not_mem st g W hmW]
    have := ih W; omega
  · push Not at hmW
    set W' := W.erase m
    have hmW' : m ∉ W' := Finset.notMem_erase m W
    have hW_eq : W = insert m W' := (Finset.insert_erase hmW).symm
    have hq' : qOf st' W' = qOf st W' := qOf_congr_of_not_mem st g W' hmW'
    have hU' : Uof st' W' = Uof st W' := Uof_congr_of_not_mem st g W' hmW'
    have huW : unionT st' W = Tof (st'.getD m (∅, ∅)) ∪ unionT st W' := by
      rw [hW_eq, unionT, Finset.biUnion_insert, ← unionT, unionT_congr_of_not_mem st g W' hmW']
    have hnew : st'.getD m (∅, ∅) =
        (match g.inputs with
         | [] => (∅, ∅)
         | [a] => st.getD a (∅, ∅)
         | [a, b] => ((st.getD a (∅, ∅)).1 ∪ (st.getD b (∅, ∅)).1,
                      (st.getD a (∅, ∅)).2 ∪ (st.getD b (∅, ∅)).2)
         | _ => (∅, ∅)) := by
      rw [stepVF_getD_last]
      simp only [stepVFEntry, hor]
      cases hin : g.inputs with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b rest2 =>
          cases rest2 with
          | nil => rfl
          | cons _ _ => rfl
    rw [huW]
    cases hin : g.inputs with
    | nil =>
      rw [hin] at hnew; dsimp only at hnew
      have hqW : qOf st' W = qOf st W' + 1 := by
        rw [hW_eq, qOf_insert_not_mem_ne1 st' W' m hmW' (by rw [hnew]; simp), hq']
      rw [hnew, hqW, Tof_empty, Finset.empty_union]
      have := ih W'; omega
    | cons a rest =>
      cases rest with
      | nil =>
        rw [hin] at hnew; dsimp only at hnew
        have hsub : Tof (st'.getD m (∅, ∅)) ∪ unionT st W' = unionT st (insert a W') := by
          rw [hnew, unionT_insert]
        rw [hsub]
        have hq_cmp : qOf st (insert a W') ≤ qOf st' W := by
          by_cases ha1 : (st.getD a (∅, ∅)).1.card = 1
          · obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
            have hm_eq : (st'.getD m (∅, ∅)).1 = {u} := by rw [hnew]; exact hau
            by_cases huW : u ∈ Uof st W'
            · rw [qOf_insert_eq1_mem st W' a u hau huW]
              rw [hW_eq, qOf_insert_eq1_mem st' W' m u hm_eq (by rw [hU']; exact huW), hq']
            · have hle := qOf_insert_eq1_le st W' a u hau
              have hWne : Wne1 st' (insert m W') = Wne1 st' W' := by
                ext x; simp only [Wne1, Finset.mem_filter, Finset.mem_insert]
                constructor
                · rintro ⟨rfl | hx, hne⟩
                  · exact absurd (by rw [hm_eq]; simp) hne
                  · exact ⟨hx, hne⟩
                · rintro ⟨hx, hne⟩; exact ⟨Or.inr hx, hne⟩
              have hUm : Uof st' (insert m W') = insert u (Uof st' W') := by
                ext x; simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
                constructor
                · rintro ⟨w, rfl | hw, hx⟩
                  · rw [if_pos (by rw [hm_eq]; simp), hm_eq, Finset.mem_singleton] at hx
                    left; exact hx
                  · right; exact ⟨w, hw, hx⟩
                · rintro (rfl | ⟨w, hw, hx⟩)
                  · refine ⟨m, Or.inl rfl, ?_⟩
                    rw [if_pos (by rw [hm_eq]; simp), hm_eq]; simp
                  · exact ⟨w, Or.inr hw, hx⟩
              have hqW : qOf st' W = qOf st W' + 1 := by
                rw [hW_eq, qOf_eq, qOf_eq, hWne, hUm, Finset.card_insert_of_notMem (by rw [hU']; exact huW), hU']
                have := hq'
                rw [qOf_eq, qOf_eq, hU'] at this
                omega
              omega
          · have hqW : qOf st' W = qOf st W' + 1 := by
              rw [hW_eq, qOf_insert_not_mem_ne1 st' W' m hmW' (by rw [hnew]; exact ha1), hq']
            rw [hqW]
            exact qOf_insert_ne1 st W' a ha1
        have := ih (insert a W')
        omega
      | cons b rest2 =>
        cases rest2 with
        | cons _ _ => rw [hin] at hlen; simp at hlen
        | nil =>
          rw [hin] at hnew; dsimp only at hnew
          set va := (st.getD a (∅, ∅)).1
          set vb := (st.getD b (∅, ∅)).1
          set fa := (st.getD a (∅, ∅)).2
          set fb := (st.getD b (∅, ∅)).2
          by_cases hvo1 : (va ∪ vb).card = 1
          · obtain ⟨u, huv⟩ := Finset.card_eq_one.mp hvo1
            have hva_sub : va ⊆ {u} := by rw [← huv]; exact Finset.subset_union_left
            have hvb_sub : vb ⊆ {u} := by rw [← huv]; exact Finset.subset_union_right
            have hTo_eq : Tof (st'.getD m (∅, ∅)) =
                Tof (st.getD a (∅, ∅)) ∪ Tof (st.getD b (∅, ∅)) := by
              rw [hnew]
              exact Tof_union_card_one va vb fa fb u huv
            have hsub : Tof (st'.getD m (∅, ∅)) ∪ unionT st W' =
                unionT st (insert a (insert b W')) := by
              rw [hTo_eq, unionT_insert, unionT_insert, Finset.union_assoc]
            rw [hsub]
            have hm_eq : (st'.getD m (∅, ∅)).1 = {u} := by rw [hnew]; exact huv
            have hqW_eq : qOf st' W = qOf st W' + if u ∈ Uof st W' then 0 else 1 := by
              by_cases huW : u ∈ Uof st W'
              · rw [if_pos huW, Nat.add_zero, hW_eq,
                    qOf_insert_eq1_mem st' W' m u hm_eq (by rw [hU']; exact huW), hq']
              · rw [if_neg huW]
                have hWne : Wne1 st' (insert m W') = Wne1 st' W' := by
                  ext x; simp only [Wne1, Finset.mem_filter, Finset.mem_insert]
                  constructor
                  · rintro ⟨rfl | hx, hne⟩
                    · exact absurd (by rw [hm_eq]; simp) hne
                    · exact ⟨hx, hne⟩
                  · rintro ⟨hx, hne⟩; exact ⟨Or.inr hx, hne⟩
                have hUm : Uof st' (insert m W') = insert u (Uof st' W') := by
                  ext x; simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
                  constructor
                  · rintro ⟨w, rfl | hw, hx⟩
                    · rw [if_pos (by rw [hm_eq]; simp), hm_eq, Finset.mem_singleton] at hx
                      left; exact hx
                    · right; exact ⟨w, hw, hx⟩
                  · rintro (rfl | ⟨w, hw, hx⟩)
                    · refine ⟨m, Or.inl rfl, ?_⟩
                      rw [if_pos (by rw [hm_eq]; simp), hm_eq]; simp
                    · exact ⟨w, Or.inr hw, hx⟩
                rw [hW_eq, qOf_eq, qOf_eq, hWne, hUm, Finset.card_insert_of_notMem (by rw [hU']; exact huW), hU']
                have := hq'; rw [qOf_eq, qOf_eq, hU'] at this; omega
            have hqab : qOf st (insert a (insert b W')) ≤
                qOf st W' + (if u ∈ Uof st W' then 0 else 1) + 1 := by
              have hcases : (va = {u} ∨ va = ∅) ∧ (vb = {u} ∨ vb = ∅) :=
                ⟨(Finset.subset_singleton_iff.mp hva_sub).symm,
                 (Finset.subset_singleton_iff.mp hvb_sub).symm⟩
              rcases hcases.1 with ha_u | ha_0 <;> rcases hcases.2 with hb_u | hb_0
              · have hu_in_b : u ∈ Uof st (insert b W') := by
                  simp only [Uof, Finset.mem_biUnion, Finset.mem_insert]
                  refine ⟨b, Or.inl rfl, ?_⟩
                  have hbc : (st.getD b (∅, ∅)).1 = {u} := hb_u
                  rw [hbc]; simp
                by_cases huW : u ∈ Uof st W'
                · rw [if_pos huW, qOf_insert_eq1_mem st (insert b W') a u ha_u hu_in_b,
                      qOf_insert_eq1_mem st W' b u hb_u huW]
                  omega
                · rw [if_neg huW, qOf_insert_eq1_mem st (insert b W') a u ha_u hu_in_b]
                  have := qOf_insert_eq1_le st W' b u hb_u; omega
              · have hqb := qOf_insert_ne1 st W' b (show vb.card ≠ 1 by rw [hb_0]; simp)
                by_cases huW : u ∈ Uof st W'
                · rw [if_pos huW, qOf_insert_eq1_mem st (insert b W') a u ha_u
                      (by simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at huW ⊢;
                          obtain ⟨w, hw, hwu⟩ := huW; exact ⟨w, Or.inr hw, hwu⟩)]
                  omega
                · rw [if_neg huW]
                  have := qOf_insert_eq1_le st (insert b W') a u ha_u; omega
              · have hqa := qOf_insert_ne1 st (insert b W') a (show va.card ≠ 1 by rw [ha_0]; simp)
                by_cases huW : u ∈ Uof st W'
                · rw [if_pos huW]
                  rw [qOf_insert_eq1_mem st W' b u hb_u huW] at hqa
                  omega
                · rw [if_neg huW]
                  have := qOf_insert_eq1_le st W' b u hb_u; omega
              · exfalso; rw [ha_0, hb_0] at huv; simp at huv
            have := ih (insert a (insert b W'))
            rw [hqW_eq]
            omega
          · have hqW : qOf st' W = qOf st W' + 1 := by
              rw [hW_eq, qOf_insert_not_mem_ne1 st' W' m hmW' (by rw [hnew]; exact hvo1), hq']
            rw [hqW]
            by_cases hvo0 : (va ∪ vb).card = 0
            · have hva0 : va = ∅ := (Finset.union_eq_empty.mp (Finset.card_eq_zero.mp hvo0)).1
              have hvb0 : vb = ∅ := (Finset.union_eq_empty.mp (Finset.card_eq_zero.mp hvo0)).2
              have hsub : Tof (st'.getD m (∅, ∅)) ∪ unionT st W' ⊆
                  unionT st (insert a (insert b W')) := by
                rw [unionT_insert, unionT_insert]
                intro z hz
                rcases Finset.mem_union.mp hz with hl | hr
                · have hTm0 : Tof (st'.getD m (∅, ∅)) = (fa ∪ fb).image Sum.inl := by
                    rw [hnew, hva0, hvb0, Finset.empty_union]; simp [Tof]
                  rw [hTm0, Finset.mem_image] at hl
                  obtain ⟨e, he, rfl⟩ := hl
                  rcases Finset.mem_union.mp he with ha | hb
                  · exact Finset.mem_union_left _ (inl_mem_Tof ha)
                  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof hb))
                · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
              have hqb := qOf_insert_ne1 st W' b (show vb.card ≠ 1 by rw [hvb0]; simp)
              have hqa := qOf_insert_ne1 st (insert b W') a (show va.card ≠ 1 by rw [hva0]; simp)
              have := ih (insert a (insert b W'))
              have := Finset.card_le_card hsub
              omega
            · have hvo2 : 2 ≤ (va ∪ vb).card := by omega
              by_cases hcn : ∃ u : Fin 42, ∀ v ∈ va ∪ vb, adj u v = true
              · obtain ⟨ustar, hustar⟩ := hcn
                have hedge_o : edgeSetOf (va ∪ vb) =
                    (va.image (mkEdge ustar)) ∪ (vb.image (mkEdge ustar)) := by
                  rw [edgeSetOf_eq_of_common hvo2 hustar, Finset.image_union]
                have hTm : Tof (st'.getD m (∅, ∅)) =
                    (fa ∪ fb ∪ va.image (mkEdge ustar) ∪ vb.image (mkEdge ustar)).image Sum.inl := by
                  simp only [hnew, Tof, va, vb, fa, fb, hvo1, ↓reduceIte, hvo2, hedge_o,
                    Finset.image_union, Finset.union_assoc]
                rw [hTm]
                have hside_ne1 : ∀ (x : ℕ), (st.getD x (∅, ∅)).1 ⊆ va ∪ vb →
                    (st.getD x (∅, ∅)).1.card ≠ 1 →
                    ((st.getD x (∅, ∅)).1.image (mkEdge ustar)).image Sum.inl ⊆
                      Tof (st.getD x (∅, ∅)) := by
                  intro x hxsub hxne1
                  by_cases hx0 : (st.getD x (∅, ∅)).1.card = 0
                  · rw [Finset.card_eq_zero.mp hx0]; simp
                  · have hx2 : 2 ≤ (st.getD x (∅, ∅)).1.card := by omega
                    have heq := edgeSetOf_eq_of_common hx2 (fun v hv => hustar v (hxsub hv))
                    intro z hz
                    rw [Finset.mem_image] at hz
                    obtain ⟨e, he, rfl⟩ := hz
                    rw [← heq] at he
                    exact inl_mem_Tof_of_edgeSetOf hx2 he
                by_cases ha1 : va.card = 1 <;> by_cases hb1 : vb.card = 1
                · obtain ⟨v1, hav1⟩ := Finset.card_eq_one.mp ha1
                  obtain ⟨v2, hbv2⟩ := Finset.card_eq_one.mp hb1
                  have hv12 : v1 ≠ v2 := by
                    intro heq; subst heq
                    rw [hav1, hbv2, Finset.union_idempotent, Finset.card_singleton] at hvo2
                    omega
                  set e1 := mkEdge ustar v1
                  set e2 := mkEdge ustar v2
                  set LHS := ((fa ∪ fb ∪ va.image (mkEdge ustar) ∪ vb.image (mkEdge ustar)).image Sum.inl ∪ unionT st W')
                  set LHS0 := ((fa ∪ fb).image Sum.inl ∪ unionT st W')
                  have hLHS_sub : LHS ⊆ insert (Sum.inl e1) (insert (Sum.inl e2) LHS0) := by
                    intro z hz
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with he1 | heb
                      · rcases Finset.mem_union.mp he1 with he0 | hea
                        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                            (Finset.mem_union_left _ (Finset.mem_image_of_mem _ he0)))
                        · rw [hav1, Finset.image_singleton, Finset.mem_singleton] at hea
                          rw [hea]; exact Finset.mem_insert_self _ _
                      · rw [hbv2, Finset.image_singleton, Finset.mem_singleton] at heb
                        rw [heb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                        (Finset.mem_union_right _ hr))
                  have hstep : LHS.card ≤ LHS0.card + 2 :=
                    le_trans (Finset.card_le_card hLHS_sub)
                      (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right (Finset.card_insert_le _ _) 1))
                  have hLHS0_sub : LHS0 ⊆ unionT st (insert a (insert b W')) := by
                    intro z hz
                    rw [unionT_insert, unionT_insert]
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with hea | heb
                      · exact Finset.mem_union_left _ (inl_mem_Tof hea)
                      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof heb))
                    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
                  have hmem_v1 : Sum.inr v1 ∈ unionT st (insert a (insert b W')) := by
                    rw [unionT_insert]
                    exact Finset.mem_union_left _ ((inr_mem_Tof_iff _ v1).mpr ⟨ha1, show v1 ∈ va by rw [hav1]; simp⟩)
                  have hmem_v2 : Sum.inr v2 ∈ unionT st (insert a (insert b W')) := by
                    rw [unionT_insert, unionT_insert]
                    exact Finset.mem_union_right _
                      (Finset.mem_union_left _ ((inr_mem_Tof_iff _ v2).mpr ⟨hb1, show v2 ∈ vb by rw [hbv2]; simp⟩))
                  have hIH := ih (insert a (insert b W'))
                  by_cases hv1W : v1 ∈ Uof st W' <;> by_cases hv2W : v2 ∈ Uof st W'
                  · have hqb := qOf_insert_eq1_mem st W' b v2 hbv2 hv2W
                    have hqa : qOf st (insert a (insert b W')) = qOf st (insert b W') := by
                      apply qOf_insert_eq1_mem st (insert b W') a v1 hav1
                      simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at hv1W ⊢
                      obtain ⟨w, hw, h⟩ := hv1W; exact ⟨w, Or.inr hw, h⟩
                    have := Finset.card_le_card hLHS0_sub; omega
                  · have hqb := qOf_insert_eq1_le st W' b v2 hbv2
                    have hqa : qOf st (insert a (insert b W')) = qOf st (insert b W') := by
                      apply qOf_insert_eq1_mem st (insert b W') a v1 hav1
                      simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at hv1W ⊢
                      obtain ⟨w, hw, h⟩ := hv1W; exact ⟨w, Or.inr hw, h⟩
                    have hnot : Sum.inr v2 ∉ LHS0 := by simp [LHS0, inr_mem_unionT_iff, hv2W]
                    have := card_le_sub_one_of_mem hLHS0_sub hmem_v2 hnot; omega
                  · have hqb := qOf_insert_eq1_mem st W' b v2 hbv2 hv2W
                    have hqa := qOf_insert_eq1_le st (insert b W') a v1 hav1
                    have hnot : Sum.inr v1 ∉ LHS0 := by simp [LHS0, inr_mem_unionT_iff, hv1W]
                    have := card_le_sub_one_of_mem hLHS0_sub hmem_v1 hnot; omega
                  · have hqb := qOf_insert_eq1_le st W' b v2 hbv2
                    have hqa := qOf_insert_eq1_le st (insert b W') a v1 hav1
                    have hnot1 : Sum.inr v1 ∉ LHS0 := by simp [LHS0, inr_mem_unionT_iff, hv1W]
                    have hnot2 : Sum.inr v2 ∉ LHS0 := by simp [LHS0, inr_mem_unionT_iff, hv2W]
                    have := card_le_sub_two_of_mem (by intro h; exact hv12 (Sum.inr.inj h))
                      hLHS0_sub hmem_v1 hmem_v2 hnot1 hnot2; omega
                · obtain ⟨v1, hav1⟩ := Finset.card_eq_one.mp ha1
                  set e1 := mkEdge ustar v1
                  set LHS := ((fa ∪ fb ∪ va.image (mkEdge ustar) ∪ vb.image (mkEdge ustar)).image Sum.inl ∪ unionT st W')
                  set LHS0 := ((fa ∪ fb ∪ vb.image (mkEdge ustar)).image Sum.inl ∪ unionT st W')
                  have hLHS_sub : LHS ⊆ insert (Sum.inl e1) LHS0 := by
                    intro z hz
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with he1 | heb
                      · rcases Finset.mem_union.mp he1 with he0 | hea
                        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                            (Finset.mem_image_of_mem _ (Finset.mem_union_left _ he0)))
                        · rw [hav1, Finset.image_singleton, Finset.mem_singleton] at hea
                          rw [hea]; exact Finset.mem_insert_self _ _
                      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                          (Finset.mem_image_of_mem _ (Finset.mem_union_right _ heb)))
                    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)
                  have hstep : LHS.card ≤ LHS0.card + 1 :=
                    le_trans (Finset.card_le_card hLHS_sub) (Finset.card_insert_le _ _)
                  have hsub_b := hside_ne1 b Finset.subset_union_right hb1
                  have hLHS0_sub : LHS0 ⊆ unionT st (insert a (insert b W')) := by
                    intro z hz
                    rw [unionT_insert, unionT_insert]
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with he0 | heb
                      · rcases Finset.mem_union.mp he0 with hea | hefb
                        · exact Finset.mem_union_left _ (inl_mem_Tof hea)
                        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof hefb))
                      · exact Finset.mem_union_right _ (Finset.mem_union_left _
                          (hsub_b (Finset.mem_image_of_mem _ heb)))
                    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
                  have hqb := qOf_insert_ne1 st W' b hb1
                  have hIH := ih (insert a (insert b W'))
                  by_cases hv1W : v1 ∈ Uof st W'
                  · have hqa : qOf st (insert a (insert b W')) = qOf st (insert b W') := by
                      apply qOf_insert_eq1_mem st (insert b W') a v1 hav1
                      simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at hv1W ⊢
                      obtain ⟨w, hw, h⟩ := hv1W; exact ⟨w, Or.inr hw, h⟩
                    have := Finset.card_le_card hLHS0_sub; omega
                  · have hqa := qOf_insert_eq1_le st (insert b W') a v1 hav1
                    have hmem_v1 : Sum.inr v1 ∈ unionT st (insert a (insert b W')) := by
                      rw [unionT_insert]
                      exact Finset.mem_union_left _ ((inr_mem_Tof_iff _ v1).mpr ⟨ha1, show v1 ∈ va by rw [hav1]; simp⟩)
                    have hnot : Sum.inr v1 ∉ LHS0 := by simp [LHS0, inr_mem_unionT_iff, hv1W]
                    have := card_le_sub_one_of_mem hLHS0_sub hmem_v1 hnot; omega
                · obtain ⟨v2, hbv2⟩ := Finset.card_eq_one.mp hb1
                  set e2 := mkEdge ustar v2
                  set LHS := ((fa ∪ fb ∪ va.image (mkEdge ustar) ∪ vb.image (mkEdge ustar)).image Sum.inl ∪ unionT st W')
                  set LHS0 := ((fa ∪ fb ∪ va.image (mkEdge ustar)).image Sum.inl ∪ unionT st W')
                  have hLHS_sub : LHS ⊆ insert (Sum.inl e2) LHS0 := by
                    intro z hz
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with he1 | heb
                      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
                          (Finset.mem_image_of_mem _ he1))
                      · rw [hbv2, Finset.image_singleton, Finset.mem_singleton] at heb
                        rw [heb]; exact Finset.mem_insert_self _ _
                    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hr)
                  have hstep : LHS.card ≤ LHS0.card + 1 :=
                    le_trans (Finset.card_le_card hLHS_sub) (Finset.card_insert_le _ _)
                  have hsub_a := hside_ne1 a Finset.subset_union_left ha1
                  have hLHS0_sub : LHS0 ⊆ unionT st (insert b (insert a W')) := by
                    intro z hz
                    rw [unionT_insert, unionT_insert]
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with he0 | hea
                      · rcases Finset.mem_union.mp he0 with hefa | hefb
                        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof hefa))
                        · exact Finset.mem_union_left _ (inl_mem_Tof hefb)
                      · exact Finset.mem_union_right _ (Finset.mem_union_left _
                          (hsub_a (Finset.mem_image_of_mem _ hea)))
                    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
                  have hqa := qOf_insert_ne1 st W' a ha1
                  have hIH := ih (insert b (insert a W'))
                  by_cases hv2W : v2 ∈ Uof st W'
                  · have hqb : qOf st (insert b (insert a W')) = qOf st (insert a W') := by
                      apply qOf_insert_eq1_mem st (insert a W') b v2 hbv2
                      simp only [Uof, Finset.mem_biUnion, Finset.mem_insert] at hv2W ⊢
                      obtain ⟨w, hw, h⟩ := hv2W; exact ⟨w, Or.inr hw, h⟩
                    have := Finset.card_le_card hLHS0_sub; omega
                  · have hqb := qOf_insert_eq1_le st (insert a W') b v2 hbv2
                    have hmem_v2 : Sum.inr v2 ∈ unionT st (insert b (insert a W')) := by
                      rw [unionT_insert]
                      exact Finset.mem_union_left _ ((inr_mem_Tof_iff _ v2).mpr ⟨hb1, show v2 ∈ vb by rw [hbv2]; simp⟩)
                    have hnot : Sum.inr v2 ∉ LHS0 := by simp [LHS0, inr_mem_unionT_iff, hv2W]
                    have := card_le_sub_one_of_mem hLHS0_sub hmem_v2 hnot; omega
                · have hsub_a := hside_ne1 a Finset.subset_union_left ha1
                  have hsub_b := hside_ne1 b Finset.subset_union_right hb1
                  have hsub : ((fa ∪ fb ∪ va.image (mkEdge ustar) ∪ vb.image (mkEdge ustar)).image Sum.inl ∪ unionT st W') ⊆
                      unionT st (insert a (insert b W')) := by
                    intro z hz
                    rw [unionT_insert, unionT_insert]
                    rcases Finset.mem_union.mp hz with hl | hr
                    · rw [Finset.mem_image] at hl
                      obtain ⟨e, he, rfl⟩ := hl
                      rcases Finset.mem_union.mp he with he1 | heb
                      · rcases Finset.mem_union.mp he1 with he0 | hea
                        · rcases Finset.mem_union.mp he0 with hefa | hefb
                          · exact Finset.mem_union_left _ (inl_mem_Tof hefa)
                          · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof hefb))
                        · exact Finset.mem_union_left _ (hsub_a (Finset.mem_image_of_mem _ hea))
                      · exact Finset.mem_union_right _ (Finset.mem_union_left _
                          (hsub_b (Finset.mem_image_of_mem _ heb)))
                    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
                  have hqb := qOf_insert_ne1 st W' b hb1
                  have hqa := qOf_insert_ne1 st (insert b W') a ha1
                  have := ih (insert a (insert b W'))
                  have := Finset.card_le_card hsub
                  omega
              · have hedge0 : edgeSetOf (va ∪ vb) = ∅ := by
                  unfold edgeSetOf
                  rw [dif_neg hcn]
                have hsub : Tof (st'.getD m (∅, ∅)) ∪ unionT st W' ⊆
                    unionT st (insert a (insert b W')) := by
                  rw [unionT_insert, unionT_insert]
                  intro z hz
                  rcases Finset.mem_union.mp hz with hl | hr
                  · have hTm0 : Tof (st'.getD m (∅, ∅)) = (fa ∪ fb).image Sum.inl := by
                      rw [hnew, Tof, if_neg hvo1, if_pos hvo2, hedge0, Finset.image_empty, Finset.union_empty]
                    rw [hTm0, Finset.mem_image] at hl
                    obtain ⟨e, he, rfl⟩ := hl
                    rcases Finset.mem_union.mp he with hea | heb
                    · exact Finset.mem_union_left _ (inl_mem_Tof hea)
                    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (inl_mem_Tof heb))
                  · exact Finset.mem_union_right _ (Finset.mem_union_right _ hr)
                have hqb : qOf st (insert b W') ≤ qOf st W' + 1 := by
                  by_cases hb1 : vb.card = 1
                  · obtain ⟨v, hbv⟩ := Finset.card_eq_one.mp hb1
                    exact qOf_insert_eq1_le st W' b v hbv
                  · exact qOf_insert_ne1 st W' b hb1
                have hqa : qOf st (insert a (insert b W')) ≤ qOf st (insert b W') + 1 := by
                  by_cases ha1 : va.card = 1
                  · obtain ⟨u, hau⟩ := Finset.card_eq_one.mp ha1
                    exact qOf_insert_eq1_le st (insert b W') a u hau
                  · exact qOf_insert_ne1 st (insert b W') a ha1
                have := ih (insert a (insert b W'))
                have := Finset.card_le_card hsub
                omega

lemma card_unionT_le (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsafe : ∀ k g, gs[k]? = some g → g.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (wiresAux gs (List.ofFn x)).getD (42 + k) false = false) :
    ∀ W : Finset ℕ, (unionT (runVF gs) W).card ≤
      gs.countP (fun g => isOr g.op) + qOf (runVF gs) W := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W
    simp only [List.countP_nil, Nat.zero_add, runVF, List.foldl_nil]
    have hsub : unionT initVF W ⊆ (Uof initVF W).image Sum.inr := by
      intro z hz
      simp only [unionT, Finset.mem_biUnion] at hz
      obtain ⟨w, hw, hzw⟩ := hz
      by_cases hw42 : w < 42
      · have hget : initVF.getD w (∅, ∅) = ({⟨w, hw42⟩}, ∅) := initVF_getD_lt w hw42
        rw [hget] at hzw
        simp only [Tof, Finset.image_empty, Finset.card_singleton, ↓reduceIte,
          Finset.empty_union, Finset.image_singleton, Finset.mem_singleton] at hzw
        rw [hzw]
        apply Finset.mem_image_of_mem
        simp only [Uof, Finset.mem_biUnion]
        refine ⟨w, hw, ?_⟩
        rw [hget]
        simp
      · have hget : initVF.getD w (∅, ∅) = (∅, ∅) :=
          getD_of_ge _ _ _ (by rw [initVF_length]; omega)
        rw [hget] at hzw
        simp [Tof] at hzw
    calc (unionT initVF W).card
        ≤ ((Uof initVF W).image Sum.inr).card := Finset.card_le_card hsub
      _ ≤ (Uof initVF W).card := Finset.card_image_le
      _ ≤ qOf initVF W := by rw [qOf_eq]; omega
  | append_singleton gs g ih =>
    have hmono_pre : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have ih' := ih hmono_pre (hsafe_prefix hsafe)
    rw [runVF_concat, List.countP_append, List.countP_cons, List.countP_nil]
    have hg_m := hmono g (List.mem_append_right _ (List.mem_singleton_self g))
    rcases hg_m.1 with hand | hor
    · simp only [hand, isOr, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact golden_step_and (runVF gs) _ ih' g hand hg_m.2
        (fun a b hin => biclique_of_and gs g hmono hsafe hand a b hin)
    · simp only [hor, isOr, ↓reduceIte, Nat.zero_add]
      exact golden_step_or (runVF gs) _ ih' g hor hg_m.2

lemma countP_and_add_or (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    gs.countP (fun g => isAnd g.op) + gs.countP (fun g => isOr g.op) = gs.length := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    have hg := hmono g (List.mem_cons_self ..)
    have ih' := ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg'))
    rcases hg with hand | hor
    · have h1 : isAnd g.op = true := by rw [hand]; rfl
      have h2 : isOr g.op = false := by rw [hand]; rfl
      rw [List.countP_cons, List.countP_cons, h1, h2]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have h1 : isAnd g.op = false := by rw [hor]; rfl
      have h2 : isOr g.op = true := by rw [hor]; rfl
      rw [List.countP_cons, List.countP_cons, h1, h2]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega

lemma case2_impossible (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 124) (hc : computesF C)
    (hsafe : ∀ k g, C.gates[k]? = some g → g.op = GateOp.and →
      ∀ x : Fin 42 → Bool,
        (¬ ∃ a b : Fin 42, inc a b = true ∧ x a = true ∧ x b = true) →
        (C.wires (List.ofFn x)).getD (42 + k) false = false) : False := by
  have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hm g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hV_out : ((runVF C.gates).getD C.output (∅, ∅)).1 = ∅ := by
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    have h1 := (runVF_getV_iff C.gates hmono hsafe C.output u).mp hu
    have h2 := (hc (singleVec u)).mp h1
    exact singleVec_indep u h2
  have hE_sub : allEdges ⊆ ((runVF C.gates).getD C.output (∅, ∅)).2 := by
    intro e he
    have hinc : inc e.1 e.2 = true := (Finset.mem_filter.mp he).2
    have htrue : (wiresAux C.gates (List.ofFn (edgeVec e))).getD C.output false = true := by
      exact (hc (edgeVec e)).mpr ⟨e.1, e.2, hinc, by simp [edgeVec, pairVec], by simp [edgeVec, pairVec]⟩
    have hres := runVF_edge_sound C.gates hmono hsafe C.output e hinc htrue
    rw [hV_out] at hres
    rcases hres with h | h | h
    · exact h
    · simp at h
    · simp at h
  have hE_allF : allEdges ⊆ allF (runVF C.gates) := by
    intro e he
    exact mem_allF_of_mem _ C.output e (hE_sub he)
  have hAND : 21 ≤ C.gates.countP (fun g => isAnd g.op) := by
    have h1 := card_allF_le C.gates hmono hsafe
    have h2 := Finset.card_le_card hE_allF
    rw [card_allEdges] at h2
    omega
  have hOR : 104 ≤ C.gates.countP (fun g => isOr g.op) := by
    have h1 := card_unionT_le C.gates hmono hsafe {C.output}
    have hq1 : qOf (runVF C.gates) {C.output} = 1 := by
      rw [qOf_eq]
      have hw1 : Wne1 (runVF C.gates) {C.output} = {C.output} := by
        ext w
        simp only [Wne1, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · rintro rfl; exact ⟨rfl, by rw [hV_out]; simp⟩
      have hu1 : Uof (runVF C.gates) {C.output} = ∅ := by
        ext u
        simp only [Uof, Finset.mem_biUnion, Finset.mem_singleton, Finset.notMem_empty,
          iff_false, not_exists, not_and]
        rintro w rfl
        rw [hV_out]; simp
      rw [hw1, hu1]; simp
    have hsubT : allEdges.image Sum.inl ⊆ unionT (runVF C.gates) {C.output} := by
      intro z hz
      simp only [unionT, Finset.mem_biUnion, Finset.mem_singleton]
      refine ⟨C.output, rfl, ?_⟩
      simp only [Tof, Finset.mem_union]
      left
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image_of_mem Sum.inl (hE_sub he)
    have hcardT : 105 ≤ (unionT (runVF C.gates) {C.output}).card := by
      have hc1 := Finset.card_le_card hsubT
      rw [Finset.card_image_of_injective _ Sum.inl_injective, card_allEdges] at hc1
      exact hc1
    rw [hq1] at h1
    omega
  have hsum := countP_and_add_or C.gates (fun g hg => (hmono g hg).1)
  have hsize : C.size = C.gates.length := rfl
  omega

lemma main_proof (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 124) (hc : computesF C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 124 ∧ computesF D ∧
      ∃ k g, D.gates[k]? = some g ∧ g.op = GateOp.and ∧
        (D.wires (List.ofFn targetSet)).getD (42 + k) false = true := by
  by_cases hex : ∃ k : ℕ, ∃ g : Gate, C.gates[k]? = some g ∧ g.op = GateOp.and ∧
      ∃ x : Fin 42 → Bool,
        (¬ ∃ u v : Fin 42, inc u v = true ∧ x u = true ∧ x v = true) ∧
        (C.wires (List.ofFn x)).getD (42 + k) false = true
  · exact case1_solve C hm hs hc hex
  · exfalso
    apply case2_impossible C hm hs hc
    intro k g hgk hgop x hx
    cases hval : (C.wires (List.ofFn x)).getD (42 + k) false
    · rfl
    · exfalso
      exact hex ⟨k, g, hgk, hgop, x, hx, hval⟩

end PEqualNP.Outside.L_meta_1892

theorem PEqualNP.Outside.L_meta_1892 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ (124 : ℕ) ∧ (∀ (x6 : Fin (42 : ℕ) → Bool), x5.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) ∧ ∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x5.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x6) Bool.false = Bool.true := by
  intro C hm hs hc
  have hc' : PEqualNP.Outside.L_meta_1892.computesF C := by
    intro x
    simpa [PEqualNP.Outside.L_meta_1892.inc, PEqualNP.Outside.L_meta_1892.diffList] using hc x
  obtain ⟨D, hdm, hds, hdc, k, g, hgk, hgop, hhit⟩ :=
    PEqualNP.Outside.L_meta_1892.main_proof C hm hs hc'
  refine ⟨D, hdm, hds, ?_, k, g, hgk, hgop, hhit⟩
  intro x
  simpa [PEqualNP.Outside.L_meta_1892.inc, PEqualNP.Outside.L_meta_1892.diffList] using hdc x
