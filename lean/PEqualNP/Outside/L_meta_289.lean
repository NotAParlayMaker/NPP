import Mathlib
import PEqualNP.Defs
noncomputable section

namespace PEqualNP.Outside.LMeta289Aux

open Finset

abbrev l289N (k m : ℕ) : ℕ := m + 2 * k * m * m

def l289Orig (k : ℕ) {m : ℕ} (u : Fin m) : Fin (l289N k m) :=
  ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right m (2 * k * m * m))⟩

@[simp] theorem l289Orig_val (k : ℕ) {m : ℕ} (u : Fin m) :
    (l289Orig k u).val = u.val := rfl

theorem l289Orig_inj (k : ℕ) {m : ℕ} {u u' : Fin m} (h : l289Orig k u = l289Orig k u') :
    u = u' := by
  have h' := congrArg Fin.val h
  simp only [l289Orig_val] at h'
  exact Fin.ext h'

theorem l289Orig_lt_m (k : ℕ) {m : ℕ} (u : Fin m) : (l289Orig k u).val < m := u.isLt

theorem l289_path_lt (k m : ℕ) {u v : Fin m} (hu : u < v) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < l289N k m := by
  show m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m
  have hq : u.val * m + v.val + 1 ≤ m * m := by
    have h1 : v.val + 1 ≤ m := Nat.succ_le_of_lt v.isLt
    have h2 : u.val + 1 ≤ m - 1 := by omega
    calc u.val * m + v.val + 1 = u.val * m + (v.val + 1) := by ring
      _ ≤ u.val * m + m := Nat.add_le_add_left h1 _
      _ = (u.val + 1) * m := by ring
      _ ≤ (m - 1) * m := Nat.mul_le_mul_right m h2
      _ ≤ m * m := Nat.mul_le_mul_right m (Nat.sub_le m 1)
  have hi : i.val < 2 * k := i.isLt
  have h1 : 2 * k * (u.val * m + v.val) + i.val
      < 2 * k * (u.val * m + v.val + 1) := by
    have h := Nat.add_lt_add_left i.isLt (2 * k * (u.val * m + v.val))
    have h' : 2 * k * (u.val * m + v.val + 1) = 2 * k * (u.val * m + v.val) + 2 * k := by
      ring
    rw [h']
    exact h
  have h2 : 2 * k * (u.val * m + v.val) + i.val < 2 * k * (m * m) :=
    Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_left (2 * k) hq)
  calc m + 2 * k * (u.val * m + v.val) + i.val
      = m + (2 * k * (u.val * m + v.val) + i.val) := by ring
    _ < m + 2 * k * (m * m) := Nat.add_lt_add_left h2 m
    _ = m + 2 * k * m * m := by ring

def l289Path (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (i : Fin (2 * k)) :
    Fin (l289N k m) :=
  ⟨m + 2 * k * (u.val * m + v.val) + i.val, l289_path_lt k m hu i⟩

@[simp] theorem l289Path_val (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (i : Fin (2 * k)) :
    (l289Path k u v hu i).val = m + 2 * k * (u.val * m + v.val) + i.val := rfl

theorem l289Path_ge_m (k : ℕ) {m : ℕ} {u v : Fin m} {hu : u < v} {i : Fin (2 * k)} :
    m ≤ (l289Path k u v hu i).val := by
  rw [l289Path_val]
  exact Nat.le_trans (Nat.le_add_right m _) (Nat.le_add_right _ _)

theorem l289Path_inj (k : ℕ) {m : ℕ} {u v u' v' : Fin m} (hu : u < v) (hu' : u' < v')
    {i i' : Fin (2 * k)} (h : l289Path k u v hu i = l289Path k u' v' hu' i') :
    u = u' ∧ v = v' ∧ i = i' := by
  have hval : m + 2 * k * (u.val * m + v.val) + i.val
      = m + 2 * k * (u'.val * m + v'.val) + i'.val := by
    have h' := congrArg Fin.val h
    rw [l289Path_val, l289Path_val] at h'
    exact h'
  have hmain : 2 * k * (u.val * m + v.val) + i.val
      = 2 * k * (u'.val * m + v'.val) + i'.val :=
    Nat.add_left_cancel (by simpa only [Nat.add_assoc] using hval)
  have ht : 0 < 2 * k := by
    by_contra hc
    have h0 : 2 * k = 0 := by omega
    have hlt := i.isLt
    omega
  have hi : i.val = i'.val := by
    have hmod : (2 * k * (u.val * m + v.val) + i.val) % (2 * k)
        = (2 * k * (u'.val * m + v'.val) + i'.val) % (2 * k) := by rw [hmain]
    rw [Nat.add_comm (2 * k * (u.val * m + v.val)),
      Nat.add_comm (2 * k * (u'.val * m + v'.val)),
      Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt] at hmod
    exact hmod
  have hii : i = i' := Fin.ext hi
  have hq : u.val * m + v.val = u'.val * m + v'.val := by
    have h2 : 2 * k * (u.val * m + v.val) = 2 * k * (u'.val * m + v'.val) := by
      rw [← hii] at hmain
      exact Nat.add_right_cancel hmain
    exact Nat.mul_left_cancel ht h2
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le u.val) u.isLt
  have hv : v.val = v'.val := by
    have h1 : (u.val * m + v.val) % m = (u'.val * m + v'.val) % m := by rw [hq]
    rw [show u.val * m + v.val = v.val + m * u.val by ring,
      show u'.val * m + v'.val = v'.val + m * u'.val by ring,
      Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt v.isLt, Nat.mod_eq_of_lt v'.isLt] at h1
    exact h1
  have hu' : u.val = u'.val := by
    have h1 : (u.val * m + v.val) / m = (u'.val * m + v'.val) / m := by rw [hq]
    rw [show u.val * m + v.val = v.val + m * u.val by ring,
      show u'.val * m + v'.val = v'.val + m * u'.val by ring,
      Nat.add_mul_div_left v.val u.val hm, Nat.add_mul_div_left v'.val u'.val hm,
      Nat.div_eq_of_lt v.isLt, Nat.div_eq_of_lt v'.isLt, Nat.zero_add,
      Nat.zero_add] at h1
    exact h1
  exact ⟨Fin.ext hu', Fin.ext hv, hii⟩

theorem l289Path_eq_iff (k : ℕ) {m : ℕ} {u v : Fin m} (hu : u < v) {i i' : Fin (2 * k)} :
    l289Path k u v hu i = l289Path k u v hu i' ↔ i = i' := by
  constructor
  · intro h
    exact (l289Path_inj k hu hu h).2.2
  · intro h
    rw [h]

theorem l289Orig_ne_path (k : ℕ) {m : ℕ} {u : Fin m} {u' v' : Fin m} (hu' : u' < v')
    (i : Fin (2 * k)) : l289Orig k u ≠ l289Path k u' v' hu' i := by
  intro h
  have h1 : (l289Orig k u).val = (l289Path k u' v' hu' i).val := by rw [h]
  rw [l289Orig_val, l289Path_val] at h1
  have h2 := l289Path_ge_m k (hu := hu') (i := i)
  omega

def l289PathSet (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) : Finset (Fin (l289N k m)) :=
  (Finset.univ : Finset (Fin (2 * k))).image (fun i => l289Path k u v hu i)

theorem l289PathSet_card (k : ℕ) {m : ℕ} {u v : Fin m} (hu : u < v) :
    (l289PathSet k u v hu).card = 2 * k := by
  rw [l289PathSet, Finset.card_image_of_injective]
  · simp
  · intro i i' h
    exact (l289Path_inj k hu hu h).2.2

theorem l289PathSet_mem_iff (k : ℕ) {m : ℕ} {u v : Fin m} (hu : u < v)
    {x : Fin (l289N k m)} :
    x ∈ l289PathSet k u v hu ↔ ∃ i : Fin (2 * k), l289Path k u v hu i = x := by
  rw [l289PathSet, Finset.mem_image]
  constructor
  · rintro ⟨i, -, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ i, hi⟩

theorem l289Path_mem_pathSet (k : ℕ) {m : ℕ} {u v : Fin m} (hu : u < v)
    (i : Fin (2 * k)) : l289Path k u v hu i ∈ l289PathSet k u v hu := by
  rw [l289PathSet]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem l289PathSet_disjoint (k : ℕ) {m : ℕ} {u v u' v' : Fin m} (hu : u < v) (hu' : u' < v')
    (hne : u ≠ u' ∨ v ≠ v') :
    Disjoint (l289PathSet k u v hu) (l289PathSet k u' v' hu') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [l289PathSet_mem_iff] at hx hx'
  obtain ⟨i, hi⟩ := hx
  obtain ⟨i', hi'⟩ := hx'
  have hEq : l289Path k u v hu i = l289Path k u' v' hu' i' := by rw [hi, hi']
  obtain ⟨h1, h2, -⟩ := l289Path_inj k hu hu' hEq
  rcases hne with hne | hne
  · exact hne h1
  · exact hne h2

theorem l289Path_pair_disjoint (k : ℕ) {m : ℕ} {u v : Fin m} (hu : u < v)
    {a b a' b' : Fin (2 * k)} (haa : a ≠ a') (hab : a ≠ b') (hba : b ≠ a') (hbb : b ≠ b') :
    Disjoint ({l289Path k u v hu a, l289Path k u v hu b} : Finset (Fin (l289N k m)))
      ({l289Path k u v hu a', l289Path k u v hu b'} : Finset (Fin (l289N k m))) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  have key : ∀ {i i' : Fin (2 * k)}, l289Path k u v hu i = l289Path k u v hu i' → i = i' :=
    fun h => (l289Path_inj k hu hu h).2.2
  rcases hx with rfl | rfl <;> rcases hx' with h' | h'
  · exact haa (key h')
  · exact hab (key h')
  · exact hba (key h')
  · exact hbb (key h')

def l289Rel (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m)) (x y : Fin (l289N k m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
      (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
      (i.val + 1 = 2 * k ∧ y.val = v.val))

def l289P0 (k : ℕ) (hk : 1 ≤ k) : Fin (2 * k) := ⟨0, by omega⟩

@[simp] theorem l289P0_val (k : ℕ) (hk : 1 ≤ k) : (l289P0 k hk).val = 0 := rfl

def l289PLast (k : ℕ) (hk : 1 ≤ k) : Fin (2 * k) := ⟨2 * k - 1, by omega⟩

@[simp] theorem l289PLast_val (k : ℕ) (hk : 1 ≤ k) : (l289PLast k hk).val = 2 * k - 1 := rfl

theorem l289PLast_succ (k : ℕ) (hk : 1 ≤ k) : (l289PLast k hk).val + 1 = 2 * k := by
  rw [l289PLast_val]
  omega

theorem l289Rel_first {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m} (hu : u < v)
    (hadj : H.Adj u v) (hk : 1 ≤ k) :
    l289Rel k H (l289Path k u v hu (l289P0 k hk)) (l289Orig k u) := by
  refine ⟨u, v, hu, hadj, l289P0 k hk, ?_, Or.inl ⟨?_, ?_⟩⟩
  · simp
  · simp
  · simp

theorem l289Rel_step {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m} (hu : u < v)
    (hadj : H.Adj u v) {i : Fin (2 * k)} (hi : i.val + 1 < 2 * k) :
    l289Rel k H (l289Path k u v hu i) (l289Path k u v hu ⟨i.val + 1, hi⟩) := by
  refine ⟨u, v, hu, hadj, i, ?_, Or.inr (Or.inl ⟨hi, ?_⟩)⟩
  · simp
  · simp only [l289Path_val]
    omega

theorem l289Rel_last {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m} (hu : u < v)
    (hadj : H.Adj u v) (hk : 1 ≤ k) :
    l289Rel k H (l289Path k u v hu (l289PLast k hk)) (l289Orig k v) := by
  refine ⟨u, v, hu, hadj, l289PLast k hk, ?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
  · simp
  · rw [l289PLast_val]
    omega
  · simp

theorem l289_adj_of_rel {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)}
    {S : SimpleGraph (Fin (l289N k m))}
    (hS : S = SimpleGraph.fromRel (l289Rel k H)) {x y : Fin (l289N k m)} (hxy : x ≠ y)
    (h : l289Rel k H x y ∨ l289Rel k H y x) : S.Adj x y := by
  rw [hS, SimpleGraph.fromRel_adj]
  exact ⟨hxy, h⟩

theorem l289_adj_first {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)}
    {S : SimpleGraph (Fin (l289N k m))} (hS : S = SimpleGraph.fromRel (l289Rel k H))
    {u v : Fin m} (hu : u < v) (hadj : H.Adj u v) (hk : 1 ≤ k) :
    S.Adj (l289Orig k u) (l289Path k u v hu (l289P0 k hk)) := by
  refine l289_adj_of_rel hS ?_ (Or.inr (l289Rel_first hu hadj hk))
  exact l289Orig_ne_path k hu (l289P0 k hk)

theorem l289_adj_step {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)}
    {S : SimpleGraph (Fin (l289N k m))} (hS : S = SimpleGraph.fromRel (l289Rel k H))
    {u v : Fin m} (hu : u < v) (hadj : H.Adj u v) {i : Fin (2 * k)}
    (hi : i.val + 1 < 2 * k) :
    S.Adj (l289Path k u v hu i) (l289Path k u v hu ⟨i.val + 1, hi⟩) := by
  refine l289_adj_of_rel hS ?_ (Or.inl (l289Rel_step hu hadj hi))
  intro h
  have := (l289Path_inj k hu hu h).2.2
  have h2 := congrArg Fin.val this
  simp at h2

theorem l289_adj_last {k : ℕ} {m : ℕ} {H : SimpleGraph (Fin m)}
    {S : SimpleGraph (Fin (l289N k m))} (hS : S = SimpleGraph.fromRel (l289Rel k H))
    {u v : Fin m} (hu : u < v) (hadj : H.Adj u v) (hk : 1 ≤ k) :
    S.Adj (l289Path k u v hu (l289PLast k hk)) (l289Orig k v) := by
  refine l289_adj_of_rel hS ?_ (Or.inl (l289Rel_last hu hadj hk))
  intro h
  have h1 : (l289Path k u v hu (l289PLast k hk)).val = (l289Orig k v).val := by rw [h]
  rw [l289Path_val, l289Orig_val] at h1
  have h2 := l289Path_ge_m k (hu := hu) (i := l289PLast k hk)
  omega

noncomputable def l289PathSetP (k : ℕ) {m : ℕ} (p : Fin m × Fin m) :
    Finset (Fin (l289N k m)) := by
  classical
  exact if h : p.1 < p.2 then l289PathSet k p.1 p.2 h else ∅

theorem l289PathSetP_of_lt {k m : ℕ} {p : Fin m × Fin m} (hu : p.1 < p.2) :
    l289PathSetP k p = l289PathSet k p.1 p.2 hu := by
  unfold l289PathSetP
  rw [dif_pos hu]

def l289M2A (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (j : Fin k) : Fin (l289N k m) :=
  l289Path k u v hu ⟨2 * j.val, by have := j.isLt; omega⟩

def l289M2B (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (j : Fin k) : Fin (l289N k m) :=
  l289Path k u v hu ⟨2 * j.val + 1, by have := j.isLt; omega⟩

def l289MidA (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (j : Fin (k - 1)) :
    Fin (l289N k m) :=
  l289Path k u v hu ⟨2 * j.val + 1, by have := j.isLt; omega⟩

def l289MidB (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (j : Fin (k - 1)) :
    Fin (l289N k m) :=
  l289Path k u v hu ⟨2 * j.val + 2, by have := j.isLt; omega⟩

theorem l289_pair_family {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    {S : SimpleGraph α} {U : Finset α}
    (hcover : ∀ x y : α, S.Adj x y → x ∈ U ∨ y ∈ U)
    (x y : ι → α)
    (hdisj : ∀ i j : ι, i ≠ j →
      Disjoint ({x i, y i} : Finset α) ({x j, y j} : Finset α))
    (hadj : ∀ i, S.Adj (x i) (y i)) :
    Fintype.card ι ≤ (U ∩ Finset.univ.biUnion (fun i => ({x i, y i} : Finset α))).card := by
  classical
  have hpair : ∀ i : ι, 1 ≤ (U ∩ ({x i, y i} : Finset α)).card := by
    intro i
    rcases hcover (x i) (y i) (hadj i) with h | h
    · exact Finset.one_le_card.mpr ⟨x i, Finset.mem_inter.mpr ⟨h, by simp⟩⟩
    · exact Finset.one_le_card.mpr ⟨y i, Finset.mem_inter.mpr ⟨h, by simp⟩⟩
  have hdisj' : ∀ i j : ι, i ≠ j →
      Disjoint (U ∩ ({x i, y i} : Finset α)) (U ∩ ({x j, y j} : Finset α)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.disjoint_left.mp (hdisj i j hij)) (Finset.mem_inter.mp ha).2
      (Finset.mem_inter.mp hb).2
  have hcard : ((Finset.univ : Finset ι).biUnion (fun i => U ∩ ({x i, y i} : Finset α))).card
      = ∑ i : ι, (U ∩ ({x i, y i} : Finset α)).card := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj' i j hij)]
  calc Fintype.card ι = ∑ i : ι, 1 := by
        rw [← Finset.card_univ, Finset.card_eq_sum_ones]
    _ ≤ ∑ i : ι, (U ∩ ({x i, y i} : Finset α)).card :=
        Finset.sum_le_sum (fun i _ => hpair i)
    _ = ((Finset.univ : Finset ι).biUnion
          (fun i => U ∩ ({x i, y i} : Finset α))).card := hcard.symm
    _ = (U ∩ (Finset.univ : Finset ι).biUnion (fun i => ({x i, y i} : Finset α))).card := by
        rw [Finset.inter_biUnion]

theorem l289_card_add_le {α : Type*} [DecidableEq α] {U B1 B2 C : Finset α}
    (h1 : B1 ⊆ C) (h2 : B2 ⊆ C) (hd : Disjoint B1 B2) :
    (U ∩ B1).card + (U ∩ B2).card ≤ (U ∩ C).card := by
  classical
  have hd' : Disjoint (U ∩ B1) (U ∩ B2) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.disjoint_left.mp hd) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  have hsub : U ∩ B1 ∪ U ∩ B2 ⊆ U ∩ C := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, h1 (Finset.mem_inter.mp ha).2⟩
    · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, h2 (Finset.mem_inter.mp ha).2⟩
  calc (U ∩ B1).card + (U ∩ B2).card = (U ∩ B1 ∪ U ∩ B2).card := by
        rw [Finset.card_union_of_disjoint hd']
    _ ≤ (U ∩ C).card := Finset.card_le_card hsub

noncomputable def l289Edges (m : ℕ) (H : SimpleGraph (Fin m)) : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)

theorem l289Edges_mem {m : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m} :
    p ∈ l289Edges m H ↔ p.1 < p.2 ∧ H.Adj p.1 p.2 := by
  classical
  simp [l289Edges]

theorem l289Edges_card {m : ℕ} (H : SimpleGraph (Fin m)) :
    (l289Edges m H).card = H.edgeSet.ncard := by
  classical
  have h1 : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have himg : (l289Edges m H).image (fun p : Fin m × Fin m => s(p.1, p.2)) = H.edgeFinset := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_image] at he
      obtain ⟨p, hp, rfl⟩ := he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (l289Edges_mem.mp hp).2
    · intro he
      revert he
      refine Sym2.ind ?_ e
      intro a b he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hne : a ≠ b := H.ne_of_adj he
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact Finset.mem_image.mpr ⟨(a, b), l289Edges_mem.mpr ⟨hab, he⟩, rfl⟩
      · exact Finset.mem_image.mpr
          ⟨(b, a), l289Edges_mem.mpr ⟨hba, H.adj_symm he⟩, Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  have hinj : Set.InjOn (fun p : Fin m × Fin m => s(p.1, p.2)) ↑(l289Edges m H) := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := l289Edges_mem.mp hp
    obtain ⟨hq1, hq2⟩ := l289Edges_mem.mp hq
    rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      omega
  calc (l289Edges m H).card = ((l289Edges m H).image (fun p => s(p.1, p.2))).card := by
        rw [Finset.card_image_of_injOn hinj]
    _ = H.edgeFinset.card := by rw [himg]
    _ = H.edgeSet.ncard := h1.symm

theorem l289M2A_val (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (j : Fin k) :
    (l289M2A k u v hu j).val = m + 2 * k * (u.val * m + v.val) + 2 * j.val := by
  simp [l289M2A]

theorem l289M2B_val (k : ℕ) {m : ℕ} (u v : Fin m) (hu : u < v) (j : Fin k) :
    (l289M2B k u v hu j).val = m + 2 * k * (u.val * m + v.val) + (2 * j.val + 1) := by
  simp [l289M2B]

theorem l289_edge_base {k m : ℕ} (hk : 1 ≤ k) {H : SimpleGraph (Fin m)}
    {S : SimpleGraph (Fin (l289N k m))} (hS : S = SimpleGraph.fromRel (l289Rel k H))
    {U : Finset (Fin (l289N k m))} (hcover : ∀ x y, S.Adj x y → x ∈ U ∨ y ∈ U)
    {p : Fin m × Fin m} (hp : p ∈ l289Edges m H) :
    k ≤ (U ∩ l289PathSetP k p).card := by
  classical
  obtain ⟨hu, hadj⟩ := l289Edges_mem.mp hp
  rw [l289PathSetP_of_lt hu]
  have hadj2 : ∀ j : Fin k, S.Adj (l289M2A k p.1 p.2 hu j) (l289M2B k p.1 p.2 hu j) := by
    intro j
    have hi : (2 * j.val) + 1 < 2 * k := by have := j.isLt; omega
    exact l289_adj_step hS hu hadj hi
  have hdisj2 : ∀ j j' : Fin k, j ≠ j' →
      Disjoint ({l289M2A k p.1 p.2 hu j, l289M2B k p.1 p.2 hu j} : Finset (Fin (l289N k m)))
        ({l289M2A k p.1 p.2 hu j', l289M2B k p.1 p.2 hu j'} : Finset (Fin (l289N k m))) := by
    intro j j' hjj'
    simp only [l289M2A, l289M2B]
    refine l289Path_pair_disjoint k hu ?_ ?_ ?_ ?_
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      exact hjj' (Fin.ext (by omega))
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      exact hjj' (Fin.ext (by omega))
  have key := l289_pair_family (S := S) (U := U) hcover
    (l289M2A k p.1 p.2 hu) (l289M2B k p.1 p.2 hu) hdisj2 hadj2
  have hsub : (Finset.univ : Finset (Fin k)).biUnion
      (fun i => ({l289M2A k p.1 p.2 hu i, l289M2B k p.1 p.2 hu i} : Finset (Fin (l289N k m))))
      ⊆ l289PathSet k p.1 p.2 hu := by
    intro w hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨i, -, hw⟩ := hw
    rw [l289PathSet_mem_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨⟨2 * i.val, by have := i.isLt; omega⟩, rfl⟩
    · exact ⟨⟨2 * i.val + 1, by have := i.isLt; omega⟩, rfl⟩
  calc k = Fintype.card (Fin k) := by simp
    _ ≤ (U ∩ (Finset.univ : Finset (Fin k)).biUnion
          (fun i => ({l289M2A k p.1 p.2 hu i, l289M2B k p.1 p.2 hu i} :
            Finset (Fin (l289N k m))))).card := key
    _ ≤ (U ∩ l289PathSet k p.1 p.2 hu).card := Finset.card_le_card (by
          intro w hw
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hsub (Finset.mem_inter.mp hw).2⟩)

theorem l289_edge_extra {k m : ℕ} (hk : 1 ≤ k) {H : SimpleGraph (Fin m)}
    {S : SimpleGraph (Fin (l289N k m))} (hS : S = SimpleGraph.fromRel (l289Rel k H))
    {U : Finset (Fin (l289N k m))} (hcover : ∀ x y, S.Adj x y → x ∈ U ∨ y ∈ U)
    {p : Fin m × Fin m} (hp : p ∈ l289Edges m H)
    (hboth : l289Orig k p.1 ∉ U ∧ l289Orig k p.2 ∉ U) :
    k + 1 ≤ (U ∩ l289PathSetP k p).card := by
  classical
  obtain ⟨hu, hadj⟩ := l289Edges_mem.mp hp
  obtain ⟨hpu, hpv⟩ := hboth
  rw [l289PathSetP_of_lt hu]
  have hp0U : l289Path k p.1 p.2 hu (l289P0 k hk) ∈ U := by
    rcases hcover _ _ (l289_adj_first hS hu hadj hk) with h | h
    · exact absurd h hpu
    · exact h
  have hpNU : l289Path k p.1 p.2 hu (l289PLast k hk) ∈ U := by
    rcases hcover _ _ (l289_adj_last hS hu hadj hk) with h | h
    · exact h
    · exact absurd h hpv
  have hadj1 : ∀ j : Fin (k - 1),
      S.Adj (l289MidA k p.1 p.2 hu j) (l289MidB k p.1 p.2 hu j) := by
    intro j
    have hi : (2 * j.val + 1) + 1 < 2 * k := by have := j.isLt; omega
    exact l289_adj_step hS hu hadj hi
  have hdisj1 : ∀ j j' : Fin (k - 1), j ≠ j' →
      Disjoint ({l289MidA k p.1 p.2 hu j, l289MidB k p.1 p.2 hu j} : Finset (Fin (l289N k m)))
        ({l289MidA k p.1 p.2 hu j', l289MidB k p.1 p.2 hu j'} : Finset (Fin (l289N k m))) := by
    intro j j' hjj'
    simp only [l289MidA, l289MidB]
    refine l289Path_pair_disjoint k hu ?_ ?_ ?_ ?_
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      exact hjj' (Fin.ext (by omega))
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      exact hjj' (Fin.ext (by omega))
  let C1 : Finset (Fin (l289N k m)) := (Finset.univ : Finset (Fin (k - 1))).biUnion
    (fun j => ({l289MidA k p.1 p.2 hu j, l289MidB k p.1 p.2 hu j} : Finset (Fin (l289N k m))))
  let C2 : Finset (Fin (l289N k m)) :=
    ({l289Path k p.1 p.2 hu (l289P0 k hk), l289Path k p.1 p.2 hu (l289PLast k hk)} :
      Finset (Fin (l289N k m)))
  have hC1 : k - 1 ≤ (U ∩ C1).card := by
    have key := l289_pair_family (S := S) (U := U) hcover
      (l289MidA k p.1 p.2 hu) (l289MidB k p.1 p.2 hu) hdisj1 hadj1
    simpa only [Fintype.card_fin, C1] using key
  have hC2 : 2 ≤ (U ∩ C2).card := by
    have hsub2 : C2 ⊆ U := by
      intro w hw
      simp only [C2, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hp0U
      · exact hpNU
    have hcard : (U ∩ C2).card = C2.card := by
      rw [Finset.inter_comm, Finset.inter_eq_left.mpr hsub2]
    rw [hcard]
    have hne : l289Path k p.1 p.2 hu (l289P0 k hk)
        ≠ l289Path k p.1 p.2 hu (l289PLast k hk) := by
      intro h
      have hi := (l289Path_eq_iff k hu).mp h
      have hvv := congrArg Fin.val hi
      simp only [l289P0_val, l289PLast_val] at hvv
      omega
    have hC2val : C2 = ({l289Path k p.1 p.2 hu (l289P0 k hk),
        l289Path k p.1 p.2 hu (l289PLast k hk)} : Finset (Fin (l289N k m))) := rfl
    rw [hC2val, Finset.card_pair hne]
  have hC1sub : C1 ⊆ l289PathSet k p.1 p.2 hu := by
    intro w hw
    simp only [C1, Finset.mem_biUnion, Finset.mem_univ, true_and] at hw
    obtain ⟨j, hw⟩ := hw
    rw [l289PathSet_mem_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨⟨2 * j.val + 1, by have := j.isLt; omega⟩, rfl⟩
    · exact ⟨⟨2 * j.val + 2, by have := j.isLt; omega⟩, rfl⟩
  have hC2sub : C2 ⊆ l289PathSet k p.1 p.2 hu := by
    intro w hw
    simp only [C2, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [l289PathSet_mem_iff]
    rcases hw with rfl | rfl
    · exact ⟨l289P0 k hk, rfl⟩
    · exact ⟨l289PLast k hk, rfl⟩
  have hdisjC : Disjoint C1 C2 := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    simp only [C1, Finset.mem_biUnion, Finset.mem_univ, true_and] at hw1
    obtain ⟨j, hw1⟩ := hw1
    simp only [C2, Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
    rcases hw1 with rfl | rfl <;> rcases hw2 with h | h
    · have hi := (l289Path_eq_iff k hu).mp h
      have hvv := congrArg Fin.val hi
      simp only [l289MidA, l289P0_val, Fin.val_mk] at hvv
      have := j.isLt
      omega
    · have hi := (l289Path_eq_iff k hu).mp h
      have hvv := congrArg Fin.val hi
      simp only [l289MidA, l289PLast_val, Fin.val_mk] at hvv
      have := j.isLt
      omega
    · have hi := (l289Path_eq_iff k hu).mp h
      have hvv := congrArg Fin.val hi
      simp only [l289MidB, l289P0_val, Fin.val_mk] at hvv
      have := j.isLt
      omega
    · have hi := (l289Path_eq_iff k hu).mp h
      have hvv := congrArg Fin.val hi
      simp only [l289MidB, l289PLast_val, Fin.val_mk] at hvv
      have := j.isLt
      omega
  have hcomb := l289_card_add_le (U := U) hC1sub hC2sub hdisjC
  omega

theorem l289PathSetP_ge_m {k m : ℕ} {p : Fin m × Fin m} {z : Fin (l289N k m)}
    (hz : z ∈ l289PathSetP k p) : m ≤ z.val := by
  classical
  unfold l289PathSetP at hz
  split at hz
  · rename_i h
    rw [l289PathSet_mem_iff] at hz
    obtain ⟨i, hi⟩ := hz
    rw [← hi]
    exact l289Path_ge_m k (hu := h) (i := i)
  · exact absurd hz (Finset.notMem_empty z)

noncomputable def l289Oset (k : ℕ) {m : ℕ} (U : Finset (Fin (l289N k m))) : Finset (Fin m) :=
  Finset.univ.filter (fun u : Fin m => l289Orig k u ∈ U)

noncomputable def l289Zedges (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) : Finset (Fin m × Fin m) :=
  (l289Edges m H).filter (fun p : Fin m × Fin m => l289Orig k p.1 ∉ U ∧ l289Orig k p.2 ∉ U)

noncomputable def l289Oimg (k : ℕ) {m : ℕ} (U : Finset (Fin (l289N k m))) :
    Finset (Fin (l289N k m)) :=
  (l289Oset k U).image (l289Orig k)

noncomputable def l289SmallEnds (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) : Finset (Fin m) :=
  (l289Zedges k H U).image (fun p : Fin m × Fin m => p.1)

noncomputable def l289Pimg (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) : Finset (Fin (l289N k m)) :=
  (l289Edges m H).biUnion (fun p : Fin m × Fin m => U ∩ l289PathSetP k p)

noncomputable def l289SumC (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) : ℕ :=
  ∑ p ∈ l289Edges m H, (U ∩ l289PathSetP k p).card

theorem l289Oimg_card (k : ℕ) {m : ℕ} (U : Finset (Fin (l289N k m))) :
    (l289Oimg k U).card = (l289Oset k U).card := by
  classical
  rw [l289Oimg, Finset.card_image_of_injective]
  intro a b h
  exact l289Orig_inj k h

theorem l289Oimg_subset (k : ℕ) {m : ℕ} (U : Finset (Fin (l289N k m))) :
    l289Oimg k U ⊆ U := by
  classical
  intro x hx
  rw [l289Oimg, Finset.mem_image] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [l289Oset, Finset.mem_filter] at hu
  exact hu.2

theorem l289Pimg_subset (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) : l289Pimg k H U ⊆ U := by
  classical
  intro x hx
  rw [l289Pimg, Finset.mem_biUnion] at hx
  obtain ⟨p, -, hx⟩ := hx
  exact (Finset.mem_inter.mp hx).1

theorem l289Pimg_card (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) :
    (l289Pimg k H U).card = l289SumC k H U := by
  classical
  rw [l289Pimg, l289SumC]
  rw [Finset.card_biUnion]
  intro p hp q hq hpq
  obtain ⟨hpu, -⟩ := l289Edges_mem.mp hp
  obtain ⟨hqu, -⟩ := l289Edges_mem.mp hq
  show Disjoint (U ∩ l289PathSetP k p) (U ∩ l289PathSetP k q)
  rw [l289PathSetP_of_lt hpu, l289PathSetP_of_lt hqu]
  have hne : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_contra hc
    push_neg at hc
    exact hpq (Prod.ext hc.1 hc.2)
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact (Finset.disjoint_left.mp (l289PathSet_disjoint k hpu hqu hne))
    (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2

theorem l289Oimg_disjoint_Pimg (k : ℕ) {m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) : Disjoint (l289Oimg k U) (l289Pimg k H U) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [l289Oimg, Finset.mem_image] at hx
  obtain ⟨u, -, rfl⟩ := hx
  rw [l289Pimg, Finset.mem_biUnion] at hx'
  obtain ⟨p, -, hx'⟩ := hx'
  have h1 : (l289Orig k u).val < m := l289Orig_lt_m k u
  have h2 : m ≤ (l289Orig k u).val := l289PathSetP_ge_m (Finset.mem_inter.mp hx').2
  omega

theorem l289OZ_le_U_card {k m : ℕ} (H : SimpleGraph (Fin m))
    (U : Finset (Fin (l289N k m))) :
    (l289Oset k U).card + l289SumC k H U ≤ U.card := by
  classical
  have hunion : (l289Oimg k U ∪ l289Pimg k H U).card
      = (l289Oimg k U).card + (l289Pimg k H U).card :=
    Finset.card_union_of_disjoint (l289Oimg_disjoint_Pimg k H U)
  have hsub : l289Oimg k U ∪ l289Pimg k H U ⊆ U :=
    Finset.union_subset (l289Oimg_subset k U) (l289Pimg_subset k H U)
  calc (l289Oset k U).card + l289SumC k H U
      = (l289Oimg k U).card + (l289Pimg k H U).card := by
        rw [l289Oimg_card, l289Pimg_card]
    _ = (l289Oimg k U ∪ l289Pimg k H U).card := hunion.symm
    _ ≤ U.card := Finset.card_le_card hsub

end PEqualNP.Outside.LMeta289Aux

theorem PEqualNP.Outside.L_meta_289 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  intro k m H hk S hS U hcover R hR
  classical
  have hS' : S = SimpleGraph.fromRel (PEqualNP.Outside.LMeta289Aux.l289Rel k H) := hS
  have hper : ∀ p ∈ PEqualNP.Outside.LMeta289Aux.l289Edges m H,
      k + (if PEqualNP.Outside.LMeta289Aux.l289Orig k p.1 ∉ U ∧
            PEqualNP.Outside.LMeta289Aux.l289Orig k p.2 ∉ U then 1 else 0)
        ≤ (U ∩ PEqualNP.Outside.LMeta289Aux.l289PathSetP k p).card := by
    intro p hp
    by_cases hb : PEqualNP.Outside.LMeta289Aux.l289Orig k p.1 ∉ U ∧
        PEqualNP.Outside.LMeta289Aux.l289Orig k p.2 ∉ U
    · rw [if_pos hb]
      exact PEqualNP.Outside.LMeta289Aux.l289_edge_extra hk hS' hcover hp hb
    · rw [if_neg hb]
      exact PEqualNP.Outside.LMeta289Aux.l289_edge_base hk hS' hcover hp
  have hsum_split : (∑ p ∈ PEqualNP.Outside.LMeta289Aux.l289Edges m H,
        (k + (if PEqualNP.Outside.LMeta289Aux.l289Orig k p.1 ∉ U ∧
              PEqualNP.Outside.LMeta289Aux.l289Orig k p.2 ∉ U then 1 else 0)))
      = k * (PEqualNP.Outside.LMeta289Aux.l289Edges m H).card
        + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card := by
    rw [PEqualNP.Outside.LMeta289Aux.l289Zedges]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_const_nat (fun x hx => rfl)]
    rw [← Finset.card_filter]
    ring
  have hsum_ge : k * (PEqualNP.Outside.LMeta289Aux.l289Edges m H).card
      + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card
      ≤ PEqualNP.Outside.LMeta289Aux.l289SumC k H U := by
    rw [PEqualNP.Outside.LMeta289Aux.l289SumC]
    calc k * (PEqualNP.Outside.LMeta289Aux.l289Edges m H).card
          + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card
        = ∑ p ∈ PEqualNP.Outside.LMeta289Aux.l289Edges m H,
            (k + (if PEqualNP.Outside.LMeta289Aux.l289Orig k p.1 ∉ U ∧
                  PEqualNP.Outside.LMeta289Aux.l289Orig k p.2 ∉ U then 1 else 0)) :=
          hsum_split.symm
      _ ≤ ∑ p ∈ PEqualNP.Outside.LMeta289Aux.l289Edges m H,
            (U ∩ PEqualNP.Outside.LMeta289Aux.l289PathSetP k p).card :=
          Finset.sum_le_sum hper
  have hOP : (PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
      + PEqualNP.Outside.LMeta289Aux.l289SumC k H U ≤ U.card :=
    PEqualNP.Outside.LMeta289Aux.l289OZ_le_U_card H U
  have hRcard : R.card ≤ (PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
      + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card := by
    have hRsub : R ⊆ PEqualNP.Outside.LMeta289Aux.l289Oset k U
        ∪ PEqualNP.Outside.LMeta289Aux.l289SmallEnds k H U := by
      intro u hu
      have hr := (hR u).mp hu
      rcases hr with ⟨x, hxU, hxval⟩ | ⟨v, huv, hadj, hunU, hvnU⟩
      · rw [Finset.mem_union]
        left
        have hx' : x = PEqualNP.Outside.LMeta289Aux.l289Orig k u :=
          Fin.ext (by rw [PEqualNP.Outside.LMeta289Aux.l289Orig_val]; exact hxval)
        rw [hx'] at hxU
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hxU⟩
      · rw [Finset.mem_union]
        right
        refine Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨PEqualNP.Outside.LMeta289Aux.l289Edges_mem.mpr ⟨huv, hadj⟩, ?_, ?_⟩
        · intro hcon
          exact hunU (PEqualNP.Outside.LMeta289Aux.l289Orig k u) hcon (by simp)
        · intro hcon
          exact hvnU (PEqualNP.Outside.LMeta289Aux.l289Orig k v) hcon (by simp)
    have hsmall : (PEqualNP.Outside.LMeta289Aux.l289SmallEnds k H U).card
        ≤ (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card := by
      rw [PEqualNP.Outside.LMeta289Aux.l289SmallEnds]
      exact Finset.card_image_le
    calc R.card ≤ (PEqualNP.Outside.LMeta289Aux.l289Oset k U
          ∪ PEqualNP.Outside.LMeta289Aux.l289SmallEnds k H U).card :=
          Finset.card_le_card hRsub
      _ ≤ (PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
          + (PEqualNP.Outside.LMeta289Aux.l289SmallEnds k H U).card :=
          Finset.card_union_le _ _
      _ ≤ (PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
          + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card := by omega
  have hcoverH : ∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R := by
    intro u v huv
    have hne : u ≠ v := H.ne_of_adj huv
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · by_cases huU : PEqualNP.Outside.LMeta289Aux.l289Orig k u ∈ U
      · left
        rw [hR u]
        exact Or.inl ⟨PEqualNP.Outside.LMeta289Aux.l289Orig k u, huU, by simp⟩
      · by_cases hvU : PEqualNP.Outside.LMeta289Aux.l289Orig k v ∈ U
        · right
          rw [hR v]
          exact Or.inl ⟨PEqualNP.Outside.LMeta289Aux.l289Orig k v, hvU, by simp⟩
        · left
          rw [hR u]
          refine Or.inr ⟨v, hlt, huv, ?_, ?_⟩
          · intro x hx hxval
            have hx' : x = PEqualNP.Outside.LMeta289Aux.l289Orig k u :=
              Fin.ext (by rw [PEqualNP.Outside.LMeta289Aux.l289Orig_val]; exact hxval)
            rw [hx'] at hx
            exact huU hx
          · intro x hx hxval
            have hx' : x = PEqualNP.Outside.LMeta289Aux.l289Orig k v :=
              Fin.ext (by rw [PEqualNP.Outside.LMeta289Aux.l289Orig_val]; exact hxval)
            rw [hx'] at hx
            exact hvU hx
    · by_cases hvU : PEqualNP.Outside.LMeta289Aux.l289Orig k v ∈ U
      · right
        rw [hR v]
        exact Or.inl ⟨PEqualNP.Outside.LMeta289Aux.l289Orig k v, hvU, by simp⟩
      · by_cases huU : PEqualNP.Outside.LMeta289Aux.l289Orig k u ∈ U
        · left
          rw [hR u]
          exact Or.inl ⟨PEqualNP.Outside.LMeta289Aux.l289Orig k u, huU, by simp⟩
        · right
          rw [hR v]
          refine Or.inr ⟨u, hgt, H.adj_symm huv, ?_, ?_⟩
          · intro x hx hxval
            have hx' : x = PEqualNP.Outside.LMeta289Aux.l289Orig k v :=
              Fin.ext (by rw [PEqualNP.Outside.LMeta289Aux.l289Orig_val]; exact hxval)
            rw [hx'] at hx
            exact hvU hx
          · intro x hx hxval
            have hx' : x = PEqualNP.Outside.LMeta289Aux.l289Orig k u :=
              Fin.ext (by rw [PEqualNP.Outside.LMeta289Aux.l289Orig_val]; exact hxval)
            rw [hx'] at hx
            exact huU hx
  refine ⟨hcoverH, ?_⟩
  calc R.card + k * H.edgeSet.ncard
      = R.card + k * (PEqualNP.Outside.LMeta289Aux.l289Edges m H).card := by
        rw [← PEqualNP.Outside.LMeta289Aux.l289Edges_card]
    _ ≤ ((PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
          + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card)
          + k * (PEqualNP.Outside.LMeta289Aux.l289Edges m H).card := by omega
    _ = (PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
          + (k * (PEqualNP.Outside.LMeta289Aux.l289Edges m H).card
            + (PEqualNP.Outside.LMeta289Aux.l289Zedges k H U).card) := by ring
    _ ≤ (PEqualNP.Outside.LMeta289Aux.l289Oset k U).card
          + PEqualNP.Outside.LMeta289Aux.l289SumC k H U := by omega
    _ ≤ U.card := hOP
