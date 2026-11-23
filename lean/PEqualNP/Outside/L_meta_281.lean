import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Subdivision281

private abbrev V (m p : ℕ) := Fin (m + p * m * m)

private def code {m : ℕ} (p : ℕ) (a b : Fin m) (i : ℕ) :=
  m + p * (a.val * m + b.val) + i

private theorem block_lt {r n a b : ℕ} (ha : a < n) (hb : b < r) :
    r * a + b < r * n := by
  have h := Nat.mul_le_mul_left r (show a + 1 ≤ n from ha)
  rw [Nat.mul_succ] at h
  omega

private def mid {m p : ℕ} (a b : Fin m) (i : Fin p) : V m p :=
  ⟨code p a b i, by
    have h := block_lt a.isLt b.isLt
    rw [Nat.mul_comm m a.val] at h
    have h' := block_lt h i.isLt
    simpa [code, Nat.mul_assoc, Nat.add_assoc] using Nat.add_lt_add_left h' m⟩

private def hub {m p : ℕ} (a : Fin m) : V m p := ⟨a, by have := a.isLt; omega⟩

private theorem unpack {r x y i j : ℕ} (hi : i < r) (hj : j < r)
    (h : r * x + i = r * y + j) : x = y ∧ i = j := by
  have he := congrArg (· / r) h
  have hr := congrArg (· % r) h
  have hp : 0 < r := by omega
  exact ⟨by simpa [Nat.mul_add_div hp, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] using he,
    by simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hr⟩

private theorem code_eq {m p : ℕ} {a b c d : Fin m} {i j : Fin p} :
    code p a b i = code p c d j ↔ a = c ∧ b = d ∧ i = j := by
  constructor
  · intro h
    unfold code at h
    simp only [Nat.add_assoc, Nat.add_right_inj] at h
    obtain ⟨hpair, hij⟩ := unpack i.isLt j.isLt h
    rw [Nat.mul_comm a.val m, Nat.mul_comm c.val m] at hpair
    obtain ⟨hac, hbd⟩ := unpack b.isLt d.isLt hpair
    exact ⟨Fin.ext hac, Fin.ext hbd, Fin.ext hij⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

private theorem mid_eq {m p : ℕ} {a b c d : Fin m} {i j : Fin p} :
    mid a b i = mid c d j ↔ a = c ∧ b = d ∧ i = j :=
  Fin.ext_iff.trans code_eq

private theorem mid_ne_hub {m p : ℕ} (a b c : Fin m) (i : Fin p) : mid a b i ≠ hub c := by
  intro h
  have he : code p a b i = c.val := congrArg Fin.val h
  unfold code at he
  have := c.isLt
  omega

private def right {m p : ℕ} (a b : Fin m) (i : Fin p) : V m p :=
  if h : i.val + 1 < p then mid a b ⟨i.val + 1,h⟩ else hub b

private def left {m p : ℕ} (a b : Fin m) (i : Fin p) : V m p :=
  if h : i.val = 0 then hub a else mid a b ⟨i.val - 1, by have := i.isLt; omega⟩

private def link {m p : ℕ} (G : SimpleGraph (Fin m)) (x y : V m p) : Prop :=
  ∃ a b : Fin m, a < b ∧ G.Adj a b ∧ ∃ i : Fin p,
    x = mid a b i ∧ ((i.val = 0 ∧ y = hub a) ∨ y = right a b i)

private theorem link_mid {m p : ℕ} {G : SimpleGraph (Fin m)} {a b : Fin m}
    (hab : a < b) (he : G.Adj a b) (i : Fin p) (w : V m p) :
    (link G (mid a b i) w ∨ link G w (mid a b i)) ↔
      w = left a b i ∨ w = right a b i := by
  constructor
  · rintro (⟨c,d,_,_,j,hm,h⟩ | ⟨c,d,_,_,j,rfl,h⟩)
    · obtain ⟨rfl,rfl,rfl⟩ := mid_eq.mp hm
      rcases h with ⟨hi,rfl⟩ | hr
      · exact Or.inl (by simp [left, hi])
      · exact Or.inr hr
    · rcases h with ⟨_,hm⟩ | hm
      · exact (mid_ne_hub _ _ _ _ hm).elim
      · unfold right at hm
        split at hm
        next hj =>
          obtain ⟨rfl,rfl,hi⟩ := mid_eq.mp hm
          have hij := congrArg Fin.val hi
          change i.val = j.val + 1 at hij
          left
          unfold left
          split
          · omega
          · exact mid_eq.mpr ⟨rfl,rfl,Fin.ext (by simp [hij])⟩
        next => exact (mid_ne_hub _ _ _ _ hm).elim
  · rintro (rfl | rfl)
    · unfold left
      split
      next hi => exact Or.inl ⟨a,b,hab,he,i,rfl,Or.inl ⟨hi,rfl⟩⟩
      next hi =>
        let j : Fin p := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hj : j.val + 1 = i.val := by dsimp [j]; omega
        right
        refine ⟨a,b,hab,he,j,rfl,Or.inr ?_⟩
        unfold right
        split
        · exact mid_eq.mpr ⟨rfl,rfl,Fin.ext hj.symm⟩
        · have := i.isLt; omega
    · exact Or.inl ⟨a,b,hab,he,i,rfl,Or.inr rfl⟩

private def raw {m p : ℕ} (G : SimpleGraph (Fin m)) (x y : V m p) : Prop :=
  ∃ a b : Fin m, a < b ∧ G.Adj a b ∧ ∃ i : Fin p,
    x.val = code p a b i ∧ ((i.val = 0 ∧ y.val = a.val) ∨
      (i.val + 1 < p ∧ y.val = code p a b i + 1) ∨ (i.val + 1 = p ∧ y.val = b.val))

private theorem raw_iff {m p : ℕ} (G : SimpleGraph (Fin m)) (x y : V m p) :
    raw G x y ↔ link G x y := by
  constructor
  · rintro ⟨a,b,hab,he,i,hx,h⟩
    refine ⟨a,b,hab,he,i,Fin.ext hx,?_⟩
    rcases h with ⟨hi,hy⟩ | ⟨hi,hy⟩ | ⟨hi,hy⟩
    · exact Or.inl ⟨hi,Fin.ext hy⟩
    · right
      rw [right, dite_eq_left hi]
      exact Fin.ext (by simpa [mid, code, Nat.add_assoc] using hy)
    · right
      rw [right, dite_eq_right (by omega)]
      exact Fin.ext hy
  · rintro ⟨a,b,hab,he,i,rfl,h⟩
    refine ⟨a,b,hab,he,i,rfl,?_⟩
    rcases h with ⟨hi,rfl⟩ | rfl
    · exact Or.inl ⟨hi,rfl⟩
    · unfold right
      split
      next hi => exact Or.inr (Or.inl ⟨hi, by simp [mid, code, Nat.add_assoc]⟩)
      next hi => exact Or.inr (Or.inr ⟨by have := i.isLt; omega,rfl⟩)

private def label {m p : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (x : V m p) : ℕ :=
  ∑ a : Fin m, ∑ b : Fin m, ∑ i : Fin p,
    if a < b ∧ G.Adj a b ∧ x.val = code p a b i then i.val + 1 else 0

private theorem label_hub {m p : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (a : Fin m) :
    label G (hub (p := p) a) = 0 := by
  unfold label
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun h => mid_ne_hub b c a i (Fin.ext h.2.2.symm))

private theorem label_mid {m p : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {a b : Fin m} (hab : a < b) (he : G.Adj a b) (i : Fin p) :
    label G (mid a b i) = i.val + 1 := by
  unfold label
  change (∑ c : Fin m, ∑ d : Fin m, ∑ j : Fin p,
    if c < d ∧ G.Adj c d ∧ code p a b i = code p c d j then j.val + 1 else 0) = _
  simp_rw [code_eq]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hab, he]
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

private theorem locate {m p : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {x : V m p} (hx : label G x ≠ 0) :
    ∃ a b : Fin m, a < b ∧ G.Adj a b ∧ ∃ i : Fin p, x = mid a b i := by
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (fun h => hn ⟨a,b,h.1,h.2.1,i,Fin.ext h.2.2⟩)

private theorem left_label {m p : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {a b : Fin m} (hab : a < b) (he : G.Adj a b) (i : Fin p) :
    label G (left a b i) + 1 = i.val + 1 := by
  unfold left
  split
  next hi => simp [label_hub, hi]
  next hi =>
    rw [label_mid hab he]
    change i.val - 1 + 1 + 1 = i.val + 1
    omega

private theorem right_label {m p : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    {a b : Fin m} (hab : a < b) (he : G.Adj a b) (i : Fin p) :
    label G (right a b i) = (i.val + 1 + 1) % (p + 1) := by
  unfold right
  split
  next hi => rw [label_mid hab he, Nat.mod_eq_of_lt (by omega)]
  next hi =>
    have hi' : i.val + 1 = p := by have := i.isLt; omega
    simp [label_hub, hi']

private theorem mid_ne_right {m p : ℕ} (a b : Fin m) (i : Fin p) : mid a b i ≠ right a b i := by
  unfold right
  split
  · intro h
    have hh := congrArg Fin.val (mid_eq.mp h).2.2
    change i.val = i.val + 1 at hh
    omega
  · exact mid_ne_hub _ _ _ _

end PEqualNP.Outside.Subdivision281

open PEqualNP.Outside.Subdivision281

theorem PEqualNP.Outside.L_meta_281 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], 1 ≤ k →
    ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
    S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
      ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
        x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
        ((i.val = 0 ∧ y.val = u.val) ∨
          (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
          (i.val + 1 = 2 * k ∧ y.val = v.val))) →
    ∀ pos : Fin (m + 2 * k * m * m) → ℕ,
    (∀ j : Fin (m + 2 * k * m * m), pos j = ∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k),
      if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val
      then i.val + 1 else 0) →
    (∀ u v : Fin (m + 2 * k * m * m), S.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧
    ∀ v : Fin (m + 2 * k * m * m), pos v ≠ 0 → pos v ≤ 2 * k ∧
      ∃ a b : Fin (m + 2 * k * m * m),
        (∀ w : Fin (m + 2 * k * m * m), S.Adj v w ↔ w = a ∨ w = b) ∧
        pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1) := by
  intro k m H _ _ S hS pos hp
  change S = SimpleGraph.fromRel (raw (p := 2 * k) H) at hS
  change ∀ j, pos j = label H j at hp
  have adj (x y : V m (2 * k)) :
      S.Adj x y ↔ x ≠ y ∧ (link H x y ∨ link H y x) := by
    rw [hS, SimpleGraph.fromRel_adj, raw_iff, raw_iff]
  have source (x y : V m (2 * k)) (h : link H x y) : pos x ≠ 0 := by
    obtain ⟨a,b,hab,he,i,rfl,_⟩ := h
    rw [hp, label_mid hab he]
    omega
  constructor
  · intro x y h
    exact ((adj x y).mp h).2.imp (source x y) (source y x)
  · intro x hx
    rw [hp] at hx
    obtain ⟨a,b,hab,he,i,rfl⟩ := locate hx
    have hm := label_mid hab he i
    have hl := left_label hab he i
    have hr := right_label hab he i
    refine ⟨by rw [hp, hm]; have := i.isLt; omega, left a b i, right a b i, ?_, ?_, ?_⟩
    · intro w
      rw [adj, link_mid hab he]
      refine ⟨And.right, fun h => ⟨?_, h⟩⟩
      rcases h with rfl | rfl
      · intro eq
        rw [← eq, hm] at hl
        omega
      · exact mid_ne_right a b i
    · simpa only [hp, hm] using hl
    · simpa only [hp, hm] using hr
