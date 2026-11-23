import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

namespace Subdivision281
private abbrev V (m l : ℕ) := Fin (m + l * m * m)
private def idx {m l : ℕ} (u v : Fin m) (i : Fin l) := m + l * (u.val * m + v.val) + i.val

private theorem pack {n a b c d : ℕ} (hb : b < n) (hd : d < n)
    (h : n * a + b = n * c + d) : a = c ∧ b = d := by
  have h₁ : a = c := by
    rcases lt_trichotomy a c with hac | hac | hac
    · have hh := Nat.mul_le_mul_left n (show a + 1 ≤ c by omega)
      rw [Nat.mul_succ] at hh
      omega
    · exact hac
    · have hh := Nat.mul_le_mul_left n (show c + 1 ≤ a by omega)
      rw [Nat.mul_succ] at hh
      omega
  subst c
  exact ⟨rfl, by omega⟩

private theorem idx_inj {m l : ℕ} {u v a b : Fin m} {i j : Fin l}
    (h : idx u v i = idx a b j) : u = a ∧ v = b ∧ i = j := by
  unfold idx at h
  have ⟨hp, hi⟩ := pack i.isLt j.isLt (show l * (u.val*m+v.val) + i.val =
    l * (a.val*m+b.val) + j.val by omega)
  rw [Nat.mul_comm u.val m, Nat.mul_comm a.val m] at hp
  obtain ⟨hu,hv⟩ := pack v.isLt b.isLt hp
  exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩

private def orig {m : ℕ} (l : ℕ) (u : Fin m) : V m l := ⟨u.val, by have := u.isLt; omega⟩
private def node {m l : ℕ} (u v : Fin m) (i : Fin l) : V m l :=
  ⟨idx u v i, by
    have h₁ := Nat.mul_le_mul_right m (show u.val+1 ≤ m by exact u.isLt)
    rw [Nat.succ_mul] at h₁
    have h₂ := Nat.mul_le_mul_left l (show (u.val*m+v.val)+1 ≤ m*m by have := v.isLt; omega)
    rw [Nat.mul_succ, ← Nat.mul_assoc] at h₂
    unfold idx
    have := i.isLt
    omega⟩

private theorem node_inj {m l : ℕ} {u v a b : Fin m} {i j : Fin l}
    (h : node u v i = node a b j) : u = a ∧ v = b ∧ i = j :=
  idx_inj (congrArg Fin.val h)

private theorem orig_ne {m l : ℕ} (a u v : Fin m) (i : Fin l) : orig l a ≠ node u v i := by
  intro h
  have hh := congrArg Fin.val h
  change a.val = m + l * (u.val*m+v.val) + i.val at hh
  have := a.isLt
  omega

private def rel {m : ℕ} (H : SimpleGraph (Fin m)) (l : ℕ) (x y : V m l) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin l, x.val = idx u v i ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
    (i.val + 1 < l ∧ y.val = idx u v i + 1) ∨ (i.val + 1 = l ∧ y.val = v.val))

private def label {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (l : ℕ) (x : V m l) : ℕ :=
  ∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin l,
    if u < v ∧ H.Adj u v ∧ x.val = idx u v i then i.val + 1 else 0

private theorem label_node {m l : ℕ} {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    {a b : Fin m} (hab : a < b) (he : H.Adj a b) (j : Fin l) :
    label H l (node a b j) = j.val + 1 := by
  have term (u v : Fin m) (i : Fin l) :
      (if u < v ∧ H.Adj u v ∧ (node a b j).val = idx u v i then i.val+1 else 0) =
      (if u = a then if v = b then if i = j then j.val+1 else 0 else 0 else 0) := by
    have hiff : (node a b j).val = idx u v i ↔ u = a ∧ v = b ∧ i = j := by
      constructor
      · intro h
        obtain ⟨hu,hv,hi⟩ := idx_inj (show idx a b j = idx u v i from h)
        exact ⟨hu.symm,hv.symm,hi.symm⟩
      · rintro ⟨rfl,rfl,rfl⟩
        rfl
    simp only [hiff]
    split_ifs <;> simp_all
  simp [label, term, Finset.sum_ite_irrel]

private theorem label_other {m l : ℕ} {H : SimpleGraph (Fin m)} [DecidableRel H.Adj]
    (x : V m l) (hn : ¬ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin l, x = node u v i) :
    label H l x = 0 := by
  have hh (u v : Fin m) (i : Fin l) : ¬ (u < v ∧ H.Adj u v ∧ x.val = idx u v i) :=
    fun h => hn ⟨u,v,h.1,h.2.1,i,Fin.ext h.2.2⟩
  simp [label, hh]

private theorem label_orig {m l : ℕ} {H : SimpleGraph (Fin m)} [DecidableRel H.Adj] (a : Fin m) :
    label H l (orig l a) = 0 := by
  apply label_other
  rintro ⟨u,v,_,_,i,hi⟩
  exact orig_ne a u v i hi

private def prev {m l : ℕ} (u v : Fin m) (i : Fin l) : V m l :=
  if h : i.val = 0 then orig l u else node u v ⟨i.val-1, by have := i.isLt; omega⟩

private def next {m l : ℕ} (u v : Fin m) (i : Fin l) : V m l :=
  if h : i.val+1 < l then node u v ⟨i.val+1,h⟩ else orig l v

private theorem inside_edge {m l : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m}
    (huv : u < v) (he : H.Adj u v) (i j : Fin l) (hij : j.val = i.val+1) :
    (SimpleGraph.fromRel (rel H l)).Adj (node u v i) (node u v j) := by
  constructor
  · intro h
    have hij' := congrArg Fin.val (node_inj h).2.2
    omega
  · exact Or.inl ⟨u,v,huv,he,i,rfl,Or.inr (Or.inl ⟨by have := j.isLt; omega,
      by simp [node,idx,hij,Nat.add_assoc]⟩)⟩

private theorem prev_adj {m l : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m}
    (huv : u < v) (he : H.Adj u v) (i : Fin l) :
    (SimpleGraph.fromRel (rel H l)).Adj (node u v i) (prev u v i) := by
  unfold prev
  split
  next h => exact ⟨(orig_ne u u v i).symm, Or.inl ⟨u,v,huv,he,i,rfl,Or.inl ⟨h,rfl⟩⟩⟩
  next h => exact (inside_edge huv he _ _ (by dsimp; omega)).symm

private theorem next_adj {m l : ℕ} {H : SimpleGraph (Fin m)} {u v : Fin m}
    (huv : u < v) (he : H.Adj u v) (i : Fin l) :
    (SimpleGraph.fromRel (rel H l)).Adj (node u v i) (next u v i) := by
  unfold next
  split
  next h => exact inside_edge huv he _ _ rfl
  next h =>
    exact ⟨(orig_ne v u v i).symm, Or.inl ⟨u,v,huv,he,i,rfl,
      Or.inr (Or.inr ⟨by have := i.isLt; omega, rfl⟩)⟩⟩

private theorem only_neighbors {m l : ℕ} {H : SimpleGraph (Fin m)} (u v : Fin m)
    (i : Fin l) (w : V m l) (hw : (SimpleGraph.fromRel (rel H l)).Adj (node u v i) w) :
    w = prev u v i ∨ w = next u v i := by
  rcases hw.2 with hw | hw
  · obtain ⟨a,b,_,_,j,hx,hw⟩ := hw
    obtain ⟨ha,hb,hj⟩ := idx_inj (show idx u v i = idx a b j from hx)
    subst a
    subst b
    subst j
    rcases hw with ⟨hz,hy⟩ | ⟨hs,hy⟩ | ⟨hl,hy⟩
    · left
      rw [prev, dif_pos hz]
      exact Fin.ext hy
    · right
      rw [next, dif_pos hs]
      apply Fin.ext
      simpa [node,idx,Nat.add_assoc] using hy
    · right
      rw [next, dif_neg (show ¬ i.val+1 < l by omega)]
      exact Fin.ext hy
  · obtain ⟨a,b,_,_,j,hx,hy⟩ := hw
    rcases hy with ⟨_,hy⟩ | ⟨hs,hy⟩ | ⟨_,hy⟩
    · exact False.elim (orig_ne a u v i (Fin.ext hy.symm))
    · let t : Fin l := ⟨j.val+1,hs⟩
      have hh : idx u v i = idx a b t := by
        change idx u v i = idx a b j + 1 at hy
        simpa [idx,t,Nat.add_assoc] using hy
      obtain ⟨ha,hb,hi⟩ := idx_inj hh
      subst a
      subst b
      have hval : i.val = j.val+1 := congrArg Fin.val hi
      left
      rw [prev, dif_neg (show i.val ≠ 0 by omega)]
      apply Fin.ext
      simpa [node,idx,hval] using hx
    · exact False.elim (orig_ne b u v i (Fin.ext hy.symm))

private theorem solve (l m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    (∀ x y, (SimpleGraph.fromRel (rel H l)).Adj x y →
      label H l x ≠ 0 ∨ label H l y ≠ 0) ∧
    ∀ x, label H l x ≠ 0 → label H l x ≤ l ∧ ∃ a b : V m l,
      (∀ w, (SimpleGraph.fromRel (rel H l)).Adj x w ↔ w = a ∨ w = b) ∧
      label H l a + 1 = label H l x ∧ label H l b = (label H l x + 1) % (l+1) := by
  have source (x y : V m l) (h : rel H l x y) : label H l x ≠ 0 := by
    obtain ⟨u,v,huv,he,i,hx,_⟩ := h
    rw [show x = node u v i from Fin.ext hx,label_node huv he]
    omega
  constructor
  · intro x y h
    exact h.2.imp (source x y) (source y x)
  · intro x hx
    have hex : ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin l, x = node u v i := by
      by_contra hn
      exact hx (label_other x hn)
    obtain ⟨u,v,huv,he,i,rfl⟩ := hex
    rw [label_node huv he]
    refine ⟨i.isLt,prev u v i,next u v i,?_,?_,?_⟩
    · intro w
      exact ⟨only_neighbors u v i w, fun h => h.elim
        (fun e => e ▸ prev_adj huv he i) (fun e => e ▸ next_adj huv he i)⟩
    · unfold prev
      split
      next h => rw [label_orig,h]
      next h => rw [label_node huv he]; dsimp; omega
    · unfold next
      split
      next h => rw [label_node huv he,Nat.mod_eq_of_lt (by omega)]
      next h => rw [label_orig,show i.val+1+1 = l+1 by have := i.isLt; omega,Nat.mod_self]

end Subdivision281

theorem PEqualNP.Outside.L_meta_281 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ pos : Fin (m + 2 * k * m * m) → ℕ, (∀ j : Fin (m + 2 * k * m * m), pos j = ∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k), if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val then i.val + 1 else 0) → (∀ u v : Fin (m + 2 * k * m * m), S.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin (m + 2 * k * m * m), pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin (m + 2 * k * m * m), (∀ w : Fin (m + 2 * k * m * m), S.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1) := by
  intro k m H inst hk S hS pos hpos
  subst S
  have hp : pos = Subdivision281.label H (2*k) := funext hpos
  rw [hp]
  exact Subdivision281.solve (2*k) m H
