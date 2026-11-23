import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_492_aux

lemma div_eq {d a₁ b₁ a₂ b₂ : ℕ} (hb₁ : b₁ < d) (hb₂ : b₂ < d)
    (h : d * a₁ + b₁ = d * a₂ + b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ha : a₁ = a₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : d * (a₁ + 1) ≤ d * a₂ := Nat.mul_le_mul_left d hlt
      nlinarith
    · have : d * (a₂ + 1) ≤ d * a₁ := Nat.mul_le_mul_left d hgt
      nlinarith
  subst ha
  exact ⟨rfl, by omega⟩

lemma decode_val {k m : ℕ} {u₁ v₁ u₂ v₂ : Fin m} {i₁ i₂ : Fin (2 * k)}
    (h : m + 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      m + 2 * k * (u₂.val * m + v₂.val) + i₂.val) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ i₁ = i₂ := by
  have h1 : 2 * k * (u₁.val * m + v₁.val) + i₁.val =
      2 * k * (u₂.val * m + v₂.val) + i₂.val := by omega
  obtain ⟨huv, hi⟩ := div_eq i₁.isLt i₂.isLt h1
  have huv' : m * u₁.val + v₁.val = m * u₂.val + v₂.val := by
    linarith [Nat.mul_comm u₁.val m, Nat.mul_comm u₂.val m]
  obtain ⟨hu, hv⟩ := div_eq v₁.isLt v₂.isLt huv'
  exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩

def subRel (k m : ℕ) (H : SimpleGraph (Fin m)) :
    Fin (m + 2 * k * m * m) → Fin (m + 2 * k * m * m) → Prop :=
  fun x y => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
     (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
     (i.val + 1 = 2 * k ∧ y.val = v.val))

lemma deg_le_two_of_ge {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    (x : Fin (m + 2 * k * m * m)) (hx : m ≤ x.val) :
    ((SimpleGraph.fromRel (subRel k m H)).neighborSet x).ncard ≤ 2 := by
  classical
  let S := SimpleGraph.fromRel (subRel k m H)
  by_cases hthread : ∃ (a b : Fin m) (i : Fin (2 * k)),
      a < b ∧ H.Adj a b ∧ x.val = m + 2 * k * (a.val * m + b.val) + i.val
  · obtain ⟨a, b, i, hab, hadj, hxval⟩ := hthread
    let pVal : ℕ := if i.val = 0 then a.val else m + 2 * k * (a.val * m + b.val) + (i.val - 1)
    let sVal : ℕ := if i.val + 1 = 2 * k then b.val else m + 2 * k * (a.val * m + b.val) + (i.val + 1)
    have hp_lt : pVal < m + 2 * k * m * m := by
      dsimp only [pVal]
      split_ifs with h0
      · have := a.isLt; omega
      · have := x.isLt; omega
    have hs_lt : sVal < m + 2 * k * m * m := by
      dsimp only [sVal]
      split_ifs with htop
      · have := b.isLt; omega
      · have hmul : a.val * m + b.val + 1 ≤ m * m := by
          have ha : a.val + 1 ≤ m := a.isLt
          have hb : b.val + 1 ≤ m := b.isLt
          nlinarith
        have h2k : 2 * k * (a.val * m + b.val + 1) ≤ 2 * k * (m * m) :=
          Nat.mul_le_mul_left (2 * k) hmul
        have hassoc : 2 * k * m * m = 2 * k * (m * m) := by ring
        have hexp : 2 * k * (a.val * m + b.val) + 2 * k = 2 * k * (a.val * m + b.val + 1) := by ring
        have hi := i.isLt
        omega
    let pVert : Fin (m + 2 * k * m * m) := ⟨pVal, hp_lt⟩
    let sVert : Fin (m + 2 * k * m * m) := ⟨sVal, hs_lt⟩
    have hsub : S.neighborSet x ⊆ {pVert, sVert} := by
      intro y hy
      rw [SimpleGraph.mem_neighborSet] at hy
      rw [SimpleGraph.fromRel_adj] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      obtain ⟨_, hrel | hrel⟩ := hy
      · obtain ⟨u, v, _, _, j, hx', ⟨hj0, hy'⟩ | ⟨hjlt, hy'⟩ | ⟨hjtop, hy'⟩⟩ := hrel
        · obtain ⟨rfl, rfl, rfl⟩ := decode_val (hxval.symm.trans hx')
          exact Or.inl (Fin.ext (by dsimp [pVert, pVal]; rw [if_pos hj0]; exact hy'))
        · obtain ⟨rfl, rfl, rfl⟩ := decode_val (hxval.symm.trans hx')
          exact Or.inr (Fin.ext (by dsimp [sVert, sVal]; rw [if_neg (by omega)]; exact hy'))
        · obtain ⟨rfl, rfl, rfl⟩ := decode_val (hxval.symm.trans hx')
          exact Or.inr (Fin.ext (by dsimp [sVert, sVal]; rw [if_pos hjtop]; exact hy'))
      · obtain ⟨u, v, _, _, j, hy', ⟨hj0, hx'⟩ | ⟨hjlt, hx'⟩ | ⟨hjtop, hx'⟩⟩ := hrel
        · have := u.isLt; omega
        · have hj1 : j.val + 1 < 2 * k := hjlt
          have hdec : m + 2 * k * (a.val * m + b.val) + i.val =
              m + 2 * k * (u.val * m + v.val) + (⟨j.val + 1, hj1⟩ : Fin (2 * k)).val := by
            dsimp; omega
          obtain ⟨rfl, rfl, hij⟩ := decode_val hdec
          have hival : i.val = j.val + 1 := congrArg Fin.val hij
          exact Or.inl (Fin.ext (by dsimp [pVert, pVal]; rw [if_neg (by omega)]; omega))
        · have := v.isLt; omega
    calc
      (S.neighborSet x).ncard ≤ ({pVert, sVert} : Set _).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({sVert} : Set _).ncard + 1 := Set.ncard_insert_le pVert {sVert}
      _ = 2 := by simp
  · have hempty : S.neighborSet x = ∅ := by
      ext y
      simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
      intro hadj
      rw [SimpleGraph.fromRel_adj] at hadj
      obtain ⟨_, hrel | hrel⟩ := hadj
      · obtain ⟨u, v, huv, hadjH, i, hx', _⟩ := hrel
        exact hthread ⟨u, v, i, huv, hadjH, hx'⟩
      · obtain ⟨u, v, huv, hadjH, j, _, ⟨_, hx'⟩ | ⟨hjlt, hx'⟩ | ⟨_, hx'⟩⟩ := hrel
        · have := u.isLt; omega
        · exact hthread ⟨u, v, ⟨j.val + 1, hjlt⟩, huv, hadjH, by dsimp; omega⟩
        · have := v.isLt; omega
    rw [show (SimpleGraph.fromRel (subRel k m H)).neighborSet x = ∅ from hempty]
    simp

def dist (k m : ℕ) (u w : Fin (m + 2 * k * m * m)) : ℕ :=
  if w.val < m then
    if w = u then 0 else 2 * k + 1
  else
    let q := (w.val - m) / (2 * k)
    let i := (w.val - m) % (2 * k)
    let a := q / m
    let b := q % m
    if a = u.val ∧ b ≠ u.val then i + 1
    else if b = u.val ∧ a ≠ u.val then 2 * k - i
    else 2 * k + 1

lemma dist_thread {k m : ℕ} (hk : 1 ≤ k) (u : Fin (m + 2 * k * m * m))
    (a b : Fin m) (hab : a < b) (i : Fin (2 * k))
    (w : Fin (m + 2 * k * m * m)) (hw : w.val = m + 2 * k * (a.val * m + b.val) + i.val) :
    dist k m u w =
      if a.val = u.val then i.val + 1
      else if b.val = u.val then 2 * k - i.val
      else 2 * k + 1 := by
  have hge : ¬ w.val < m := by omega
  have hsub : w.val - m = i.val + 2 * k * (a.val * m + b.val) := by omega
  have hq : (w.val - m) / (2 * k) = a.val * m + b.val := by
    rw [hsub, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt i.isLt, zero_add]
  have hi : (w.val - m) % (2 * k) = i.val := by
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  have hq' : a.val * m + b.val = b.val + m * a.val := by ring
  have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have ha : ((w.val - m) / (2 * k)) / m = a.val := by
    rw [hq, hq', Nat.add_mul_div_left _ _ hm_pos, Nat.div_eq_of_lt b.isLt, zero_add]
  have hb : ((w.val - m) / (2 * k)) % m = b.val := by
    rw [hq, hq', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
  have hab_ne : a.val ≠ b.val := ne_of_lt hab
  unfold dist
  rw [if_neg hge]
  dsimp only
  rw [ha, hb, hi]
  by_cases hau : a.val = u.val
  · have hbu : b.val ≠ u.val := by omega
    rw [if_pos ⟨hau, hbu⟩, if_pos hau]
  · rw [if_neg (fun h => hau h.1), if_neg hau]
    by_cases hbu : b.val = u.val
    · rw [if_pos ⟨hbu, hau⟩, if_pos hbu]
    · rw [if_neg (fun h => hbu h.1), if_neg hbu]

lemma dist_step_subRel {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    (u : Fin (m + 2 * k * m * m)) (x y : Fin (m + 2 * k * m * m))
    (hrel : subRel k m H x y) :
    dist k m u y ≤ dist k m u x + 1 ∧ dist k m u x ≤ dist k m u y + 1 := by
  obtain ⟨a, b, hab, _, i, hx, hcase⟩ := hrel
  have hdx := dist_thread hk u a b hab i x hx
  rcases hcase with ⟨hi0, hy⟩ | ⟨hilt, hy⟩ | ⟨hitop, hy⟩
  · have hya : y.val < m := by have := a.isLt; omega
    have hdy : dist k m u y = if a.val = u.val then 0 else 2 * k + 1 := by
      unfold dist
      rw [if_pos hya]
      by_cases hau : a.val = u.val
      · rw [if_pos (Fin.ext (by omega)), if_pos hau]
      · rw [if_neg (fun h => hau (by have := congrArg Fin.val h; omega)), if_neg hau]
    rw [hdx, hdy]
    have hab_ne : a.val ≠ b.val := ne_of_lt hab
    by_cases hau : a.val = u.val
    · rw [if_pos hau, if_pos hau]; omega
    · rw [if_neg hau, if_neg hau]
      by_cases hbu : b.val = u.val
      · rw [if_pos hbu]; omega
      · rw [if_neg hbu]; omega
  · have hdy := dist_thread hk u a b hab ⟨i.val + 1, hilt⟩ y (by dsimp; omega)
    rw [hdx, hdy]
    dsimp only
    by_cases hau : a.val = u.val
    · rw [if_pos hau, if_pos hau]; omega
    · rw [if_neg hau, if_neg hau]
      by_cases hbu : b.val = u.val
      · rw [if_pos hbu, if_pos hbu]; omega
      · rw [if_neg hbu, if_neg hbu]; omega
  · have hyb : y.val < m := by have := b.isLt; omega
    have hdy : dist k m u y = if b.val = u.val then 0 else 2 * k + 1 := by
      unfold dist
      rw [if_pos hyb]
      by_cases hbu : b.val = u.val
      · rw [if_pos (Fin.ext (by omega)), if_pos hbu]
      · rw [if_neg (fun h => hbu (by have := congrArg Fin.val h; omega)), if_neg hbu]
    rw [hdx, hdy]
    have hab_ne : a.val ≠ b.val := ne_of_lt hab
    by_cases hau : a.val = u.val
    · have hbu : b.val ≠ u.val := by omega
      rw [if_pos hau, if_neg hbu]; omega
    · rw [if_neg hau]
      by_cases hbu : b.val = u.val
      · rw [if_pos hbu, if_pos hbu]; omega
      · rw [if_neg hbu, if_neg hbu]; omega

lemma dist_walk {k m : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k)
    (u : Fin (m + 2 * k * m * m)) {x y : Fin (m + 2 * k * m * m)}
    (p : (SimpleGraph.fromRel (subRel k m H)).Walk x y) :
    dist k m u y ≤ dist k m u x + p.length := by
  induction p with
  | nil => simp
  | @cons x z y hadj q ih =>
    rw [SimpleGraph.fromRel_adj] at hadj
    have hstep : dist k m u z ≤ dist k m u x + 1 := by
      rcases hadj.2 with hrel | hrel
      · exact (dist_step_subRel hk u x z hrel).1
      · exact (dist_step_subRel hk u z x hrel).2
    simp only [SimpleGraph.Walk.length_cons]
    omega

end PEqualNP.Outside.L_meta_492_aux

theorem PEqualNP.Outside.L_meta_492 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
            x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
            ((i.val = 0 ∧ y.val = u.val) ∨
             (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
             (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        ∀ u v : Fin (m + 2 * k * m * m),
          u ≠ v →
          3 ≤ (S.neighborSet u).ncard →
          3 ≤ (S.neighborSet v).ncard →
          ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length := by
  intro k m H hk S hS u v huv hdu hdv p
  subst hS
  have hu_lt : u.val < m := by
    by_contra hge
    have hle := PEqualNP.Outside.L_meta_492_aux.deg_le_two_of_ge (H := H) hk u (by omega)
    exact Nat.not_le_of_gt (by omega : 2 < 3) (le_trans hdu hle)
  have hv_lt : v.val < m := by
    by_contra hge
    have hle := PEqualNP.Outside.L_meta_492_aux.deg_le_two_of_ge (H := H) hk v (by omega)
    exact Nat.not_le_of_gt (by omega : 2 < 3) (le_trans hdv hle)
  have hwalk := PEqualNP.Outside.L_meta_492_aux.dist_walk (H := H) hk u p
  have hdu0 : PEqualNP.Outside.L_meta_492_aux.dist k m u u = 0 := by
    unfold PEqualNP.Outside.L_meta_492_aux.dist
    rw [if_pos hu_lt, if_pos rfl]
  have hdv1 : PEqualNP.Outside.L_meta_492_aux.dist k m u v = 2 * k + 1 := by
    unfold PEqualNP.Outside.L_meta_492_aux.dist
    rw [if_pos hv_lt, if_neg huv.symm]
  rw [hdu0, hdv1, zero_add] at hwalk
  exact hwalk
