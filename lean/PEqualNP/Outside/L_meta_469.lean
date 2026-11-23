import Mathlib
import PEqualNP.Defs

private lemma end469 {w i n r : ℕ} (hi : i < n) (hr : r < w) :
    w*i+r < w*n := by
  have h := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at h
  omega

private lemma block469 {w a b i j : ℕ} (hi : i < w) (hj : j < w)
    (h : w*a+i = w*b+j) : a = b ∧ i = j := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hl | he | hg
    · have := end469 hl hi
      omega
    · exact he
    · have := end469 hg hj
      omega
  subst b
  exact ⟨rfl, by omega⟩

private lemma card_ordered_adj_eq_edgeSet_ncard {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    ((Finset.univ : Finset (Fin m × Fin m)).filter
      (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2)).card = H.edgeSet.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  refine Finset.card_bij (fun e _ => s(e.1, e.2)) ?_ ?_ ?_
  · intro e he
    exact Set.mem_toFinset.mpr (H.mem_edgeSet.mpr (Finset.mem_filter.mp he).2.2)
  · intro a ha b hb he
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext h.1 h.2
    · have ha' := (Finset.mem_filter.mp ha).2.1
      have hb' := (Finset.mem_filter.mp hb).2.1
      rw [h.1, h.2] at ha'
      exact (lt_asymm hb' ha').elim
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      have hab := H.mem_edgeSet.mp (Set.mem_toFinset.mp he)
      rcases lt_or_gt_of_ne hab.ne with h | h
      · exact ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hab⟩, rfl⟩
      · exact ⟨(b,a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hab.symm⟩,
          Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩

theorem PEqualNP.Outside.L_meta_469 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro m k H T T' hT
  let D := Finset.univ.filter fun e : Fin m × Fin m => e.1 < e.2 ∧ H.Adj e.1 e.2
  let bit (u : Fin m) : ℕ := if u ∈ T then 1 else 0
  have hbit (u : Fin m) : bit u ≤ 1 := by simp [bit]; split <;> omega
  have hbmem (u : Fin m) : bit u = 1 ↔ u ∈ T := by simp [bit]
  let old (u : Fin m) : Fin (m + 2*k*(m*m)) := ⟨u.val, by have := u.isLt; omega⟩
  let new (z : (Fin m × Fin m) × Fin k) : Fin (m + 2*k*(m*m)) :=
    ⟨m + 2*k*(z.1.1.val*m+z.1.2.val) + (2*z.2.val + bit z.1.1), by
      have hid : z.1.1.val*m+z.1.2.val < m*m := by
        simpa only [Nat.mul_comm m z.1.1.val] using end469 z.1.1.isLt z.1.2.isLt
      have h := end469 hid (show 2*z.2.val+bit z.1.1 < 2*k by
        have := z.2.isLt; have := hbit z.1.1; omega)
      omega⟩
  have hnew : Function.Injective new := by
    rintro ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩ he
    have hx := congrArg Fin.val he
    change m+2*k*(a.val*m+b.val)+(2*i.val+bit a) =
      m+2*k*(c.val*m+d.val)+(2*j.val+bit c) at hx
    have h1 : 2*i.val+bit a < 2*k := by have := i.isLt; have := hbit a; omega
    have h2 : 2*j.val+bit c < 2*k := by have := j.isLt; have := hbit c; omega
    obtain ⟨hid,hoff⟩ := block469 h1 h2 (by omega :
      2*k*(a.val*m+b.val)+(2*i.val+bit a) =
      2*k*(c.val*m+d.val)+(2*j.val+bit c))
    rw [Nat.mul_comm a.val m,Nat.mul_comm c.val m] at hid
    obtain ⟨hu,hv⟩ := block469 b.isLt d.isLt hid
    obtain rfl := Fin.ext hu
    obtain rfl := Fin.ext hv
    obtain rfl : i = j := Fin.ext (by omega)
    rfl
  let Z := D ×ˢ (Finset.univ : Finset (Fin k))
  have hZ (e : Fin m × Fin m) (i : Fin k) :
      (e,i) ∈ Z ↔ e.1 < e.2 ∧ H.Adj e.1 e.2 := by simp [Z,D]
  have dis : Disjoint (T.image old) (Z.image new) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨⟨u,v⟩,j⟩,_,he⟩ := Finset.mem_image.mp hy
    have hv := congrArg Fin.val he
    change m+2*k*(u.val*m+v.val)+(2*j.val+bit u) = a.val at hv
    have := a.isLt
    omega
  have eqSets : T' = T.image old ∪ Z.image new := by
    ext x
    rw [hT, Finset.mem_union]
    constructor
    · rintro (⟨u,hu,hx⟩ | ⟨u,v,i,hi,huv,hadj,hx,hp⟩)
      · exact Or.inl (Finset.mem_image.mpr ⟨u,hu,Fin.ext hx.symm⟩)
      · let j : Fin k := ⟨i/2,by omega⟩
        have hh : i = 2*j.val + bit u := by
          change i = 2*(i/2)+bit u
          by_cases h : u ∈ T
          · have := hp.mpr h; simp [bit,h]; omega
          · have : i % 2 ≠ 1 := fun ht => h (hp.mp ht)
            simp [bit,h]; omega
        exact Or.inr (Finset.mem_image.mpr ⟨((u,v),j),(hZ _ _).mpr ⟨huv,hadj⟩,
          Fin.ext (by change m+2*k*(u.val*m+v.val)+(2*j.val+bit u) = x.val; omega)⟩)
    · rintro (ha | hb)
      · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
        exact Or.inl ⟨u,hu,rfl⟩
      · obtain ⟨⟨⟨u,v⟩,j⟩,hz,rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨huv,hadj⟩ := (hZ (u,v) j).mp hz
        refine Or.inr ⟨u,v,2*j.val+bit u,?_,huv,hadj,rfl,?_⟩
        · have := j.isLt; have := hbit u; omega
        · rw [← hbmem u]; have := hbit u; omega
  have hold : Function.Injective old := by
    intro a b h
    have hh := congrArg Fin.val h
    exact Fin.ext hh
  rw [eqSets,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ hold,
    Finset.card_image_of_injective _ hnew]
  change T.card + (D ×ˢ (Finset.univ : Finset (Fin k))).card = _
  rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]
  have hD : D.card = H.edgeSet.ncard := card_ordered_adj_eq_edgeSet_ncard H
  rw [hD,Nat.mul_comm H.edgeSet.ncard k]
