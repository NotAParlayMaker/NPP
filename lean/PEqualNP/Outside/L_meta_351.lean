import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_351

lemma val_mono {n b : ℕ} (PV RV : Fin b → Finset (Fin n))
    (PG RG : Fin b → Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop)
    (hPG : ∀ i : Fin b, ∀ j ∈ PG i, j < i)
    (hRG : ∀ i : Fin b, ∀ j ∈ RG i, j < i)
    (hval : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
        ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j)))
    {X Y : Finset (Fin n)} (hXY : X ⊆ Y) :
    ∀ i : Fin b, val X i → val Y i := by
  intro i
  induction i using Fin.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [hval X i] at hi
    rw [hval Y i]
    constructor
    · rcases hi.1 with ⟨v, hv, hvX⟩ | ⟨j, hj, hjv⟩
      · exact Or.inl ⟨v, hv, hXY hvX⟩
      · exact Or.inr ⟨j, hj, ih j (hPG i j hj) hjv⟩
    · rcases hi.2 with ⟨v, hv, hvX⟩ | ⟨j, hj, hjv⟩
      · exact Or.inl ⟨v, hv, hXY hvX⟩
      · exact Or.inr ⟨j, hj, ih j (hRG i j hj) hjv⟩

lemma delivery_p {n b : ℕ} (G : SimpleGraph (Fin n))
    (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b))
    (OV : Finset (Fin n)) (OG : Finset (Fin b))
    (val : Finset (Fin n) → Fin b → Prop)
    (hPG : ∀ i : Fin b, ∀ j ∈ PG i, j < i)
    (hRG : ∀ i : Fin b, ∀ j ∈ RG i, j < i)
    (hval : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
        ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j)))
    (hout : ∀ X : Finset (Fin n),
      ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔
        ∃ a ∈ X, ∃ c ∈ X, G.Adj a c)
    (hOV : OV = ∅) (H g : Fin b) (u : Fin n) (I : Finset (Fin n))
    (huRV : u ∉ RV g)
    (hu : ∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H)
    (hInd : ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c)
    (hedge : ∃ w ∈ I, G.Adj u w) (hIH : val I H) :
    ¬ val I g ∧ ((∃ v ∈ RV g, v ∈ I) ∨ ∃ j ∈ RG g, val I j) := by
  have hsub : I ⊆ insert u I := Finset.subset_insert u I
  have hIH' : val (insert u I) H := val_mono PV RV PG RG val hPG hRG hval hsub H hIH
  have hPdirect (i : Fin b) (hig : i ≠ g) (hiH : i ≠ H) :
      (∃ v ∈ PV i, v ∈ I) ↔ ∃ v ∈ PV i, v ∈ insert u I := by
    have hui : u ∉ PV i := by
      intro hui
      rcases hu i (Or.inl hui) with h | h
      · exact hig h
      · exact hiH h
    constructor
    · rintro ⟨v, hv, hvI⟩
      exact ⟨v, hv, Finset.mem_insert_of_mem hvI⟩
    · rintro ⟨v, hv, hvI⟩
      rcases Finset.mem_insert.mp hvI with rfl | hvI
      · exact (hui hv).elim
      · exact ⟨v, hv, hvI⟩
  have hRdirect (i : Fin b) (hig : i ≠ g) (hiH : i ≠ H) :
      (∃ v ∈ RV i, v ∈ I) ↔ ∃ v ∈ RV i, v ∈ insert u I := by
    have hui : u ∉ RV i := by
      intro hui
      rcases hu i (Or.inr hui) with h | h
      · exact hig h
      · exact hiH h
    constructor
    · rintro ⟨v, hv, hvI⟩
      exact ⟨v, hv, Finset.mem_insert_of_mem hvI⟩
    · rintro ⟨v, hv, hvI⟩
      rcases Finset.mem_insert.mp hvI with rfl | hvI
      · exact (hui hv).elim
      · exact ⟨v, hv, hvI⟩
  rcases hedge with ⟨w, hwI, huw⟩
  have hchange : ¬ (val I g ↔ val (insert u I) g) := by
    intro hg
    have hall : ∀ i : Fin b, val I i ↔ val (insert u I) i := by
      intro i
      induction i using Fin.strong_induction_on with
      | _ i ih =>
        by_cases hig : i = g
        · subst i
          exact hg
        by_cases hiH : i = H
        · subst i
          exact iff_of_true hIH hIH'
        rw [hval I i, hval (insert u I) i]
        apply and_congr
        · apply or_congr
          · exact hPdirect i hig hiH
          · constructor
            · rintro ⟨j, hj, hjv⟩
              exact ⟨j, hj, (ih j (hPG i j hj)).mp hjv⟩
            · rintro ⟨j, hj, hjv⟩
              exact ⟨j, hj, (ih j (hPG i j hj)).mpr hjv⟩
        · apply or_congr
          · exact hRdirect i hig hiH
          · constructor
            · rintro ⟨j, hj, hjv⟩
              exact ⟨j, hj, (ih j (hRG i j hj)).mp hjv⟩
            · rintro ⟨j, hj, hjv⟩
              exact ⟨j, hj, (ih j (hRG i j hj)).mpr hjv⟩
    have hbefore : ¬ ((∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j) := by
      rw [hout I]
      rintro ⟨x, hx, y, hy, hxy⟩
      exact hInd x hx y hy hxy
    have hafter : ((∃ v ∈ OV, v ∈ insert u I) ∨ ∃ j ∈ OG, val (insert u I) j) :=
      (hout (insert u I)).mpr
        ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, huw⟩
    rcases hafter with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
    · rw [hOV] at hv
      exact Finset.notMem_empty v hv
    · exact hbefore (Or.inr ⟨j, hj, (hall j).mpr hjv⟩)
  have hIg : ¬ val I g := by
    intro hIg
    exact hchange (iff_of_true hIg (val_mono PV RV PG RG val hPG hRG hval hsub g hIg))
  have huIg : val (insert u I) g := by
    by_contra huIg
    exact hchange (iff_of_false hIg huIg)
  have hlower : ∀ j : Fin b, j < g → val (insert u I) j → val I j := by
    intro j
    induction j using Fin.strong_induction_on with
    | _ j ih =>
      intro hjg hj
      by_cases hjH : j = H
      · subst j
        exact hIH
      have hjg' : j ≠ g := ne_of_lt hjg
      rw [hval (insert u I) j] at hj
      rw [hval I j]
      constructor
      · rcases hj.1 with h | ⟨k, hk, hkv⟩
        · exact Or.inl ((hPdirect j hjg' hjH).mpr h)
        · exact Or.inr ⟨k, hk, ih k (hPG j k hk) (lt_trans (hPG j k hk) hjg) hkv⟩
      · rcases hj.2 with h | ⟨k, hk, hkv⟩
        · exact Or.inl ((hRdirect j hjg' hjH).mpr h)
        · exact Or.inr ⟨k, hk, ih k (hRG j k hk) (lt_trans (hRG j k hk) hjg) hkv⟩
  constructor
  · exact hIg
  · have hs := (hval (insert u I) g).mp huIg
    rcases hs.2 with ⟨v, hv, hvI⟩ | ⟨j, hj, hjv⟩
    · rcases Finset.mem_insert.mp hvI with rfl | hvI
      · exact (huRV hv).elim
      · exact Or.inl ⟨v, hv, hvI⟩
    · exact Or.inr ⟨j, hj, hlower j (hRG g j hj) hjv⟩

end PEqualNP.Outside.L_meta_351

theorem PEqualNP.Outside.L_meta_351 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ H : Fin b, (∃ g : Fin b, g ≠ H) → (∀ g : Fin b, g ≠ H → (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ PV g ∧ u ∉ RV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H) ∧ (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ RV g ∧ u ∉ PV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H)) → ∀ a c : Fin n, G.Adj a c → ¬ ∀ i : Fin b, i ≠ H → ((a ∉ PV i ∧ c ∉ PV i) ∨ (a ∉ RV i ∧ c ∉ RV i)) := by
  intro n b G PV RV PG RG OV OG val hPG hRG hval hout H hne hdel a c hac hlock
  have hHOG : H ∉ OG := by
    intro hH
    rcases hne with ⟨g, hg⟩
    rcases (hdel g hg).1 with ⟨u, I, huPV, huRV, hu, hInd, huI, hedge, hIH⟩
    have houtI := (hout I).mp (Or.inr ⟨H, hH, hIH⟩)
    rcases houtI with ⟨x, hx, y, hy, hxy⟩
    exact hInd x hx y hy hxy
  have hOV : OV = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have h := (hout {v}).mp (Or.inl ⟨v, hv, by simp⟩)
    rcases h with ⟨x, hx, y, hy, hxy⟩
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact G.loopless.irrefl v hxy
  have hvalswap : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
      (((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j) ∧
        ((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j)) := by
    intro X i
    rw [hval X i]
    exact and_comm
  have hpair : ∀ i : Fin b, i ≠ H → ¬ val {a, c} i := by
    intro i
    induction i using Fin.strong_induction_on with
    | _ i ih =>
      intro hiH hvi
      have hs := (hval {a, c} i).mp hvi
      rcases hlock i hiH with hP | hR
      · rcases hs.1 with ⟨v, hv, hvX⟩ | ⟨j, hj, hjv⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hvX
          rcases hvX with rfl | rfl
          · exact hP.1 hv
          · exact hP.2 hv
        · have hji : j < i := hPG i j hj
          by_cases hjH : j = H
          · subst j
            rcases (hdel i hiH).1 with ⟨u, I, huPV, huRV, hu, hInd, huI, hedge, hIH⟩
            have hd := PEqualNP.Outside.L_meta_351.delivery_p G PV RV PG RG OV OG val hPG hRG hval hout hOV H i u I
              huRV hu hInd hedge hIH
            apply hd.1
            rw [hval I i]
            exact ⟨Or.inr ⟨H, hj, hIH⟩, hd.2⟩
          · exact ih j hji hjH hjv
      · rcases hs.2 with ⟨v, hv, hvX⟩ | ⟨j, hj, hjv⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hvX
          rcases hvX with rfl | rfl
          · exact hR.1 hv
          · exact hR.2 hv
        · have hji : j < i := hRG i j hj
          by_cases hjH : j = H
          · subst j
            rcases (hdel i hiH).2 with ⟨u, I, huRV, huPV, hu, hInd, huI, hedge, hIH⟩
            have hd := PEqualNP.Outside.L_meta_351.delivery_p G RV PV RG PG OV OG val hRG hPG hvalswap hout hOV H i u I
              huPV (fun k hk => hu k hk.symm) hInd hedge hIH
            apply hd.1
            rw [hval I i]
            exact ⟨hd.2, Or.inr ⟨H, hj, hIH⟩⟩
          · exact ih j hji hjH hjv
  have houtAC : ((∃ v ∈ OV, v ∈ ({a, c} : Finset (Fin n))) ∨
      ∃ j ∈ OG, val {a, c} j) :=
    (hout {a, c}).mpr ⟨a, by simp, c, by simp, hac⟩
  rcases houtAC with ⟨v, hv, hvAC⟩ | ⟨i, hiOG, hvi⟩
  · rw [hOV] at hv
    exact Finset.notMem_empty v hv
  · have hiH : i ≠ H := by
      intro hiH
      subst i
      exact hHOG hiOG
    exact hpair i hiH hvi
