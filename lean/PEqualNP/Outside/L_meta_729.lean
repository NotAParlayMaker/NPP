import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_729

open Classical

-- A walk of a given length along a relation.
def Wk {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | 0, u, v => u = v
  | m + 1, u, v => ∃ w, R u w ∧ Wk R m w v

theorem wk_trans {α : Type} (R : α → α → Prop) : ∀ (a b : ℕ) (u v w : α),
    Wk R a u v → Wk R b v w → Wk R (a + b) u w := by
  intro a
  induction a with
  | zero =>
    intro b u v w h1 h2
    have e : u = v := h1
    subst e
    simpa using h2
  | succ a ih =>
    intro b u v w h1 h2
    obtain ⟨x, hx, hw⟩ := h1
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact ⟨x, hx, ih b x v w hw h2⟩

theorem wk_snoc {α : Type} (R : α → α → Prop) {m : ℕ} {u v w : α} (h : Wk R m u v)
    (hr : R v w) : Wk R (m + 1) u w :=
  wk_trans R m 1 u v w h ⟨w, hr, rfl⟩

theorem wk_of_rtg {α : Type} (R : α → α → Prop) {u v : α}
    (h : Relation.ReflTransGen R u v) : ∃ m, Wk R m u v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, wk_snoc R hm hbc⟩

-- A walk as a sequence of vertices.
theorem wk_fun {α : Type} (R : α → α → Prop) : ∀ (m : ℕ) (u v : α), Wk R m u v →
    ∃ c : ℕ → α, c 0 = u ∧ c m = v ∧ ∀ i, i < m → R (c i) (c (i + 1)) := by
  intro m
  induction m with
  | zero =>
    intro u v h
    exact ⟨fun _ => u, rfl, h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro u v h
    obtain ⟨w, hw, hwk⟩ := h
    obtain ⟨c, c0, cm, cs⟩ := ih w v hwk
    refine ⟨fun i => if i = 0 then u else c (i - 1), by simp, by simp [cm], ?_⟩
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp [c0]
      exact hw
    · have := cs (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this
      simp [h0]
      exact this

-- Richardson's theorem on every vertex set, by induction on the set.
theorem kernel {n : ℕ} (D : Fin n → Fin n → Prop)
    (hodd : ¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧
      ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) :
    ∀ V : Finset (Fin n), ∃ K : Finset (Fin n), K ⊆ V ∧ (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧
      ∀ v ∈ V, v ∉ K → ∃ k ∈ K, D v k := by
  intro V
  induction V using Finset.strongInduction with
  | H V ih =>
    by_cases hV : V.Nonempty
    swap
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro v hv
      exact absurd ⟨v, hv⟩ hV
    obtain ⟨R, hR⟩ : ∃ R : Fin n → Fin n → Prop, ∀ u w, R u w ↔ (D u w ∧ w ∈ V) :=
      ⟨_, fun _ _ => Iff.rfl⟩
    have hodd' : ∀ (k : ℕ) (u : Fin n), ¬ Wk R (2 * k + 1) u u := by
      intro k u h
      obtain ⟨c, c0, cm, cs⟩ := wk_fun R _ u u h
      exact hodd ⟨k, c, by rw [cm, c0], fun i hi => ((hR _ _).mp (cs i hi)).1⟩
    obtain ⟨r, hrV, hmin⟩ := Finset.exists_min_image V
      (fun v => (V.filter (fun w => Relation.ReflTransGen R v w)).card) hV
    obtain ⟨C, hC⟩ : ∃ C : Finset (Fin n), ∀ w, w ∈ C ↔ (w ∈ V ∧ Relation.ReflTransGen R r w) :=
      ⟨V.filter _, fun w => Finset.mem_filter⟩
    have hrC : r ∈ C := (hC r).mpr ⟨hrV, Relation.ReflTransGen.refl⟩
    have c3 : ∀ v ∈ C, Relation.ReflTransGen R v r := by
      intro v hv
      obtain ⟨hvV, hrv⟩ := (hC v).mp hv
      have hsub : V.filter (fun w => Relation.ReflTransGen R v w)
          ⊆ V.filter (fun w => Relation.ReflTransGen R r w) := by
        intro w hw
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨hw.1, hrv.trans hw.2⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (hmin v hvV)
      have hmem : r ∈ V.filter (fun w => Relation.ReflTransGen R r w) :=
        Finset.mem_filter.mpr ⟨hrV, Relation.ReflTransGen.refl⟩
      rw [← heq] at hmem
      exact (Finset.mem_filter.mp hmem).2
    have c2 : ∀ u ∈ C, ∀ w, D u w → w ∈ V → w ∈ C := by
      intro u hu w hd hw
      exact (hC w).mpr ⟨hw, ((hC u).mp hu).2.tail ((hR u w).mpr ⟨hd, hw⟩)⟩
    obtain ⟨P0, hP0⟩ : ∃ P0 : Finset (Fin n),
        ∀ w, w ∈ P0 ↔ (w ∈ C ∧ ∃ j, Wk R (2 * j) r w) :=
      ⟨C.filter _, fun w => Finset.mem_filter⟩
    have hrP0 : r ∈ P0 := (hP0 r).mpr ⟨hrC, 0, rfl⟩
    have indepP0 : ∀ u ∈ P0, ∀ v ∈ P0, ¬ D u v := by
      intro u hu v hv hd
      obtain ⟨huC, j, hj⟩ := (hP0 u).mp hu
      obtain ⟨hvC, j', hj'⟩ := (hP0 v).mp hv
      have hvV := ((hC v).mp hvC).1
      obtain ⟨b, hb⟩ := wk_of_rtg R (c3 v hvC)
      have h1 : Wk R (2 * j + 1) r v := wk_snoc R hj ((hR u v).mpr ⟨hd, hvV⟩)
      rcases Nat.even_or_odd' b with ⟨c, rfl | rfl⟩
      · have := wk_trans R _ _ r v r h1 hb
        exact hodd' (j + c) r (by
          rw [show 2 * (j + c) + 1 = 2 * j + 1 + 2 * c by ring]
          exact this)
      · have := wk_trans R _ _ r v r hj' hb
        exact hodd' (j' + c) r (by
          rw [show 2 * (j' + c) + 1 = 2 * j' + (2 * c + 1) by ring]
          exact this)
    have absC : ∀ v ∈ C, v ∉ P0 → ∃ k ∈ P0, D v k := by
      intro v hvC hvP
      obtain ⟨hvV, hrv⟩ := (hC v).mp hvC
      obtain ⟨m, hm⟩ := wk_of_rtg R hrv
      obtain ⟨b, hb⟩ := wk_of_rtg R (c3 v hvC)
      rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
      · exact absurd ((hP0 v).mpr ⟨hvC, j, hm⟩) hvP
      · cases b with
        | zero =>
          have e : v = r := hb
          rw [e] at hvP
          exact absurd hrP0 hvP
        | succ b' =>
          obtain ⟨w, hw, _⟩ := hb
          obtain ⟨hdw, hwV⟩ := (hR v w).mp hw
          refine ⟨w, (hP0 w).mpr ⟨c2 v hvC w hdw hwV, j + 1, ?_⟩, hdw⟩
          have := wk_snoc R hm hw
          rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
          exact this
    obtain ⟨V', hV'⟩ : ∃ V' : Finset (Fin n),
        ∀ w, w ∈ V' ↔ (w ∈ V ∧ ¬ (w ∈ C ∨ ∃ k ∈ P0, D w k)) :=
      ⟨V.filter _, fun w => Finset.mem_filter⟩
    have hss : V' ⊂ V := by
      refine ⟨fun w hw => ((hV' w).mp hw).1, fun h => ?_⟩
      exact ((hV' r).mp (h hrV)).2 (Or.inl hrC)
    obtain ⟨K', hK'sub, hK'ind, hK'abs⟩ := ih V' hss
    refine ⟨P0 ∪ K', ?_, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact ((hC w).mp ((hP0 w).mp h).1).1
      · exact ((hV' w).mp (hK'sub h)).1
    · intro u hu v hv hd
      rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
      · exact indepP0 u hu v hv hd
      · have hvV' := (hV' v).mp (hK'sub hv)
        exact hvV'.2 (Or.inl (c2 u ((hP0 u).mp hu).1 v hd hvV'.1))
      · have huV' := (hV' u).mp (hK'sub hu)
        exact huV'.2 (Or.inr ⟨v, hv, hd⟩)
      · exact hK'ind u hu v hv hd
    · intro v hvV hvK
      rw [Finset.mem_union, not_or] at hvK
      by_cases h1 : v ∈ C
      · obtain ⟨k, hk, hd⟩ := absC v h1 hvK.1
        exact ⟨k, Finset.mem_union_left _ hk, hd⟩
      · by_cases h2 : ∃ k ∈ P0, D v k
        · obtain ⟨k, hk, hd⟩ := h2
          exact ⟨k, Finset.mem_union_left _ hk, hd⟩
        · have hvV' : v ∈ V' := (hV' v).mpr ⟨hvV, by
            rintro (h | h)
            · exact h1 h
            · exact h2 h⟩
          obtain ⟨k, hk, hd⟩ := hK'abs v hvV' hvK.2
          exact ⟨k, Finset.mem_union_right _ hk, hd⟩

end PEqualNP.Outside.L_meta_729

theorem PEqualNP.Outside.L_meta_729 : ∀ (n : ℕ) (D : Fin n → Fin n → Prop),
  (∀ v, ¬ D v v) → (∀ u v, D u v → ¬ D v u) →
  (¬ ∃ (k : ℕ) (c : ℕ → Fin n), c (2 * k + 1) = c 0 ∧ ∀ i, i < 2 * k + 1 → D (c i) (c (i + 1))) →
  ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ D u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  intro n D _ _ hodd
  obtain ⟨K, _, hind, habs⟩ := PEqualNP.Outside.L_meta_729.kernel D hodd Finset.univ
  refine ⟨(K : Set (Fin n)), ?_, ?_⟩
  · intro u hu v hv
    exact hind u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv)
  · intro v hv
    obtain ⟨k, hk, hd⟩ := habs v (Finset.mem_univ v) (fun h => hv (Finset.mem_coe.mpr h))
    exact ⟨k, Finset.mem_coe.mpr hk, hd⟩
