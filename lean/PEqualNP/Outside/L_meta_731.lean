import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_731

open scoped Classical

-- Remove sinks and their neighbours until every remaining vertex has an outgoing edge.
private theorem peelOn731 {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hadj : ∀ u v, G.Adj u v ↔ D u v ∨ D v u) (S : Finset (Fin n)) :
    ∃ P R : Finset (Fin n), P ⊆ S ∧ R ⊆ S ∧
      (∀ u ∈ P, ∀ v ∈ P, ¬ G.Adj u v) ∧ Disjoint P R ∧
      (∀ u ∈ P, ∀ v ∈ R, ¬ G.Adj u v) ∧ (∀ v ∈ R, ∃ w ∈ R, D v w) ∧
      (∀ v ∈ S, v ∉ P → v ∉ R → ∃ u ∈ P, D v u) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hsink : ∃ x ∈ S, ∀ y ∈ S, ¬ D x y
    · obtain ⟨x,hx,sink⟩ := hsink
      let T := S.filter (fun y => y ≠ x ∧ ¬ D y x)
      have sub : T ⊆ S := Finset.filter_subset _ _
      have hxT : x ∉ T := by simp [T]
      have strict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨sub, fun eq => hxT (eq ▸ hx)⟩
      have separate (v : Fin n) (hv : v ∈ T) : ¬ G.Adj x v := by
        have h := (Finset.mem_filter.mp hv).2.2
        exact fun edge => ((hadj x v).mp edge).elim (sink v (sub hv)) h
      obtain ⟨P,R,hP,hR,ind,disj,apart,out,dom⟩ := ih T strict
      refine ⟨insert x P,R,Finset.insert_subset hx (hP.trans sub),hR.trans sub,?_,?_,?_,out,?_⟩
      · intro u hu v hv
        rcases Finset.mem_insert.mp hu with ux | up
        · subst u
          rcases Finset.mem_insert.mp hv with vx | vp
          · subst v
            exact G.loopless.irrefl _
          · exact separate _ (hP vp)
        · rcases Finset.mem_insert.mp hv with vx | vp
          · subst v
            exact fun e => separate _ (hP up) e.symm
          · exact ind _ up _ vp
      · apply Finset.disjoint_left.mpr
        intro u hu h
        rcases Finset.mem_insert.mp hu with rfl | hp
        · exact hxT (hR h)
        · exact Finset.disjoint_left.mp disj hp h
      · intro u hu v hv
        rcases Finset.mem_insert.mp hu with rfl | hp
        · exact separate _ (hR hv)
        · exact apart _ hp _ hv
      · intro v hv hp hr
        by_cases edge : D v x
        · exact ⟨x, Finset.mem_insert_self _ _,edge⟩
        · have vne : v ≠ x := fun e => hp (Finset.mem_insert.mpr (Or.inl e))
          have hvT : v ∈ T := Finset.mem_filter.mpr ⟨hv,vne,edge⟩
          obtain ⟨u,hu,he⟩ := dom v hvT (fun h => hp (Finset.mem_insert_of_mem h)) hr
          exact ⟨u,Finset.mem_insert_of_mem hu,he⟩
    · refine ⟨∅, S, Finset.empty_subset _, Finset.Subset.rfl, by simp, by simp, by simp, ?_, ?_⟩
      · intro v hv
        by_contra! none
        exact hsink ⟨v,hv,none⟩
      · intro v hv _ hn
        exact (hn hv).elim

theorem peel731 {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (hadj : ∀ u v, G.Adj u v ↔ D u v ∨ D v u) :
    ∃ P R : Finset (Fin n), (∀ u ∈ P, ∀ v ∈ P, ¬ G.Adj u v) ∧ Disjoint P R ∧
      (∀ u ∈ P, ∀ v ∈ R, ¬ G.Adj u v) ∧ (∀ v ∈ R, ∃ w ∈ R, D v w) ∧
      (∀ v, v ∉ P → v ∉ R → ∃ u ∈ P, D v u) := by
  obtain ⟨P,R,_,_,ind,disj,apart,out,dom⟩ := peelOn731 G D hadj Finset.univ
  exact ⟨P,R,ind,disj,apart,out,fun v => dom v (Finset.mem_univ v)⟩

-- On the remaining graph, compare missed vertices with the size of each colour class.
theorem color731 {n : ℕ} (R : Finset (Fin n)) (D : Fin n → Fin n → Prop)
    (c : Fin n → Fin 3) (hc : ∀ u v, D u v → c u ≠ c v)
    (hR : ∀ v ∈ R, ∃ w ∈ R, D v w) :
    ∃ j : Fin 3, (R.filter (fun v => c v ≠ j ∧ ¬ ∃ w ∈ R, c w = j ∧ D v w)).card ≤
      (R.filter (fun v => c v = j)).card := by
  classical
  let missed (j : Fin 3) (v : Fin n) : Prop := c v ≠ j ∧ ¬ ∃ w ∈ R, c w = j ∧ D v w
  have one (v : Fin n) (hv : v ∈ R) :
      ((Finset.univ : Finset (Fin 3)).filter (fun j => missed j v)).card ≤ 1 := by
    obtain ⟨w, hw, edge⟩ := hR v hv
    have avoids (j : Fin 3) (h : missed j v) : c v ≠ j ∧ c w ≠ j :=
      ⟨h.1, fun eq => h.2 ⟨w, hw, eq, edge⟩⟩
    have three : ∀ a b j k : Fin 3, a ≠ b → a ≠ j → b ≠ j → a ≠ k → b ≠ k → j = k := by decide
    apply Finset.card_le_one.mpr
    intro j hj k hk
    obtain ⟨hjv, hjw⟩ := avoids j (Finset.mem_filter.mp hj).2
    obtain ⟨hkv, hkw⟩ := avoids k (Finset.mem_filter.mp hk).2
    exact three _ _ _ _ (hc v w edge) hjv hjw hkv hkw
  have small : (∑ j : Fin 3, (R.filter (missed j)).card) ≤ R.card := by
    calc
      _ = ∑ v ∈ R, ((Finset.univ : Finset (Fin 3)).filter (fun j => missed j v)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ ≤ _ := by
        simpa using Finset.sum_le_sum (s := R) one
  have total : (∑ j : Fin 3, (R.filter (fun v => c v = j)).card) = R.card := by
    calc
      _ = ∑ v ∈ R, ((Finset.univ : Finset (Fin 3)).filter (fun j => c v = j)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by
        have singleton (v : Fin n) : ((Finset.univ : Finset (Fin 3)).filter (fun j => c v = j)) = {c v} := by
          ext j
          simp [eq_comm]
        simp_rw [singleton]
        simp
  change ∃ j : Fin 3, (R.filter (missed j)).card ≤ (R.filter (fun v => c v = j)).card
  by_contra! impossible
  have strict := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 3))) Finset.univ_nonempty
    (fun j _ => impossible j)
  omega

-- The selected sinks together with the chosen colour class form the independent set.
theorem assemble731 {n : ℕ} (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (c : G.Coloring (Fin 3)) (P R : Finset (Fin n)) (j : Fin 3)
    (hP : ∀ u ∈ P, ∀ v ∈ P, ¬ G.Adj u v) (hPR : Disjoint P R)
    (hcross : ∀ u ∈ P, ∀ v ∈ R, ¬ G.Adj u v)
    (hR : ∀ v ∈ R, ∃ w ∈ R, D v w)
    (hrest : ∀ v, v ∉ P → v ∉ R → ∃ u ∈ P, D v u)
    (hmiss : (R.filter (fun v => c v ≠ j ∧ ¬ ∃ w ∈ R, c w = j ∧ D v w)).card ≤
      (R.filter (fun v => c v = j)).card) :
    ∃ S : Finset (Fin n), (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) ∧
      n ≤ {v : Fin n | v ∈ S ∧ ∃ w, D v w}.ncard +
        {v : Fin n | v ∉ S ∧ ∃ w ∈ S, D v w}.ncard + G.indepNum := by
  classical
  let C := R.filter (fun v => c v = j)
  let M := R.filter (fun v => c v ≠ j ∧ ¬ ∃ w ∈ R, c w = j ∧ D v w)
  let S := P ∪ C
  have hC (v : Fin n) : v ∈ C ↔ v ∈ R ∧ c v = j := Finset.mem_filter
  have hS (v : Fin n) : v ∈ S ↔ v ∈ P ∨ v ∈ C := Finset.mem_union
  have hind : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    intro u hu v hv
    rcases (hS u).mp hu with hu | hu <;> rcases (hS v).mp hv with hv | hv
    · exact hP u hu v hv
    · exact hcross u hu v ((hC v).mp hv).1
    · exact fun e => hcross v hv u ((hC u).mp hu).1 e.symm
    · exact fun e => c.valid e (((hC u).mp hu).2.trans ((hC v).mp hv).2.symm)
  refine ⟨S, hind, ?_⟩
  let A : Set (Fin n) := {v | v ∈ S ∧ ∃ w, D v w}
  let B : Set (Fin n) := {v | v ∉ S ∧ ∃ w ∈ S, D v w}
  change n ≤ A.ncard + B.ncard + G.indepNum
  have cover : Set.univ ⊆ (A ∪ B) ∪ ((P : Set (Fin n)) ∪ (M : Set (Fin n))) := by
    intro v _
    by_cases hp : v ∈ P
    · exact Or.inr (Or.inl hp)
    by_cases hr : v ∈ R
    · by_cases hc : c v = j
      · obtain ⟨w, _, hd⟩ := hR v hr
        exact Or.inl (Or.inl ⟨(hS v).mpr (Or.inr ((hC v).mpr ⟨hr, hc⟩)), w, hd⟩)
      have hns : v ∉ S := fun hv => ((hS v).mp hv).elim hp (fun h => hc ((hC v).mp h).2)
      by_cases hout : ∃ w ∈ R, c w = j ∧ D v w
      · obtain ⟨w, hw, hj, hd⟩ := hout
        exact Or.inl (Or.inr ⟨hns, w, (hS w).mpr (Or.inr ((hC w).mpr ⟨hw, hj⟩)), hd⟩)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hr, hc, hout⟩))
    · obtain ⟨w, hw, hd⟩ := hrest v hp hr
      have hns : v ∉ S := fun hv => ((hS v).mp hv).elim hp (fun h => hr ((hC v).mp h).1)
      exact Or.inl (Or.inr ⟨hns, w, (hS w).mpr (Or.inl hw), hd⟩)
  have hpc : Disjoint P C := Finset.disjoint_left.mpr fun _ hp hc =>
    Finset.disjoint_left.mp hPR hp ((hC _).mp hc).1
  have hsind : G.IsIndepSet (S : Set (Fin n)) := fun u hu v hv _ => hind u hu v hv
  have hα : P.card + C.card ≤ G.indepNum := by
    rw [← Finset.card_union_of_disjoint hpc]
    exact hsind.card_le_indepNum
  have hcover := Set.ncard_le_ncard cover
  have hsplit := Set.ncard_union_le (A ∪ B) ((P : Set (Fin n)) ∪ (M : Set (Fin n)))
  have hab := Set.ncard_union_le A B
  have hpm := Set.ncard_union_le (P : Set (Fin n)) (M : Set (Fin n))
  simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hcover
  simp only [Set.ncard_coe_finset] at hpm
  change M.card ≤ C.card at hmiss
  omega

-- Extending an independent set preserves its coverage.
theorem extend731 (n : ℕ) (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop)
    (S : Finset (Fin n))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hcount : n ≤ {v : Fin n | v ∈ S ∧ ∃ w, D v w}.ncard
      + {v : Fin n | v ∉ S ∧ ∃ w ∈ S, D v w}.ncard + G.indepNum) :
    ∃ I : Set (Fin n),
    (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) ∧
    n ≤ {v : Fin n | v ∈ I ∧ ∃ w, D v w}.ncard + {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}.ncard
      + G.indepNum := by
  classical
  let Indep (T : Set (Fin n)) := ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v
  obtain ⟨I, hSI, hmax⟩ := Finite.exists_le_maximal (p := Indep) (a := (S : Set (Fin n))) hS
  refine ⟨I, hmax.prop, ?_, ?_⟩
  · intro v hv
    by_contra hn
    have hnew : Indep (insert v I) := by
      intro a ha b hb
      rcases Set.mem_insert_iff.mp ha with hav | hai
      · subst a
        rcases Set.mem_insert_iff.mp hb with hbv | hbi
        · subst b
          exact G.irrefl
        · exact fun e => hn ⟨b, hbi, e⟩
      · rcases Set.mem_insert_iff.mp hb with hbv | hbi
        · subst b
          exact fun e => hn ⟨a, hai, e.symm⟩
        · exact hmax.prop a hai b hbi
    exact hv ((hmax.le_of_ge hnew (Set.subset_insert v I)) (Set.mem_insert v I))
  · let A (T : Set (Fin n)) := {v : Fin n | v ∈ T ∧ ∃ w, D v w}
    let B (T : Set (Fin n)) := {v : Fin n | v ∉ T ∧ ∃ w ∈ T, D v w}
    have hd (T : Set (Fin n)) : Disjoint (A T) (B T) :=
      Set.disjoint_left.mpr fun _ ha hb => hb.1 ha.1
    have sub : A S ∪ B S ⊆ A I ∪ B I := by
      intro v hv
      rcases hv with ⟨hs, hw⟩ | ⟨_, w, hw, he⟩
      · exact Or.inl ⟨hSI hs, hw⟩
      · by_cases hi : v ∈ I
        · exact Or.inl ⟨hi, w, he⟩
        · exact Or.inr ⟨hi, w, hSI hw, he⟩
    have hm := Set.ncard_le_ncard sub
    rw [Set.ncard_union_eq (hd S), Set.ncard_union_eq (hd I)] at hm
    exact hcount.trans (Nat.add_le_add_right hm _)

end PEqualNP.Outside.L_meta_731

open PEqualNP.Outside.L_meta_731

theorem PEqualNP.Outside.L_meta_731 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : Fin n → Fin n → Prop),
  G.Colorable 3 → (∀ u v, G.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
  ∃ I : Set (Fin n),
    (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) ∧
    n ≤ {v : Fin n | v ∈ I ∧ ∃ w, D v w}.ncard + {v : Fin n | v ∉ I ∧ ∃ w ∈ I, D v w}.ncard
      + G.indepNum := by
  classical
  intro n G D hcolor hadj _
  obtain ⟨c⟩ := hcolor
  obtain ⟨P, R, hP, hPR, hcross, hR, hrest⟩ := peel731 G D hadj
  obtain ⟨j, hj⟩ := color731 R D c (fun u v e => c.valid ((hadj u v).mpr (Or.inl e))) hR
  obtain ⟨S, hS, hcount⟩ := assemble731 G D c P R j hP hPR hcross hR hrest hj
  exact extend731 n G D S hS hcount
