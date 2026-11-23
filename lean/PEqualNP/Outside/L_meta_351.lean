import Mathlib
import PEqualNP.Defs

private def wireOn {n b : ℕ} (V : Finset (Fin n)) (D : Finset (Fin b))
    (val : Finset (Fin n) → Fin b → Prop) (X : Finset (Fin n)) : Prop :=
  (∃ v ∈ V, v ∈ X) ∨ ∃ j ∈ D, val X j

private theorem gateOrder (b : ℕ) : WellFounded (fun j i : Fin b => j < i) :=
  (measure (fun i : Fin b => i.val)).wf

private theorem wireOn_mono {n b : ℕ} {V : Finset (Fin n)} {D : Finset (Fin b)}
    {val : Finset (Fin n) → Fin b → Prop} {X Y : Finset (Fin n)}
    (hXY : X ⊆ Y) (hval : ∀ j ∈ D, val X j → val Y j) :
    wireOn V D val X → wireOn V D val Y := by
  rintro (⟨v, hv, hx⟩ | ⟨j, hj, hx⟩)
  · exact Or.inl ⟨v, hv, hXY hx⟩
  · exact Or.inr ⟨j, hj, hval j hj hx⟩

private theorem wireOn_insert {n b : ℕ} {V : Finset (Fin n)} {D : Finset (Fin b)}
    {val : Finset (Fin n) → Fin b → Prop} {I : Finset (Fin n)} {u : Fin n}
    (hu : u ∉ V) (hval : ∀ j ∈ D, val (insert u I) j ↔ val I j) :
    wireOn V D val (insert u I) ↔ wireOn V D val I := by
  constructor
  · rintro (⟨v, hv, hx⟩ | ⟨j, hj, hx⟩)
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (hu hv).elim
      · exact Or.inl ⟨v, hv, hx⟩
    · exact Or.inr ⟨j, hj, (hval j hj).mp hx⟩
  · exact wireOn_mono (fun _ hx => Finset.mem_insert_of_mem hx)
      (fun j hj => (hval j hj).mpr)

private theorem noDelivery {n b : ℕ} {G : SimpleGraph (Fin n)}
    {PV RV : Fin b → Finset (Fin n)} {PG RG : Fin b → Finset (Fin b)}
    {OV : Finset (Fin n)} {OG : Finset (Fin b)}
    {val : Finset (Fin n) → Fin b → Prop}
    (leftBefore : ∀ i, ∀ j ∈ PG i, j < i) (rightBefore : ∀ i, ∀ j ∈ RG i, j < i)
    (gate : ∀ X i, val X i ↔ wireOn (PV i) (PG i) val X ∧ wireOn (RV i) (RG i) val X)
    (output : ∀ X, wireOn OV OG val X ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c)
    (noBareOutput : ∀ u, u ∉ OV) {g H : Fin b}
    (locked : ∃ (u : Fin n) (I : Finset (Fin n)), u ∈ PV g ∧ u ∉ RV g ∧
      (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧
      (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H) :
    H ∉ PG g := by
  intro hFeed
  obtain ⟨u, I, _, huRight, huWhere, hIndependent, _, ⟨w, hw, huw⟩, hH⟩ := locked
  have mono (i : Fin b) : val I i → val (insert u I) i := by
    refine (gateOrder b).induction (C := fun j => val I j → val (insert u I) j) i ?_
    intro j ih hj
    obtain ⟨hl, hr⟩ := (gate I j).mp hj
    exact (gate (insert u I) j).mpr
      ⟨wireOn_mono (fun _ hx => Finset.mem_insert_of_mem hx)
          (fun k hk => ih k (leftBefore j k hk)) hl,
       wireOn_mono (fun _ hx => Finset.mem_insert_of_mem hx)
          (fun k hk => ih k (rightBefore j k hk)) hr⟩
  have hH' := mono H hH
  have unchanged (i : Fin b) : val (insert u I) i ↔ val I i := by
    refine (gateOrder b).induction (C := fun j => val (insert u I) j ↔ val I j) i ?_
    intro j ih
    by_cases hjH : j = H
    · subst j
      exact ⟨fun _ => hH, fun _ => hH'⟩
    have rightAbsent : u ∉ RV j := by
      intro hu
      rcases huWhere j (Or.inr hu) with hjg | hjH'
      · exact huRight (hjg ▸ hu)
      · exact hjH hjH'
    have rightSame := wireOn_insert (val := val) (I := I) rightAbsent
      (fun k hk => ih k (rightBefore j k hk))
    have leftSame : wireOn (PV j) (PG j) val (insert u I) ↔ wireOn (PV j) (PG j) val I := by
      by_cases hjg : j = g
      · subst j
        exact ⟨fun _ => Or.inr ⟨H, hFeed, hH⟩, fun _ => Or.inr ⟨H, hFeed, hH'⟩⟩
      · apply wireOn_insert
        · intro hu
          exact (huWhere j (Or.inl hu)).elim hjg hjH
        · exact fun k hk => ih k (leftBefore j k hk)
    rw [gate (insert u I) j, gate I j, leftSame, rightSame]
  have insertedOutput := (output (insert u I)).mpr
    ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hw, huw⟩
  have oldOutput := (wireOn_insert (noBareOutput u) (fun j _ => unchanged j)).mp insertedOutput
  obtain ⟨a, ha, c, hc, hac⟩ := (output I).mp oldOutput
  exact hIndependent a ha c hc hac

theorem PEqualNP.Outside.L_meta_351 :
    ∀ (n b : ℕ) (G : SimpleGraph (Fin n))
      (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b))
      (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop),
      (∀ i : Fin b, ∀ j ∈ PG i, j < i) →
      (∀ i : Fin b, ∀ j ∈ RG i, j < i) →
      (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔
        (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
         ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) →
      (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔
        ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) →
      ∀ H : Fin b, (∃ g : Fin b, g ≠ H) →
      (∀ g : Fin b, g ≠ H →
        (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ PV g ∧ u ∉ RV g ∧
          (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧
          (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H) ∧
        (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ RV g ∧ u ∉ PV g ∧
          (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧
          (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H)) →
      ∀ a c : Fin n, G.Adj a c →
        ¬ ∀ i : Fin b, i ≠ H → ((a ∉ PV i ∧ c ∉ PV i) ∨ (a ∉ RV i ∧ c ∉ RV i)) := by
  intro n b G PV RV PG RG OV OG val leftBefore rightBefore gate output H existsOther locks
  change ∀ X i, val X i ↔ wireOn (PV i) (PG i) val X ∧ wireOn (RV i) (RG i) val X at gate
  change ∀ X, wireOn OV OG val X ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c at output
  have noBareOutput (v : Fin n) : v ∉ OV := by
    intro hv
    obtain ⟨a, ha, c, hc, hac⟩ := (output {v}).mp (Or.inl ⟨v, hv, by simp⟩)
    simp only [Finset.mem_singleton] at ha hc
    subst a
    subst c
    exact G.irrefl hac
  have noGateOutput : H ∉ OG := by
    intro h
    obtain ⟨g, hg⟩ := existsOther
    obtain ⟨_, I, _, _, _, hIndependent, _, _, hH⟩ := (locks g hg).1
    obtain ⟨a, ha, c, hc, hac⟩ := (output I).mp (Or.inr ⟨H, h, hH⟩)
    exact hIndependent a ha c hc hac
  have leftNoFeed (g : Fin b) (hg : g ≠ H) : H ∉ PG g :=
    noDelivery leftBefore rightBefore gate output noBareOutput (locks g hg).1
  have rightNoFeed (g : Fin b) (hg : g ≠ H) : H ∉ RG g := by
    apply noDelivery rightBefore leftBefore (fun X i => (gate X i).trans and_comm)
      output noBareOutput
    obtain ⟨u, I, hu, hu', huWhere, rest⟩ := (locks g hg).2
    exact ⟨u, I, hu, hu', fun i h => huWhere i (h.elim Or.inr Or.inl), rest⟩
  intro a c hac lacksBare
  have noLive (i : Fin b) : i ≠ H → ¬ val {a, c} i := by
    refine (gateOrder b).induction (C := fun j => j ≠ H → ¬ val {a, c} j) i ?_
    intro j ih hj hjOn
    have sideOff {V : Finset (Fin n)} {D : Finset (Fin b)} (ha : a ∉ V) (hc : c ∉ V)
        (hBefore : ∀ k ∈ D, k < j) (hNoFeed : H ∉ D) : ¬ wireOn V D val {a, c} := by
      rintro (⟨v, hv, hx⟩ | ⟨k, hk, hx⟩)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha hv
        · exact hc hv
      · exact ih k (hBefore k hk) (fun h => hNoFeed (h ▸ hk)) hx
    obtain ⟨leftOn, rightOn⟩ := (gate {a, c} j).mp hjOn
    rcases lacksBare j hj with ⟨ha, hc⟩ | ⟨ha, hc⟩
    · exact sideOff ha hc (leftBefore j) (leftNoFeed j hj) leftOn
    · exact sideOff ha hc (rightBefore j) (rightNoFeed j hj) rightOn
  have outOn := (output {a, c}).mpr ⟨a, by simp, c, by simp, hac⟩
  rcases outOn with ⟨v, hv, _⟩ | ⟨j, hj, hOn⟩
  · exact noBareOutput v hv
  · exact noLive j (fun h => noGateOutput (h ▸ hj)) hOn
