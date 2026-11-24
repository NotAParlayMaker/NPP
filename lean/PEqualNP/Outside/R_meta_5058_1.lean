import Mathlib
import PEqualNP.Defs

open PEqualNP.AndCount

theorem PEqualNP.Outside.R_meta_5058_1
    (h_full :
      have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ (C : AndCountCircuit 42), C.WellFormed → C.Computes G → 19 ≤ C.size)
    (h_one :
      have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ (v : Fin 42) (C : AndCountCircuit 42), C.WellFormed →
        (∀ U : Finset (Fin 42), v ∉ U → (∀ w ∈ U, ¬G.Adj v w) →
          (C.eval U = true ↔ ∃ a ∈ U, ∃ b ∈ U, G.Adj a b)) →
        16 ≤ C.size)
    (h_two :
      have G : SimpleGraph (Fin 42) := SimpleGraph.fromRel fun a b : Fin 42 =>
        a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ (p l : Fin 42), p.val < 21 → 21 ≤ l.val → ¬G.Adj p l →
        ∀ (C : AndCountCircuit 42), C.WellFormed →
        (∀ U : Finset (Fin 42), p ∉ U → l ∉ U →
          (∀ w ∈ U, ¬G.Adj p w ∧ ¬G.Adj l w) →
          (C.eval U = true ↔ ∃ a ∈ U, ∃ b ∈ U, G.Adj a b)) →
        14 ≤ C.size) :
    have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size ≤ (20 : ℕ) → (19 : ℕ) ≤ x2.size ∧ (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard + (16 : ℕ) ≤ x2.size) ∧ ∀ (x9 x10 : Fin (42 : ℕ)), ↑x9 < (21 : ℕ) → (21 : ℕ) ≤ ↑x10 → ¬x1.Adj x9 x10 → {x14 : Fin x2.size | x9 ∈ x2.leftVars x14 ∨ x9 ∈ x2.rightVars x14 ∨ x10 ∈ x2.leftVars x14 ∨ x10 ∈ x2.rightVars x14}.ncard + (14 : ℕ) ≤ x2.size := by
  classical
  dsimp only
  intro C hWF hComp hOut hSing hDisj hSize
  have sideTrue_def {m : ℕ} (U B : Finset (Fin 42)) (F : Finset (Fin m)) (i : Fin m) (v : Fin m → Bool) :
      AndCountCircuit.sideTrue U B F i v =
      decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl
  have gateValFuel_zero (E : AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin E.size) :
      E.gateValFuel U 0 i = false := rfl
  have gateValFuel_succ (E : AndCountCircuit 42) (U : Finset (Fin 42)) (d : ℕ) (i : Fin E.size) :
      E.gateValFuel U (d + 1) i =
        (AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
         AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) := rfl
  have gateVal_def (E : AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin E.size) :
      E.gateVal U i = E.gateValFuel U E.size i := rfl
  have eval_def (E : AndCountCircuit 42) (U : Finset (Fin 42)) :
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := rfl
  -- Helper 1: gateValFuel independence of fuel >= i.val + 1
  have fuel_indep : ∀ (D : AndCountCircuit 42) (U : Finset (Fin 42)) (d₁ d₂ : ℕ) (i : Fin D.size),
      i.val < d₁ → i.val < d₂ → D.gateValFuel U d₁ i = D.gateValFuel U d₂ i := by
    intro D U d₁
    induction d₁ with
    | zero => intro d₂ i h1; omega
    | succ d₁ ih =>
      intro d₂ i h1 h2
      cases d₂ with
      | zero => omega
      | succ d₂ =>
        rw [gateValFuel_succ, gateValFuel_succ, sideTrue_def, sideTrue_def, sideTrue_def, sideTrue_def]
        have hsub : ∀ (B : Finset (Fin 42)) (F : Finset (Fin D.size)),
            decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ D.gateValFuel U d₁ j = true) =
            decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ D.gateValFuel U d₂ j = true) := by
          intro B F
          congr 1; apply propext; constructor <;> rintro (h | ⟨j, hjF, hji, hjv⟩)
          · exact Or.inl h
          · exact Or.inr ⟨j, hjF, hji, by rw [← ih d₂ j (by omega) (by omega)]; exact hjv⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, hjF, hji, by rw [ih d₂ j (by omega) (by omega)]; exact hjv⟩
        rw [hsub, hsub]
  -- Helper 2: gateVal unfolding
  have gateVal_unfold : ∀ (D : AndCountCircuit 42) (U : Finset (Fin 42)) (i : Fin D.size),
      D.gateVal U i =
        (AndCountCircuit.sideTrue U (D.leftVars i) (D.leftGates i) i (D.gateVal U) &&
         AndCountCircuit.sideTrue U (D.rightVars i) (D.rightGates i) i (D.gateVal U)) := by
    intro D U i
    rw [gateVal_def D U i]
    rw [fuel_indep D U D.size (i.val + 1) i i.isLt (Nat.lt_succ_self _)]
    rw [gateValFuel_succ, sideTrue_def, sideTrue_def, sideTrue_def, sideTrue_def]
    have hsub : ∀ (B : Finset (Fin 42)) (F : Finset (Fin D.size)),
        decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ D.gateValFuel U i.val j = true) =
        decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, j < i ∧ D.gateVal U j = true) := by
      intro B F
      congr 1; apply propext; constructor <;> rintro (h | ⟨j, hjF, hji, hjv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, hjF, hji, by rw [gateVal_def, ← fuel_indep D U i.val D.size j hji j.isLt]; exact hjv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hjF, hji, by rw [fuel_indep D U i.val D.size j hji j.isLt, ← gateVal_def]; exact hjv⟩
    rw [hsub, hsub]
  -- Helper 3: monotonicity in U
  have gateVal_mono : ∀ (D : AndCountCircuit 42) {U V : Finset (Fin 42)}, U ⊆ V →
      ∀ (d : ℕ) (i : Fin D.size), D.gateValFuel U d i = true → D.gateValFuel V d i = true := by
    intro D U V hUV d
    induction d with
    | zero => intro i h; rw [gateValFuel_zero] at h; exact Bool.noConfusion h
    | succ d ih =>
      intro i h
      rw [gateValFuel_succ, Bool.and_eq_true, sideTrue_def, sideTrue_def,
        decide_eq_true_eq, decide_eq_true_eq] at h ⊢
      constructor
      · rcases h.1 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, hUV hvU⟩
        · exact Or.inr ⟨j, hjF, hji, ih j hjv⟩
      · rcases h.2 with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, hUV hvU⟩
        · exact Or.inr ⟨j, hjF, hji, ih j hjv⟩
  -- Core reduction lemma: restricting to U ∪ S eliminates every gate reading S
  have restrict_elim : ∀ (S : Finset (Fin 42)), C.eval S = false →
      ∃ (D : AndCountCircuit 42), D.WellFormed ∧
        D.size + (Finset.univ.filter fun i : Fin C.size =>
          ∃ v ∈ S, v ∈ C.leftVars i ∨ v ∈ C.rightVars i).card ≤ C.size ∧
        ∀ (U : Finset (Fin 42)), D.eval U = C.eval (U ∪ S) := by
    intro S hS_false
    have hS_outV : ∀ v ∈ C.outVars, v ∉ S := by
      intro v hv hvS
      have hT : C.eval S = true := by
        rw [eval_def, decide_eq_true_eq]
        exact Or.inl ⟨v, hv, hvS⟩
      rw [hT] at hS_false; exact Bool.noConfusion hS_false
    have hS_outG : ∀ j ∈ C.outGates, C.gateVal S j = false := by
      intro j hj
      cases hval : C.gateVal S j
      · rfl
      · have hT : C.eval S = true := by
          rw [eval_def, decide_eq_true_eq]
          exact Or.inr ⟨j, hj, hval⟩
        rw [hT] at hS_false; exact Bool.noConfusion hS_false
    let sL : Fin C.size → Bool := fun i =>
      AndCountCircuit.sideTrue S (C.leftVars i) (C.leftGates i) i (C.gateVal S)
    let sR : Fin C.size → Bool := fun i =>
      AndCountCircuit.sideTrue S (C.rightVars i) (C.rightGates i) i (C.gateVal S)
    let Keep : Finset (Fin C.size) := Finset.univ.filter fun i => sL i = false ∧ sR i = false
    -- For every gate i with gateVal S i = false, expand it into (V_i, G_i) with G_i ⊆ Keep
    have expand_exists : ∀ (m : ℕ) (i : Fin C.size), i.val = m → C.gateVal S i = false →
        ∃ (V : Finset (Fin 42)) (G : Finset (Fin C.size)),
          (∀ k ∈ G, k ∈ Keep ∧ k ≤ i) ∧
          (∀ U : Finset (Fin 42), C.gateVal (U ∪ S) i = true ↔
            (∃ v ∈ V, v ∈ U) ∨ (∃ k ∈ G, C.gateVal (U ∪ S) k = true)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro i hi hm
        by_cases hKeep : i ∈ Keep
        · refine ⟨∅, {i}, ?_, ?_⟩
          · intro k hk
            simp only [Finset.mem_singleton] at hk
            subst hk
            exact ⟨hKeep, le_refl _⟩
          · intro U
            simp
        · have hgate : (sL i && sR i) = false := by
            have := gateVal_unfold C S i
            rw [hm] at this
            exact this.symm
          -- Helper to expand a side (B, F) that is false at S
          have expand_side : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
              AndCountCircuit.sideTrue S B F i (C.gateVal S) = false →
              (∀ j ∈ F, j < i) →
              ∃ (V : Finset (Fin 42)) (G : Finset (Fin C.size)),
                (∀ k ∈ G, k ∈ Keep ∧ k < i) ∧
                (∀ U : Finset (Fin 42),
                  AndCountCircuit.sideTrue (U ∪ S) B F i (C.gateVal (U ∪ S)) = true ↔
                    (∃ v ∈ V, v ∈ U) ∨ (∃ k ∈ G, C.gateVal (U ∪ S) k = true)) := by
            intro B F hFfalse hFlt
            have hBS : ∀ v ∈ B, v ∉ S := by
              intro v hvB hvS
              have : AndCountCircuit.sideTrue S B F i (C.gateVal S) = true := by
                rw [sideTrue_def, decide_eq_true_eq]
                exact Or.inl ⟨v, hvB, hvS⟩
              rw [this] at hFfalse; exact Bool.noConfusion hFfalse
            have hFS : ∀ j ∈ F, C.gateVal S j = false := by
              intro j hjF
              cases hval : C.gateVal S j
              · rfl
              · have : AndCountCircuit.sideTrue S B F i (C.gateVal S) = true := by
                  rw [sideTrue_def, decide_eq_true_eq]
                  exact Or.inr ⟨j, hjF, hFlt j hjF, hval⟩
                rw [this] at hFfalse; exact Bool.noConfusion hFfalse
            have hexp : ∀ j : Fin C.size, ∃ (Vj : Finset (Fin 42)) (Gj : Finset (Fin C.size)),
                j ∈ F → (∀ k ∈ Gj, k ∈ Keep ∧ k ≤ j) ∧
                  (∀ U : Finset (Fin 42), C.gateVal (U ∪ S) j = true ↔
                    (∃ v ∈ Vj, v ∈ U) ∨ (∃ k ∈ Gj, C.gateVal (U ∪ S) k = true)) := by
              intro j
              by_cases hjF : j ∈ F
              · obtain ⟨Vj, Gj, h1, h2⟩ := ih j.val (by have := hFlt j hjF; omega) j rfl (hFS j hjF)
                exact ⟨Vj, Gj, fun _ => ⟨h1, h2⟩⟩
              · exact ⟨∅, ∅, fun h => absurd h hjF⟩
            choose fV fG hf using hexp
            refine ⟨B ∪ F.biUnion fV, F.biUnion fG, ?_, ?_⟩
            · intro k hk
              rw [Finset.mem_biUnion] at hk
              obtain ⟨j, hjF, hkG⟩ := hk
              obtain ⟨hkK, hkj⟩ := (hf j hjF).1 k hkG
              exact ⟨hkK, lt_of_le_of_lt hkj (hFlt j hjF)⟩
            · intro U
              rw [sideTrue_def]
              simp only [decide_eq_true_eq]
              constructor
              · rintro (⟨v, hvB, hvUS⟩ | ⟨j, hjF, _, hjv⟩)
                · rw [Finset.mem_union] at hvUS
                  rcases hvUS with hvU | hvS
                  · exact Or.inl ⟨v, Finset.mem_union_left _ hvB, hvU⟩
                  · exact absurd hvS (hBS v hvB)
                · rcases ((hf j hjF).2 U).mp hjv with ⟨v, hvVj, hvU⟩ | ⟨k, hkGj, hkv⟩
                  · exact Or.inl ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjF, hvVj⟩), hvU⟩
                  · exact Or.inr ⟨k, Finset.mem_biUnion.mpr ⟨j, hjF, hkGj⟩, hkv⟩
              · rintro (⟨v, hvV, hvU⟩ | ⟨k, hkG, hkv⟩)
                · rw [Finset.mem_union] at hvV
                  rcases hvV with hvB | hvBi
                  · exact Or.inl ⟨v, hvB, Finset.mem_union_left _ hvU⟩
                  · rw [Finset.mem_biUnion] at hvBi
                    obtain ⟨j, hjF, hvVj⟩ := hvBi
                    exact Or.inr ⟨j, hjF, hFlt j hjF, ((hf j hjF).2 U).mpr (Or.inl ⟨v, hvVj, hvU⟩)⟩
                · rw [Finset.mem_biUnion] at hkG
                  obtain ⟨j, hjF, hkGj⟩ := hkG
                  exact Or.inr ⟨j, hjF, hFlt j hjF, ((hf j hjF).2 U).mpr (Or.inr ⟨k, hkGj, hkv⟩)⟩
          cases hsL : sL i
          · -- sL i = false, so sR i must be true (since i ∉ Keep)
            have hsR : sR i = true := by
              cases h : sR i
              · exfalso; apply hKeep
                simp only [Keep, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hsL, h⟩
              · rfl
            obtain ⟨V, G, hVG, hEval⟩ := expand_side (C.leftVars i) (C.leftGates i) hsL (hWF i).1
            refine ⟨V, G, fun k hk => ⟨(hVG k hk).1, le_of_lt (hVG k hk).2⟩, ?_⟩
            intro U
            rw [gateVal_unfold C (U ∪ S) i, Bool.and_eq_true]
            have hrTrue : AndCountCircuit.sideTrue (U ∪ S) (C.rightVars i) (C.rightGates i) i
                (C.gateVal (U ∪ S)) = true := by
              have hSsub : S ⊆ U ∪ S := Finset.subset_union_right
              dsimp only [sR] at hsR
              rw [sideTrue_def, decide_eq_true_eq] at hsR ⊢
              rcases hsR with ⟨v, hvB, hvS⟩ | ⟨j, hjF, hji, hjv⟩
              · exact Or.inl ⟨v, hvB, hSsub hvS⟩
              · exact Or.inr ⟨j, hjF, hji, gateVal_mono C hSsub C.size j hjv⟩
            simp only [hrTrue, and_true]
            exact hEval U
          · -- sL i = true, so sR i = false
            have hsR : sR i = false := by
              rw [hsL] at hgate
              simpa using hgate
            obtain ⟨V, G, hVG, hEval⟩ := expand_side (C.rightVars i) (C.rightGates i) hsR (hWF i).2
            refine ⟨V, G, fun k hk => ⟨(hVG k hk).1, le_of_lt (hVG k hk).2⟩, ?_⟩
            intro U
            rw [gateVal_unfold C (U ∪ S) i, Bool.and_eq_true]
            have hlTrue : AndCountCircuit.sideTrue (U ∪ S) (C.leftVars i) (C.leftGates i) i
                (C.gateVal (U ∪ S)) = true := by
              have hSsub : S ⊆ U ∪ S := Finset.subset_union_right
              dsimp only [sL] at hsL
              rw [sideTrue_def, decide_eq_true_eq] at hsL ⊢
              rcases hsL with ⟨v, hvB, hvS⟩ | ⟨j, hjF, hji, hjv⟩
              · exact Or.inl ⟨v, hvB, hSsub hvS⟩
              · exact Or.inr ⟨j, hjF, hji, gateVal_mono C hSsub C.size j hjv⟩
            simp only [hlTrue, true_and]
            exact hEval U
    -- Choose expansion for every gate j (valid when gateVal S j = false)
    have expand_all : ∀ j : Fin C.size, ∃ (Vj : Finset (Fin 42)) (Gj : Finset (Fin C.size)),
        C.gateVal S j = false → (∀ k ∈ Gj, k ∈ Keep ∧ k ≤ j) ∧
          (∀ U : Finset (Fin 42), C.gateVal (U ∪ S) j = true ↔
            (∃ v ∈ Vj, v ∈ U) ∨ (∃ k ∈ Gj, C.gateVal (U ∪ S) k = true)) := by
      intro j
      by_cases hj : C.gateVal S j = false
      · obtain ⟨Vj, Gj, h1, h2⟩ := expand_exists j.val j rfl hj
        exact ⟨Vj, Gj, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨∅, ∅, fun h => absurd h hj⟩
    choose eV eG he using expand_all
    let emb : Fin Keep.card ↪o Fin C.size := Keep.orderEmbOfFin rfl
    let pullG : Finset (Fin C.size) → Finset (Fin Keep.card) := fun G =>
      Finset.univ.filter fun idx => emb idx ∈ G
    let D : AndCountCircuit 42 := {
      size := Keep.card
      leftVars := fun idx => C.leftVars (emb idx) ∪ (C.leftGates (emb idx)).biUnion eV
      leftGates := fun idx => pullG ((C.leftGates (emb idx)).biUnion eG)
      rightVars := fun idx => C.rightVars (emb idx) ∪ (C.rightGates (emb idx)).biUnion eV
      rightGates := fun idx => pullG ((C.rightGates (emb idx)).biUnion eG)
      outVars := C.outVars ∪ C.outGates.biUnion eV
      outGates := pullG (C.outGates.biUnion eG)
    }
    have hD_WF : D.WellFormed := by
      intro idx
      have hiK : emb idx ∈ Keep := Keep.orderEmbOfFin_mem rfl idx
      obtain ⟨hsL_i, hsR_i⟩ := (Finset.mem_filter.mp hiK).2
      constructor
      · intro idx' hidx'
        simp only [D, pullG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hidx'
        obtain ⟨j, hjG, hkj⟩ := hidx'
        have hjlt : j < emb idx := (hWF (emb idx)).1 j hjG
        have hjS : C.gateVal S j = false := by
          cases hval : C.gateVal S j
          · rfl
          · have : sL (emb idx) = true := by
              dsimp only [sL]; rw [sideTrue_def, decide_eq_true_eq]
              exact Or.inr ⟨j, hjG, hjlt, hval⟩
            rw [this] at hsL_i; exact Bool.noConfusion hsL_i
        have hle : emb idx' ≤ j := ((he j hjS).1 (emb idx') hkj).2
        exact emb.lt_iff_lt.mp (lt_of_le_of_lt hle hjlt)
      · intro idx' hidx'
        simp only [D, pullG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hidx'
        obtain ⟨j, hjG, hkj⟩ := hidx'
        have hjlt : j < emb idx := (hWF (emb idx)).2 j hjG
        have hjS : C.gateVal S j = false := by
          cases hval : C.gateVal S j
          · rfl
          · have : sR (emb idx) = true := by
              dsimp only [sR]; rw [sideTrue_def, decide_eq_true_eq]
              exact Or.inr ⟨j, hjG, hjlt, hval⟩
            rw [this] at hsR_i; exact Bool.noConfusion hsR_i
        have hle : emb idx' ≤ j := ((he j hjS).1 (emb idx') hkj).2
        exact emb.lt_iff_lt.mp (lt_of_le_of_lt hle hjlt)
    -- Prove D.gateVal U idx = C.gateVal (U ∪ S) (emb idx) by strong induction on idx.val
    have hD_gate : ∀ (U : Finset (Fin 42)) (m : ℕ) (idx : Fin D.size),
        idx.val = m → D.gateVal U idx = C.gateVal (U ∪ S) (emb idx) := by
      intro U m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro idx hidx
        rw [gateVal_unfold D U idx, gateVal_unfold C (U ∪ S) (emb idx)]
        have hiK : emb idx ∈ Keep := Keep.orderEmbOfFin_mem rfl idx
        obtain ⟨hsL_i, hsR_i⟩ := (Finset.mem_filter.mp hiK).2
        have side_eq : ∀ (B : Finset (Fin 42)) (F : Finset (Fin C.size)),
            AndCountCircuit.sideTrue S B F (emb idx) (C.gateVal S) = false →
            (∀ j ∈ F, j < emb idx) →
            AndCountCircuit.sideTrue U (B ∪ F.biUnion eV) (pullG (F.biUnion eG)) idx (D.gateVal U) =
            AndCountCircuit.sideTrue (U ∪ S) B F (emb idx) (C.gateVal (U ∪ S)) := by
          intro B F hFfalse hFlt
          have hBS : ∀ v ∈ B, v ∉ S := by
            intro v hvB hvS
            have : AndCountCircuit.sideTrue S B F (emb idx) (C.gateVal S) = true := by
              rw [sideTrue_def]; simp only [decide_eq_true_eq]
              exact Or.inl ⟨v, hvB, hvS⟩
            rw [this] at hFfalse; exact Bool.noConfusion hFfalse
          have hFS : ∀ j ∈ F, C.gateVal S j = false := by
            intro j hjF
            cases hval : C.gateVal S j
            · rfl
            · have : AndCountCircuit.sideTrue S B F (emb idx) (C.gateVal S) = true := by
                rw [sideTrue_def, decide_eq_true_eq]
                exact Or.inr ⟨j, hjF, hFlt j hjF, hval⟩
              rw [this] at hFfalse; exact Bool.noConfusion hFfalse
          rw [sideTrue_def, sideTrue_def]
          congr 1; apply propext; constructor
          · rintro (⟨v, hvV, hvU⟩ | ⟨idx', hidx'G, hlt', hv'⟩)
            · rw [Finset.mem_union] at hvV
              rcases hvV with hvB | hvBi
              · exact Or.inl ⟨v, hvB, Finset.mem_union_left _ hvU⟩
              · rw [Finset.mem_biUnion] at hvBi
                obtain ⟨j, hjF, hvVj⟩ := hvBi
                exact Or.inr ⟨j, hjF, hFlt j hjF, ((he j (hFS j hjF)).2 U).mpr (Or.inl ⟨v, hvVj, hvU⟩)⟩
            · simp only [pullG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hidx'G
              obtain ⟨j, hjF, hkj⟩ := hidx'G
              rw [ih idx'.val (by omega) idx' rfl] at hv'
              exact Or.inr ⟨j, hjF, hFlt j hjF, ((he j (hFS j hjF)).2 U).mpr (Or.inr ⟨emb idx', hkj, hv'⟩)⟩
          · rintro (⟨v, hvB, hvUS⟩ | ⟨j, hjF, _, hjv⟩)
            · rw [Finset.mem_union] at hvUS
              rcases hvUS with hvU | hvS
              · exact Or.inl ⟨v, Finset.mem_union_left _ hvB, hvU⟩
              · exact absurd hvS (hBS v hvB)
            · rcases ((he j (hFS j hjF)).2 U).mp hjv with ⟨v, hvVj, hvU⟩ | ⟨k, hkGj, hkv⟩
              · exact Or.inl ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjF, hvVj⟩), hvU⟩
              · obtain ⟨hkK, hkj⟩ := (he j (hFS j hjF)).1 k hkGj
                have hrange : k ∈ Set.range emb := by
                  rw [Finset.range_orderEmbOfFin]; exact hkK
                obtain ⟨idx', rfl⟩ := hrange
                have hlt' : idx' < idx := emb.lt_iff_lt.mp (lt_of_le_of_lt hkj (hFlt j hjF))
                refine Or.inr ⟨idx', ?_, hlt', ?_⟩
                · simp only [pullG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
                  exact ⟨j, hjF, hkGj⟩
                · rw [ih idx'.val (by omega) idx' rfl]; exact hkv
        change (AndCountCircuit.sideTrue U (C.leftVars (emb idx) ∪ (C.leftGates (emb idx)).biUnion eV)
            (pullG ((C.leftGates (emb idx)).biUnion eG)) idx (D.gateVal U) &&
          AndCountCircuit.sideTrue U (C.rightVars (emb idx) ∪ (C.rightGates (emb idx)).biUnion eV)
            (pullG ((C.rightGates (emb idx)).biUnion eG)) idx (D.gateVal U)) = _
        rw [side_eq (C.leftVars (emb idx)) (C.leftGates (emb idx)) hsL_i (hWF (emb idx)).1,
            side_eq (C.rightVars (emb idx)) (C.rightGates (emb idx)) hsR_i (hWF (emb idx)).2]
    -- Prove D.eval U = C.eval (U ∪ S)
    have hD_eval : ∀ U : Finset (Fin 42), D.eval U = C.eval (U ∪ S) := by
      intro U
      rw [eval_def, eval_def]
      congr 1; apply propext; constructor
      · rintro (⟨v, hvO, hvU⟩ | ⟨idx, hidxO, hval⟩)
        · simp only [D, Finset.mem_union, Finset.mem_biUnion] at hvO
          rcases hvO with hvC | ⟨j, hjO, hvVj⟩
          · exact Or.inl ⟨v, hvC, Finset.mem_union_left _ hvU⟩
          · exact Or.inr ⟨j, hjO, ((he j (hS_outG j hjO)).2 U).mpr (Or.inl ⟨v, hvVj, hvU⟩)⟩
        · simp only [D, pullG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hidxO
          obtain ⟨j, hjO, hkj⟩ := hidxO
          rw [hD_gate U idx.val idx rfl] at hval
          exact Or.inr ⟨j, hjO, ((he j (hS_outG j hjO)).2 U).mpr (Or.inr ⟨emb idx, hkj, hval⟩)⟩
      · rintro (⟨v, hvO, hvUS⟩ | ⟨j, hjO, hjv⟩)
        · rw [Finset.mem_union] at hvUS
          rcases hvUS with hvU | hvS
          · exact Or.inl ⟨v, Finset.mem_union_left _ hvO, hvU⟩
          · exact absurd hvS (hS_outV v hvO)
        · rcases ((he j (hS_outG j hjO)).2 U).mp hjv with ⟨v, hvVj, hvU⟩ | ⟨k, hkGj, hkv⟩
          · exact Or.inl ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hjO, hvVj⟩), hvU⟩
          · have hkK := ((he j (hS_outG j hjO)).1 k hkGj).1
            have hrange : k ∈ Set.range emb := by
              rw [Finset.range_orderEmbOfFin]; exact hkK
            obtain ⟨idx, rfl⟩ := hrange
            refine Or.inr ⟨idx, ?_, ?_⟩
            · simp only [D, pullG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
              exact ⟨j, hjO, hkGj⟩
            · rw [hD_gate U idx.val idx rfl]; exact hkv
    -- Prove Keep.card + deg_C(S) ≤ C.size
    have hD_card : D.size + (Finset.univ.filter fun i : Fin C.size =>
        ∃ v ∈ S, v ∈ C.leftVars i ∨ v ∈ C.rightVars i).card ≤ C.size := by
      have hdisjK : Disjoint Keep (Finset.univ.filter fun i : Fin C.size =>
          ∃ v ∈ S, v ∈ C.leftVars i ∨ v ∈ C.rightVars i) := by
        rw [Finset.disjoint_left]
        intro i hiK hiR
        obtain ⟨hsL_i, hsR_i⟩ := (Finset.mem_filter.mp hiK).2
        obtain ⟨v, hvS, hvL | hvR⟩ := (Finset.mem_filter.mp hiR).2
        · have : sL i = true := by
            dsimp only [sL]; rw [sideTrue_def, decide_eq_true_eq]
            exact Or.inl ⟨v, hvL, hvS⟩
          rw [this] at hsL_i; exact Bool.noConfusion hsL_i
        · have : sR i = true := by
            dsimp only [sR]; rw [sideTrue_def, decide_eq_true_eq]
            exact Or.inl ⟨v, hvR, hvS⟩
          rw [this] at hsR_i; exact Bool.noConfusion hsR_i
      have hunion := Finset.card_union_of_disjoint hdisjK
      have hle : (Keep ∪ Finset.univ.filter fun i : Fin C.size =>
          ∃ v ∈ S, v ∈ C.leftVars i ∨ v ∈ C.rightVars i).card ≤ (Finset.univ : Finset (Fin C.size)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_univ, Fintype.card_fin] at hle
      change Keep.card + _ ≤ C.size
      omega
    exact ⟨D, hD_WF, hD_card, hD_eval⟩
  -- Assemble the three conclusions
  refine ⟨h_full C hWF hComp, ?_, ?_⟩
  · -- Part 2: single vertex v
    intro v
    have hv_false : C.eval {v} = false := by
      rw [eval_def]
      simp [hOut, hSing]
    obtain ⟨D, hDWF, hDcard, hDeval⟩ := restrict_elim {v} hv_false
    have hD16 : 16 ≤ D.size := by
      apply h_one v D hDWF
      intro U hvU hnoAdj
      rw [hDeval U, hComp (U ∪ {v})]
      constructor
      · rintro ⟨a, ha, b, hb, hadj⟩
        simp only [Finset.mem_union, Finset.mem_singleton] at ha hb
        rcases ha with haU | rfl <;> rcases hb with hbU | rfl
        · exact ⟨a, haU, b, hbU, hadj⟩
        · exact absurd hadj.symm (hnoAdj a haU)
        · exact absurd hadj (hnoAdj b hbU)
        · exact absurd rfl hadj.ne
      · rintro ⟨a, haU, b, hbU, hadj⟩
        exact ⟨a, Finset.mem_union_left _ haU, b, Finset.mem_union_left _ hbU, hadj⟩
    have hncard : {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard =
        (Finset.univ.filter fun i : Fin C.size =>
          ∃ w ∈ ({v} : Finset (Fin 42)), w ∈ C.leftVars i ∨ w ∈ C.rightVars i).card := by
      rw [← Set.ncard_coe_finset]
      congr 1; ext i; simp
    rw [hncard]
    omega
  · -- Part 3: non-incident point p < 21 and line l >= 21
    intro p l hp hl hnotAdj
    have hpl_false : C.eval {p, l} = false := by
      cases hval : C.eval {p, l}
      · rfl
      · exfalso
        obtain ⟨a, ha, b, hb, hadj⟩ := (hComp {p, l}).mp hval
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact hadj.ne rfl
        · exact hnotAdj hadj
        · exact hnotAdj hadj.symm
        · exact hadj.ne rfl
    obtain ⟨D, hDWF, hDcard, hDeval⟩ := restrict_elim {p, l} hpl_false
    have hD14 : 14 ≤ D.size := by
      apply h_two p l hp hl hnotAdj D hDWF
      intro U hpU hlU hnoAdj
      rw [hDeval U, hComp (U ∪ {p, l})]
      constructor
      · rintro ⟨a, ha, b, hb, hadj⟩
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with haU | rfl | rfl <;> rcases hb with hbU | rfl | rfl
        · exact ⟨a, haU, b, hbU, hadj⟩
        · exact absurd hadj.symm (hnoAdj a haU).1
        · exact absurd hadj.symm (hnoAdj a haU).2
        · exact absurd hadj (hnoAdj b hbU).1
        · exact absurd rfl hadj.ne
        · exact absurd hadj hnotAdj
        · exact absurd hadj (hnoAdj b hbU).2
        · exact absurd hadj.symm hnotAdj
        · exact absurd rfl hadj.ne
      · rintro ⟨a, haU, b, hbU, hadj⟩
        exact ⟨a, Finset.mem_union_left _ haU, b, Finset.mem_union_left _ hbU, hadj⟩
    have hncard : {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i ∨
        l ∈ C.leftVars i ∨ l ∈ C.rightVars i}.ncard =
        (Finset.univ.filter fun i : Fin C.size =>
          ∃ w ∈ ({p, l} : Finset (Fin 42)), w ∈ C.leftVars i ∨ w ∈ C.rightVars i).card := by
      rw [← Set.ncard_coe_finset]
      congr 1; ext i; simp [or_assoc]
    rw [hncard]
    omega
