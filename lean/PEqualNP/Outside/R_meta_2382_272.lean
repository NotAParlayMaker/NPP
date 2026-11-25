import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2382_272
    (tiny :
      let G := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        let Z := (centreless G C).card
        let O := (orN G C \ lam G C).card
        (O = 0 ∨ (O ≤ 1 ∧ Z = 0)) →
        (Ustar G C).card ≤ 2 * Z + O + 2)
    (core :
      let G := edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C →
        let U := Ustar G C
        let J := junk G C
        let O := (orN G C \ lam G C).card
        let B := 2 * (centreless G C).card + O
        let D := fun S => J.filter fun j => ¬ Disjoint S (gammaE G C j)
        2 ≤ J.card → 0 < O → 2 ≤ B → B + J.card < U.card →
        U ⊆ J.biUnion (gammaE G C) →
        ∀ V ⊆ U, V.card = B + (D V).card + 1 →
          (∀ W ⊂ V, W.card ≤ B + (D W).card) → False) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           (∀ (x9 x10 : Fin (11 : ℕ)), s(x9, x10) ∈ x7 → ∃ x12 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → x8 < (2 : ℕ) * x7.card → x7.card ≤ x8 := by
  classical
  let G := edgeGraph 11
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  dsimp only
  intro C hsize hleast htop hj hcover _
  let U := Ustar G C
  let J := junk G C
  let Z := (centreless G C).card
  let O := (orN G C \ lam G C).card
  let B := 2 * Z + O
  let D (S : Finset (Sym2 (Fin 11))) := J.filter fun j => ¬ Disjoint S (gammaE G C j)
  change 2 ≤ J.card at hj
  change U.card ≤ 2 * Z + J.card + O
  by_contra! hfail
  have hdefect : B + J.card < U.card := by dsimp [B]; omega
  have htiny : ¬ (O = 0 ∨ (O ≤ 1 ∧ Z = 0)) := by
    intro h
    have hbound := tiny C hleast htop h
    change U.card ≤ 2 * Z + O + 2 at hbound
    omega
  have hO : 0 < O := by
    by_contra! h
    exact htiny (Or.inl (by omega))
  have hB : 2 ≤ B := by
    by_contra! h
    exact htiny (Or.inr (by dsimp [B] at h; omega))
  have hDU : (D U).card ≤ J.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hmono {S T : Finset (Sym2 (Fin 11))} (hST : S ⊆ T) : D S ⊆ D T := by
    intro j hj
    obtain ⟨hjJ, hjD⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjJ, fun hd => hjD (hd.mono_left hST)⟩
  have minimize (S : Finset (Sym2 (Fin 11))) :
      B + (D S).card < S.card →
        ∃ V ⊆ S, V.card = B + (D V).card + 1 ∧
          ∀ W ⊂ V, W.card ≤ B + (D W).card := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro hS
      by_cases hex : ∃ W ⊂ S, B + (D W).card < W.card
      · obtain ⟨W, hWS, hW⟩ := hex
        obtain ⟨V, hVW, hV, hmin⟩ := ih W hWS hW
        exact ⟨V, hVW.trans hWS.le, hV, hmin⟩
      · have hmin (W : Finset (Sym2 (Fin 11))) (hWS : W ⊂ S) :
            W.card ≤ B + (D W).card := by
          by_contra! hW
          exact hex ⟨W, hWS, hW⟩
        obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
        have hbound := hmin (S.erase e) (Finset.erase_ssubset he)
        have hmonoCard := Finset.card_le_card (hmono (Finset.erase_subset e S))
        have herase := Finset.card_erase_add_one he
        exact ⟨S, Finset.Subset.rfl, by omega, hmin⟩
  obtain ⟨V, hVU, hV, hmin⟩ := minimize U (by omega)
  have hcovered : U ⊆ J.biUnion (gammaE G C) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      obtain ⟨j, hjJ, hval⟩ := hcover u v he
      exact Finset.mem_biUnion.mpr ⟨j, hjJ,
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hval⟩⟩
  exact core C hsize hleast htop hj hO hB hdefect hcovered V hVU hV hmin
