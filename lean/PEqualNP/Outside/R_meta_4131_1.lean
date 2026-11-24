import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Reduce L-meta-4131 by the deficit d = B - |U*|: the case d = 0, the middle
-- cases 1 <= d <= 5, and the case d = 6. When d >= 7 the bound is immediate
-- from X subset T and T.card = 7.
theorem PEqualNP.Outside.R_meta_4131_1
    (zero :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → B < 2*U.card → B = U.card →
        ∀ T X : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T → X ⊆ T →
          (G.deleteEdges ↑U).IsVertexCover ↑(T \ X) → X.card ≤ B - U.card)
    (mid :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → B < 2*U.card → 1 ≤ B - U.card → B - U.card ≤ 5 →
        ∀ T X : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T → X ⊆ T →
          (G.deleteEdges ↑U).IsVertexCover ↑(T \ X) → X.card ≤ B - U.card)
    (six :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        U.card ≤ B → B < 2*U.card → B - U.card = 6 →
        ∀ T X : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T → X ⊆ T →
          (G.deleteEdges ↑U).IsVertexCover ↑(T \ X) → X.card ≤ B - U.card) :
    have es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    let G : SimpleGraph (Fin 11) := edgeGraph 11 es
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      have U : Finset (Sym2 (Fin 11)) := Ustar G C
      have B : ℕ := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      U.card ≤ B → B < 2*U.card → ∀ T X : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T →
        X ⊆ T → (G.deleteEdges ↑U).IsVertexCover ↑(T \ X) → X.card ≤ B - U.card := by
  intro es G C hsize least top hjunk U B hlo hhi T X hT coverT hX coverCut
  by_cases h0 : B = U.card
  · exact zero C hsize least top hjunk hlo hhi h0 T X hT coverT hX coverCut
  · have hd1 : 1 ≤ B - U.card := by omega
    by_cases h5 : B - U.card ≤ 5
    · exact mid C hsize least top hjunk hlo hhi hd1 h5 T X hT coverT hX coverCut
    · by_cases h6 : B - U.card = 6
      · exact six C hsize least top hjunk hlo hhi h6 T X hT coverT hX coverCut
      · have hXle : X.card ≤ 7 := (Finset.card_le_card hX).trans_eq hT
        omega
