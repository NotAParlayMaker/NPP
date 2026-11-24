import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3523_aux

def leftVertex {n m : ℕ} (v : Fin n) : Fin (n + m) :=
  Fin.castAdd m v

def rightVertex {n m : ℕ} (v : Fin m) : Fin (n + m) :=
  Fin.natAdd n v

theorem leftInjective (n m : ℕ) :
    Function.Injective (leftVertex (n := n) (m := m)) := by
  intro a b same
  have values := congrArg (fun w : Fin (n + m) => w.val) same
  exact Fin.ext values

theorem rightInjective (n m : ℕ) :
    Function.Injective (rightVertex (n := n) (m := m)) := by
  intro a b same
  apply Fin.ext
  have values := congrArg Fin.val same
  change n + a.val = n + b.val at values
  exact Nat.add_left_cancel values

theorem oppositeDistinct {n m : ℕ} (v : Fin n) (w : Fin m) :
    leftVertex (m := m) v ≠ rightVertex (n := n) w := by
  intro same
  have values := congrArg Fin.val same
  change v.val = n + w.val at values
  have bound := v.isLt
  omega

def edgeLabel {n m : ℕ} (e : Fin n × Fin m) : Sym2 (Fin (n + m)) :=
  s(leftVertex e.1, rightVertex e.2)

theorem edgeLabelInjective (n m : ℕ) :
    Function.Injective (edgeLabel (n := n) (m := m)) := by
  intro e f same
  rcases Sym2.eq_iff.mp same with ordered | reversed
  · exact Prod.ext (leftInjective n m ordered.1) (rightInjective n m ordered.2)
  · exact (oppositeDistinct e.1 f.2 reversed.1).elim

def incidence {n m : ℕ} (E : Finset (Fin n × Fin m)) :
    SimpleGraph (Fin (n + m)) where
  Adj a b := ∃ e ∈ E, (a = leftVertex e.1 ∧ b = rightVertex e.2) ∨
    (b = leftVertex e.1 ∧ a = rightVertex e.2)
  symm := ⟨fun _ _ ⟨e, mem, ends⟩ => ⟨e, mem, ends.symm⟩⟩
  loopless := ⟨by
    rintro a ⟨e, _, ends | ends⟩
    · exact oppositeDistinct e.1 e.2 (ends.1.symm.trans ends.2)
    · exact oppositeDistinct e.1 e.2 (ends.1.symm.trans ends.2)⟩

theorem incidenceEdgeSet {n m : ℕ} (E : Finset (Fin n × Fin m)) :
    (incidence E).edgeSet = (E.image edgeLabel : Set (Sym2 (Fin (n + m)))) := by
  ext edge
  induction edge using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨e, mem, ends | ends⟩
      · exact ⟨e, mem, Sym2.eq_iff.mpr (Or.inl ⟨ends.1.symm, ends.2.symm⟩)⟩
      · exact ⟨e, mem, Sym2.eq_iff.mpr (Or.inr ⟨ends.1.symm, ends.2.symm⟩)⟩
    · rintro ⟨e, mem, equal⟩
      rcases Sym2.eq_iff.mp equal with ordered | reversed
      · exact ⟨e, mem, Or.inl ⟨ordered.1.symm, ordered.2.symm⟩⟩
      · exact ⟨e, mem, Or.inr ⟨reversed.1.symm, reversed.2.symm⟩⟩

theorem incidenceEdgeCount {n m : ℕ} (E : Finset (Fin n × Fin m)) :
    (incidence E).edgeSet.ncard = E.card := by
  rw [incidenceEdgeSet, Set.ncard_coe_finset, Finset.card_image_of_injective E (edgeLabelInjective n m)]

theorem matchingCoverCount {n m : ℕ} (E M : Finset (Fin n × Fin m)) (within : M ⊆ E)
    (leftUnique : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (rightUnique : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (T : Finset (Fin (n + m))) (cover : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (incidence E) T) :
    M.card ≤ T.card := by
  classical
  have chooseEnd (e : ↑M) :
      ∃ v : ↑T, v.val = leftVertex e.val.1 ∨ v.val = rightVertex e.val.2 := by
    have adj : (incidence E).Adj (leftVertex e.val.1) (rightVertex e.val.2) :=
      ⟨e.val, within e.property, Or.inl ⟨rfl, rfl⟩⟩
    rcases cover _ _ adj with ha | hb
    · exact ⟨⟨_, ha⟩, Or.inl rfl⟩
    · exact ⟨⟨_, hb⟩, Or.inr rfl⟩
  choose select ends using chooseEnd
  have injective : Function.Injective select := by
    intro e f same
    have vertex := congrArg Subtype.val same
    apply Subtype.ext
    rcases ends e with onLeft | onRight <;> rcases ends f with leftF | rightF
    · exact leftUnique _ e.property _ f.property (leftInjective n m (onLeft.symm.trans (vertex.trans leftF)))
    · exact (oppositeDistinct e.val.1 f.val.2 (onLeft.symm.trans (vertex.trans rightF))).elim
    · exact (oppositeDistinct f.val.1 e.val.2 (leftF.symm.trans (vertex.symm.trans onRight))).elim
    · exact rightUnique _ e.property _ f.property (rightInjective n m (onRight.symm.trans (vertex.trans rightF)))
  simpa using Fintype.card_le_of_injective select injective

end PEqualNP.Outside.L_meta_3523_aux

open PEqualNP.Outside.L_meta_3523_aux

theorem PEqualNP.Outside.L_meta_3523 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) → (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.2 = x9.2 → x7 = x9) → ∃ (x8 : SimpleGraph (Fin (x1 + x2))), (∀ (x9 x10 : Fin (x1 + x2)), x8.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) ∧ x8.edgeSet.ncard = x3.card ∧ ∀ (x9 : Finset (Fin (x1 + x2))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x8 x9 → x4.card ≤ x9.card := by
  intro n m E M within leftUnique rightUnique
  exact ⟨incidence E, fun _ _ => Iff.rfl, incidenceEdgeCount E,
    matchingCoverCount E M within leftUnique rightUnique⟩
