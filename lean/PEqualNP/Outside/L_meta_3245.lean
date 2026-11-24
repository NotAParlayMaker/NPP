import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

private def Along (B : ℕ) (gs : List Gate) (P : ℕ → Gate → Prop) : Prop :=
  ∀ (i : ℕ) (hi : i < gs.length), P (B + i) gs[i]

private def Proper (w : ℕ) (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ r ∈ g.inputs, r < w

private def Cross (S T : Finset ℕ) (g : Gate) : Prop :=
  g.op = .and → ∃ a b, g.inputs = [a, b] ∧
    (a ∈ S ∧ b ∈ T ∨ a ∈ T ∧ b ∈ S)

private def Closed (L : Finset ℕ) (B : ℕ) (gs : List Gate) (S : Finset ℕ) : Prop :=
  ∀ w ∈ S, w ∈ L ∨ ∃ (i : ℕ) (hi : i < gs.length), w = B + i ∧
    gs[i].op = .or ∧ ∀ r ∈ gs[i].inputs, r ∈ S

private lemma alongAppend {B : ℕ} {gs ts : List Gate} {P : ℕ → Gate → Prop}
    (hgs : Along B gs P) (hts : Along (B + gs.length) ts P) :
    Along B (gs ++ ts) P := by
  intro i hi
  by_cases hg : i < gs.length
  · rw [List.getElem_append_left hg]
    exact hgs i hg
  · have ht : i - gs.length < ts.length := by simp at hi; omega
    rw [List.getElem_append_right (by omega)]
    convert hts (i - gs.length) ht using 1
    omega

private lemma closedAppend {L S U : Finset ℕ} {B : ℕ} {gs ts : List Gate}
    (hs : Closed L B gs S) (hu : Closed L (B + gs.length) ts U) :
    Closed L B (gs ++ ts) (S ∪ U) := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases hs w hw with hw | ⟨i, hi, hwire, hop, hinputs⟩
    · exact Or.inl hw
    · have hi' : i < (gs ++ ts).length := by simp; omega
      refine Or.inr ⟨i, hi', hwire, ?_, ?_⟩
      · rwa [List.getElem_append_left hi]
      · rw [List.getElem_append_left hi]
        exact fun r hr => Finset.mem_union_left _ (hinputs r hr)
  · rcases hu w hw with hw | ⟨i, hi, hwire, hop, hinputs⟩
    · exact Or.inl hw
    · have hi' : i + gs.length < (gs ++ ts).length := by simp; omega
      refine Or.inr ⟨i + gs.length, hi', by omega, ?_, ?_⟩
      · rw [← List.getElem_append_right' gs hi]
        exact hop
      · rw [← List.getElem_append_right' gs hi]
        exact fun r hr => Finset.mem_union_right _ (hinputs r hr)

private lemma crossMono {S T S' T' : Finset ℕ} {g : Gate}
    (hS : S ⊆ S') (hT : T ⊆ T') (h : Cross S T g) : Cross S' T' g := by
  intro hop
  obtain ⟨a, b, hab, ht | ht⟩ := h hop
  · exact ⟨a, b, hab, Or.inl ⟨hS ht.1, hT ht.2⟩⟩
  · exact ⟨a, b, hab, Or.inr ⟨hT ht.1, hS ht.2⟩⟩

private lemma crossSwap {S T : Finset ℕ} {g : Gate} (h : Cross S T g) : Cross T S g := by
  intro hop
  obtain ⟨a, b, hab, ht⟩ := h hop
  exact ⟨a, b, hab, ht.symm⟩

private def Certified (L R : Finset ℕ) (B : ℕ) (gs : List Gate) : Prop :=
  ∃ S T, L ⊆ S ∧ R ⊆ T ∧ Closed L B gs S ∧ Closed R B gs T ∧
    Along B gs (fun w g => Proper w g ∧ Cross S T g)

private lemma certifiedAppend {L R : Finset ℕ} {B : ℕ} {gs ts : List Gate}
    (hgs : Certified L R B gs) (hts : Certified L R (B + gs.length) ts) :
    Certified L R B (gs ++ ts) := by
  obtain ⟨S, T, hS, hT, hleft, hright, h⟩ := hgs
  obtain ⟨U, V, hU, hV, hleft', hright', h'⟩ := hts
  refine ⟨S ∪ U, T ∪ V, fun _ hw => Finset.mem_union_left _ (hS hw),
    fun _ hw => Finset.mem_union_left _ (hT hw), closedAppend hleft hleft',
    closedAppend hright hright', ?_⟩
  apply alongAppend
  · intro i hi
    exact ⟨(h i hi).1, crossMono (fun _ hw => Finset.mem_union_left _ hw)
      (fun _ hw => Finset.mem_union_left _ hw) (h i hi).2⟩
  · intro i hi
    exact ⟨(h' i hi).1, crossMono (fun _ hw => Finset.mem_union_right _ hw)
      (fun _ hw => Finset.mem_union_right _ hw) (h' i hi).2⟩

private lemma certifiedSwap {L R : Finset ℕ} {B : ℕ} {gs : List Gate}
    (h : Certified R L B gs) : Certified L R B gs := by
  obtain ⟨T, S, hT, hS, hright, hleft, hshape⟩ := h
  exact ⟨S, T, hS, hT, hleft, hright, fun i hi =>
    ⟨(hshape i hi).1, crossSwap (hshape i hi).2⟩⟩

private def accum (B v m i : ℕ) : ℕ :=
  (v :: (List.range m).map (fun j => B + j)).getD i 0

private lemma accumZero (B v m : ℕ) : accum B v m 0 = v := rfl

private lemma accumSucc {B v m i : ℕ} (hi : i < m) :
    accum B v m (i + 1) = B + i := by
  have hi' : i < ((List.range m).map (fun j => B + j)).length := by simpa using hi
  simp [accum, List.getD, List.getElem?_eq_getElem hi']

private lemma accumFacts {B v m : ℕ} {L : Finset ℕ} (hv : v ∈ L) (hvB : v < B)
    {i : ℕ} (hi : i ≤ m) :
    accum B v m i ∈ L ∪ Finset.Ico B (B + m) ∧ accum B v m i < B + i := by
  cases i with
  | zero => exact ⟨Finset.mem_union_left _ hv, by simpa [accumZero] using hvB⟩
  | succ i =>
    rw [accumSucc (by omega)]
    exact ⟨Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by omega⟩

private def chain (B v : ℕ) (rest : List ℕ) : List Gate :=
  (List.range rest.length).map (fun i => ⟨.or, [accum B v rest.length i, rest.getD i 0]⟩)

private def finish (B a t v : ℕ) (rest : List ℕ) (lead : Bool) : List Gate :=
  ⟨.and, [t, accum B v rest.length rest.length]⟩ ::
    (if lead then [] else [⟨.or, [a, B + rest.length]⟩])

private lemma chainLength (B v : ℕ) (rest : List ℕ) : (chain B v rest).length = rest.length := by
  simp [chain]

private lemma chainGate {B v : ℕ} {rest : List ℕ} {i : ℕ} (hi : i < (chain B v rest).length) :
    (chain B v rest)[i] = ⟨.or, [accum B v rest.length i, rest.getD i 0]⟩ := by
  simp [chain]

private lemma restGet {rest : List ℕ} {i : ℕ} (hi : i < rest.length) :
    rest.getD i 0 ∈ rest := by
  simp [List.getD, List.getElem?_eq_getElem hi]

private lemma blockCertified {L R : Finset ℕ} {B a t v : ℕ} {rest : List ℕ} {lead : Bool}
    (ht : t ∈ L) (hv : v ∈ R) (hrest : ∀ r ∈ rest, r ∈ R)
    (hL : ∀ w ∈ L, w < B) (hR : ∀ w ∈ R, w < B) (ha : lead = false → a < B) :
    Certified L R B (blockGates B a t v rest lead) := by
  let S := R ∪ Finset.Ico B (B + rest.length)
  have hRsub : R ⊆ S := fun _ hw => Finset.mem_union_left _ hw
  change Certified L R B (chain B v rest ++ finish B a t v rest lead)
  refine ⟨L, S, fun _ hw => hw, hRsub, fun _ hw => Or.inl hw, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl hw
    · obtain ⟨hmin, hmax⟩ := Finset.mem_Ico.mp hw
      let i := w - B
      have hi : i < rest.length := by dsimp [i]; omega
      have hic : i < (chain B v rest).length := by simpa [chainLength] using hi
      have hia : i < (chain B v rest ++ finish B a t v rest lead).length := by
        simp [chainLength]; omega
      refine Or.inr ⟨i, hia, by dsimp [i]; omega, ?_⟩
      rw [List.getElem_append_left hic, chainGate hic]
      refine ⟨rfl, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (accumFacts hv (hR v hv) (by omega)).1
      · exact hRsub (hrest _ (restGet hi))
  · apply alongAppend
    · intro i hi
      have hr : i < rest.length := by simpa [chainLength] using hi
      rw [chainGate hi]
      refine ⟨⟨Or.inr rfl, rfl, ?_⟩, by simp [Cross]⟩
      intro r hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact (accumFacts hv (hR v hv) (by omega)).2
      · have := hR _ (hrest _ (restGet hr))
        omega
    · intro i hi
      have hroot := accumFacts hv (hR v hv) (Nat.le_refl rest.length)
      let andGate : Gate := ⟨.and, [t, accum B v rest.length rest.length]⟩
      have hand : Proper (B + rest.length) andGate ∧ Cross L S andGate := by
        have hOwner := hL t ht
        refine ⟨⟨Or.inl rfl, rfl, ?_⟩, fun _ => ⟨t, _, rfl, Or.inl ⟨ht, hroot.1⟩⟩⟩
        intro r hmem
        simp only [andGate, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl
        · omega
        · exact hroot.2
      rw [chainLength]
      cases lead
      · simp [finish] at hi
        have hiCases : i = 0 ∨ i = 1 := by omega
        rcases hiCases with rfl | rfl
        · exact hand
        · change Proper (B + rest.length + 1) ⟨.or, [a, B + rest.length]⟩ ∧
            Cross L S ⟨.or, [a, B + rest.length]⟩
          refine ⟨⟨Or.inr rfl, rfl, ?_⟩, by simp [Cross]⟩
          intro r hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with rfl | rfl
          · have := ha rfl
            omega
          · omega
      · simp [finish] at hi
        have hzero : i = 0 := by omega
        subst i
        exact hand

private lemma coverCertified {L R : Finset ℕ} (own : List (ℕ × List ℕ))
    (hown : ∀ p ∈ own, p.2 ≠ [] ∧
      ((p.1 ∈ L ∧ ∀ r ∈ p.2, r ∈ R) ∨ (p.1 ∈ R ∧ ∀ r ∈ p.2, r ∈ L)))
    (B : ℕ) (lead : Bool) (a : ℕ) (hL : ∀ w ∈ L, w < B) (hR : ∀ w ∈ R, w < B)
    (ha : lead = false → a < B) : Certified L R B (coverGatesB B lead a own) := by
  induction own generalizing B lead a with
  | nil =>
    exact ⟨L, R, fun _ hw => hw, fun _ hw => hw, fun _ hw => Or.inl hw,
      fun _ hw => Or.inl hw, fun _ hi => by simp [coverGatesB] at hi⟩
  | cons p own ih =>
    obtain ⟨t, xs⟩ := p
    have hhead := hown (t, xs) (by simp)
    have htail : ∀ p ∈ own, p.2 ≠ [] ∧
        ((p.1 ∈ L ∧ ∀ r ∈ p.2, r ∈ R) ∨ (p.1 ∈ R ∧ ∀ r ∈ p.2, r ∈ L)) :=
      fun p hp => hown p (List.mem_cons_of_mem _ hp)
    cases xs with
    | nil => exact False.elim (hhead.1 rfl)
    | cons v rest =>
      let gs := blockGates B a t v rest lead
      have hgs : Certified L R B gs := by
        rcases hhead.2 with h | h
        · exact blockCertified h.1 (h.2 v (by simp))
            (fun r hr => h.2 r (List.mem_cons_of_mem _ hr)) hL hR ha
        · exact certifiedSwap (blockCertified h.1 (h.2 v (by simp))
            (fun r hr => h.2 r (List.mem_cons_of_mem _ hr)) hR hL ha)
      have hlen : 0 < gs.length := by simp [gs, blockGates]
      have hnext : B + gs.length - 1 < B + gs.length := by omega
      exact certifiedAppend hgs (ih htail (B + gs.length) false (B + gs.length - 1)
        (fun w hw => by have := hL w hw; omega)
        (fun w hw => by have := hR w hw; omega) (fun _ => hnext))

private lemma coverGatesEq (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split
  · rename_i h
    exact h.symm
  · rfl

private lemma gateAtEq {C : Circuit} {i : ℕ} (hi : i < C.gates.length) :
    gateAt C i = C.gates[i] := by
  simp [gateAt, List.getD, List.getElem?_eq_getElem hi]

end PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3245

theorem PEqualNP.Outside.L_meta_3245 :
    ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),
      have x4 : ℕ := x1 + x2;
      (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨
        x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →
      have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;
      have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;
      ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧
        (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length,
          x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧
        (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length,
          x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧
        ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧
            (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro l r own
  dsimp only
  intro hown
  let n := l + r
  let C := coverCircuitB n own
  let L := Finset.range l
  let R := Finset.Ico l n
  have hsides : ∀ p ∈ own, p.2 ≠ [] ∧
      ((p.1 ∈ L ∧ ∀ w ∈ p.2, w ∈ R) ∨ (p.1 ∈ R ∧ ∀ w ∈ p.2, w ∈ L)) := by
    simpa only [L, R, n, Finset.mem_range, Finset.mem_Ico, and_assoc] using hown
  have hcert : Certified L R n C.gates := by
    dsimp only [C]
    rw [coverGatesEq]
    apply coverCertified own hsides n true 0
    · intro w hw
      have := Finset.mem_range.mp hw
      dsimp [n]
      omega
    · exact fun _ hw => (Finset.mem_Ico.mp hw).2
    · simp
  obtain ⟨S, T, _, _, hclosedL, hclosedR, hshape⟩ := hcert
  change ∃ S T, PEqualNP.TopForm.IsAO2 n C ∧ _
  refine ⟨S, T, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hshape i hi).1.1
    · intro i hi w hw
      rw [gateAtEq hi] at hw
      exact (hshape i hi).1.2.2 w hw
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact (hshape i hi).1.2.1
  · intro w hw
    rcases hclosedL w hw with hw | ⟨i, hi, hiw, hop, hinputs⟩
    · exact Or.inl (Finset.mem_range.mp hw)
    · exact Or.inr ⟨i, hi, hiw, by rwa [gateAtEq hi], by rwa [gateAtEq hi]⟩
  · intro w hw
    rcases hclosedR w hw with hw | ⟨i, hi, hiw, hop, hinputs⟩
    · exact Or.inl (Finset.mem_Ico.mp hw)
    · exact Or.inr ⟨i, hi, hiw, by rwa [gateAtEq hi], by rwa [gateAtEq hi]⟩
  · intro i hi
    rw [gateAtEq hi]
    exact (hshape i hi).2
