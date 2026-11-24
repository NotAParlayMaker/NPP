import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Location (B : ℕ) (gs : List Gate) (w : ℕ) (g : Gate) : Prop :=
  ∃ i, gs[i]? = some g ∧ w = B+i

lemma loc_append (B : ℕ) (gs hs : List Gate) (w : ℕ) (g : Gate) :
    Location B (gs ++ hs) w g ↔ Location B gs w g ∨ Location (B+gs.length) hs w g := by
  constructor
  · rintro ⟨i,hi,rfl⟩
    by_cases h : i < gs.length
    · exact Or.inl ⟨i,by simpa [List.getElem?_append_left h] using hi,rfl⟩
    · exact Or.inr ⟨i-gs.length,by simpa [List.getElem?_append_right (by omega : gs.length ≤ i)] using hi,by omega⟩
  · rintro (⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩)
    · have h : i < gs.length := List.getElem?_eq_some_iff.mp hi |>.1
      exact ⟨i,by simpa [List.getElem?_append_left h] using hi,rfl⟩
    · refine ⟨gs.length+i,?_,by omega⟩
      simpa [List.getElem?_append_right (by omega : gs.length ≤ gs.length+i)] using hi

def Closed (X : Finset ℕ) (B : ℕ) (gs : List Gate) (P : Finset ℕ) :=
  ∀ w ∈ P, w ∈ X ∨ ∃ g, Location B gs w g ∧ g.op = .or ∧ ∀ v ∈ g.inputs, v ∈ P

def Good (P L : Finset ℕ) (w : ℕ) (g : Gate) :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
  (∀ v ∈ g.inputs, v < w) ∧ (g.op = .and → ∃ a b, g.inputs = [a,b] ∧
    (a ∈ P ∧ b ∈ L ∨ a ∈ L ∧ b ∈ P))

def Cert (X Y : Finset ℕ) (B : ℕ) (gs : List Gate) :=
  ∃ P L, Closed X B gs P ∧ Closed Y B gs L ∧ ∀ w g, Location B gs w g → Good P L w g

lemma good_mono {P L P' L' : Finset ℕ} {w g} (hp : P ⊆ P') (hl : L ⊆ L')
    (h : Good P L w g) : Good P' L' w g := by
  refine ⟨h.1,h.2.1,h.2.2.1,fun ha => ?_⟩
  obtain ⟨a,b,he,hx|hx⟩ := h.2.2.2 ha
  · exact ⟨a,b,he,Or.inl ⟨hp hx.1,hl hx.2⟩⟩
  · exact ⟨a,b,he,Or.inr ⟨hl hx.1,hp hx.2⟩⟩

lemma closed_append {X P Q : Finset ℕ} {B gs hs} (hp : Closed X B gs P)
    (hq : Closed X (B+gs.length) hs Q) : Closed X B (gs++hs) (P∪Q) := by
  intro w hw
  rcases Finset.mem_union.mp hw with h | h
  · rcases hp w h with h | ⟨g,loc,op,ins⟩
    · exact Or.inl h
    · exact Or.inr ⟨g,(loc_append ..).mpr (Or.inl loc),op,fun v hv => Finset.mem_union_left _ (ins v hv)⟩
  · rcases hq w h with h | ⟨g,loc,op,ins⟩
    · exact Or.inl h
    · exact Or.inr ⟨g,(loc_append ..).mpr (Or.inr loc),op,fun v hv => Finset.mem_union_right _ (ins v hv)⟩

lemma cert_append {X Y B gs hs} (h : Cert X Y B gs) (k : Cert X Y (B+gs.length) hs) :
    Cert X Y B (gs++hs) := by
  obtain ⟨P,L,hp,hl,hgood⟩ := h
  obtain ⟨Q,M,hq,hm,kgood⟩ := k
  refine ⟨_,_,closed_append hp hq,closed_append hl hm,fun w g hg => ?_⟩
  rcases (loc_append ..).mp hg with f | f
  · exact good_mono Finset.subset_union_left Finset.subset_union_left (hgood w g f)
  · exact good_mono Finset.subset_union_right Finset.subset_union_right (kgood w g f)

lemma cert_swap {X Y B gs} (h : Cert X Y B gs) : Cert Y X B gs := by
  obtain ⟨P,L,hp,hl,k⟩ := h
  refine ⟨L,P,hl,hp,fun w g loc => ?_⟩
  obtain ⟨op,sz,back,ha⟩ := k w g loc
  refine ⟨op,sz,back,fun eq => ?_⟩
  obtain ⟨a,b,he,h⟩ := ha eq
  exact ⟨a,b,he,h.symm⟩

lemma cert_nil (X Y : Finset ℕ) (B : ℕ) : Cert X Y B [] := by
  refine ⟨∅,∅,by simp [Closed],by simp [Closed],?_⟩
  rintro w g ⟨i,hi,_⟩
  simp at hi

def src (B v d i : ℕ) := (v :: (List.range d).map (fun j => B+j)).getD i 0

lemma prev_succ (B v d i : ℕ) (hi : i < d) : src B v d (i+1) = B+i := by
  simp [src,List.getD_eq_getElem?_getD,hi]

lemma block_cert {X Y : Finset ℕ} (B a t v : ℕ) (r : List ℕ) (lead : Bool)
    (ht : t ∈ X) (hv : v ∈ Y) (hr : ∀ u ∈ r, u ∈ Y)
    (xt : t < B) (yt : ∀ u ∈ Y, u < B) (acc : lead = false → a < B) :
    Cert X Y B (blockGates B a t v r lead) := by
  let slots := (Finset.range r.length).image (fun i => B+i)
  let L := Y ∪ slots
  let getR := fun i => r.getD i 0
  let gate := fun i => (⟨GateOp.or,[src B v r.length i, getR i]⟩ : Gate)
  let chain := (List.range r.length).map gate
  let finish : Gate := ⟨.and,[t,src B v r.length r.length]⟩
  let joinGate : Gate := ⟨.or,[a,B+r.length]⟩
  let tail := finish :: (if lead then [] else [joinGate])
  have eq : blockGates B a t v r lead = chain ++ tail := rfl
  have len : chain.length = r.length := by simp [chain]
  have grid (i : ℕ) (hi : i < r.length) : chain[i]? = some (gate i) := by simp [chain,hi]
  have input (i : ℕ) (hi : i ≤ r.length) : src B v r.length i ∈ L ∧ src B v r.length i < B+i := by
    cases i with
    | zero => exact ⟨Finset.mem_union_left _ hv,by simpa [src] using yt _ hv⟩
    | succ i =>
      rw [prev_succ _ _ _ _ (by omega)]
      exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩),by omega⟩
  have member (i : ℕ) (hi : i < r.length) : getR i ∈ Y := by
    apply hr
    simp [getR,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
  have inputs (i : ℕ) (hi : i < r.length) : ∀ u ∈ (gate i).inputs, u ∈ L := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact (input i hi.le).1
    · have he : u = getR i := by simpa using hu
      exact he ▸ Finset.mem_union_left _ (member i hi)
  rw [eq]
  refine ⟨X,L,fun w hw => Or.inl hw,?_,?_⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact Or.inl h
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      have hir := Finset.mem_range.mp hi
      exact Or.inr ⟨gate i,(loc_append ..).mpr (Or.inl ⟨i,grid i hir,rfl⟩),rfl,inputs i hir⟩
  · intro w g loc
    rcases (loc_append ..).mp loc with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
    · have hir : i < r.length := by rw [← len]; exact (List.getElem?_eq_some_iff.mp hi).1
      rw [grid i hir] at hi
      cases hi
      refine ⟨Or.inr rfl,rfl,?_,by simp [gate]⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact (input i hir.le).2
      · have he : u = getR i := by simpa using hu
        have := yt _ (member i hir)
        omega
    · cases i with
      | zero =>
        have he : finish = g := by simpa [tail] using hi
        subst g
        refine ⟨Or.inl rfl,rfl,?_,fun _ => ⟨t,_,rfl,Or.inl ⟨ht,(input _ le_rfl).1⟩⟩⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · omega
        · have he : u = src B v r.length r.length := by simpa using hu
          have := (input r.length le_rfl).2
          omega
      | succ i =>
        cases lead with
        | true => simp [tail] at hi
        | false =>
          cases i with
          | succ i => simp [tail] at hi
          | zero =>
            have he : joinGate = g := by simpa [tail] using hi
            subst g
            refine ⟨Or.inr rfl,rfl,?_,by simp [joinGate]⟩
            intro u hu
            have hh : u = a ∨ u = B+r.length := by simpa [joinGate] using hu
            have := acc rfl
            omega


def Plan (p n : ℕ) (x : ℕ × List ℕ) : Prop :=
  x.2 ≠ [] ∧ ((x.1 < p ∧ ∀ u ∈ x.2, p ≤ u ∧ u < n) ∨
    (p ≤ x.1 ∧ x.1 < n ∧ ∀ u ∈ x.2, u < p))

lemma cover_cert (p n : ℕ) (hp : p ≤ n) (owners : List (ℕ × List ℕ)) :
    ∀ B lead a, n ≤ B → (lead = false → a < B) → (∀ x ∈ owners, Plan p n x) →
      Cert (Finset.range p) (Finset.Ico p n) B (coverGatesB B lead a owners) := by
  induction owners with
  | nil =>
    intro B lead a _ _ _
    exact cert_nil _ _ _
  | cons h os ih =>
    intro B lead a hn ha plans
    obtain ⟨t,vs⟩ := h
    have head := plans (t,vs) (by simp)
    have tail := fun x (hx : x ∈ os) => plans x (List.mem_cons_of_mem _ hx)
    cases vs with
    | nil => exact (head.1 rfl).elim
    | cons v r =>
      change Cert _ _ B (blockGates B a t v r lead ++ _)
      apply cert_append
      · rcases head.2 with ⟨ht,hl⟩ | ⟨ht,ht',hl⟩
        · change t < p at ht
          apply block_cert B a t v r lead (Finset.mem_range.mpr ht)
          · exact Finset.mem_Ico.mpr (hl v (by simp))
          · exact fun w hw => Finset.mem_Ico.mpr (hl w (List.mem_cons_of_mem _ hw))
          · omega
          · exact fun w hw => (Finset.mem_Ico.mp hw).2.trans_le hn
          · exact ha
        · change t < n at ht'
          apply cert_swap
          apply block_cert B a t v r lead (Finset.mem_Ico.mpr ⟨ht,ht'⟩)
          · exact Finset.mem_range.mpr (hl v (by simp))
          · exact fun w hw => Finset.mem_range.mpr (hl w (List.mem_cons_of_mem _ hw))
          · omega
          · exact fun w hw => (Finset.mem_range.mp hw).trans_le (hp.trans hn)
          · exact ha
      · apply ih _ false _ (by omega) _ tail
        intro _
        have hl : 0 < (blockGates B a t v r lead).length := by
          cases lead <;> simp [blockGates]
        omega

lemma closure_at {X P B} (C : Circuit) (hc : Closed X B C.gates P) :
    ∀ w ∈ P, w ∈ X ∨ ∃ i < C.gates.length, w = B+i ∧ (gateAt C i).op = .or ∧
      ∀ v ∈ (gateAt C i).inputs, v ∈ P := by
  intro w hw
  rcases hc w hw with h | ⟨g,⟨i,hi,he⟩,hop,hin⟩
  · exact Or.inl h
  · have hg : gateAt C i = g := by simp [gateAt,List.getD_eq_getElem?_getD,hi]
    exact Or.inr ⟨i,(List.getElem?_eq_some_iff.mp hi).1,he,hg ▸ hop,hg ▸ hin⟩

end PEqualNP.Outside.L_meta_3245


theorem PEqualNP.Outside.L_meta_3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro p q owners n plans C atGate
  have gates : C.gates = PEqualNP.MetaComplexity.coverGatesB n true 0 owners := by
    change (PEqualNP.MetaComplexity.coverCircuitB n owners).gates = _
    unfold PEqualNP.MetaComplexity.coverCircuitB
    split <;> simp_all
  have hc := PEqualNP.Outside.L_meta_3245.cover_cert p n (by dsimp [n]; omega)
    owners n true 0 le_rfl (by simp) plans
  rw [← gates] at hc
  obtain ⟨P,L,hP,hL,good⟩ := hc
  have atIndex (i : ℕ) (hi : i < C.gates.length) :
      PEqualNP.Outside.L_meta_3245.Good P L (n+i) (atGate i) := by
    apply good _ _
    refine ⟨i,?_,rfl⟩
    simp [atGate,PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD_eq_getElem?_getD,hi]
  have member (g : PEqualNP.CircuitLowerBounds.Gate) (hg : g ∈ C.gates) :
      ∃ w, PEqualNP.Outside.L_meta_3245.Good P L w g := by
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hg
    exact ⟨n+i,good _ _ ⟨i,by simpa [hi] using congrArg some he,rfl⟩⟩
  refine ⟨P,L,⟨fun g hg => ?_,fun i hi => ?_,fun g hg => ?_⟩,?_,?_,?_⟩
  · obtain ⟨_,h⟩ := member g hg
    exact h.1
  · exact (atIndex i hi).2.2.1
  · obtain ⟨_,h⟩ := member g hg
    exact h.2.1
  · simpa only [Finset.mem_range] using PEqualNP.Outside.L_meta_3245.closure_at C hP
  · simpa only [Finset.mem_Ico] using PEqualNP.Outside.L_meta_3245.closure_at C hL
  · exact fun i hi => (atIndex i hi).2.2.2


