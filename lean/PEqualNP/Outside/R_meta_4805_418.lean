import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

theorem PEqualNP.Outside.R_meta_4805_418
    (encode : ∀ (n s : Nat) (C : Circuit), 0 < s → Monotone2 C → C.size ≤ s →
      FormulaSat (enc n s (fun r => C.eval (List.ofFn (fun i : Fin n => r.testBit i.val))) (List.range (2^n))))
    (order : ∀ (n s : Nat) (f : Nat → Bool), 0 < s →
      FormulaSat (enc n s f (List.range (2^n))) → FormulaSat (enc2 n s f (List.range (2^n)))) :
    ∀ (x1 x2 : ℕ) (x3 : ℕ → Bool) (x4 : List ℕ) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x2 → (∀ x7 ∈ x4, x7 < (2 : ℕ) ^ x1) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ x2 → (∀ x10 ∈ x4, x5.eval (List.ofFn fun (x12 : Fin x1) => x10.testBit ↑x12) = x3 x10) → ∃ x11 < PEqualNP.Defs.LratEncoding.enc2CubeCount x1 x2, PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc2 x1 x2 x3 x4 ++ PEqualNP.Defs.LratEncoding.enc2Cube x1 x2 x11) := by
  have cover (n s : Nat) (g : Nat → Bool) (rows : List Nat) (hs : 0 < s)
      (sat : FormulaSat (enc2 n s g rows)) :
      ∃ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k) := by
    obtain ⟨a, ok⟩ := sat
    let j := s-1
    have hj : j<s := by dsimp [j]; omega
    have width : n+j+1=n+s := by dsimp [j];omega
    have srcClause : (List.range (n+j+1)).map (fun k => P (ix n s 1 j k)) ∈ fSrcAlo n s := by
      apply List.mem_flatMap.mpr
      exact ⟨1,by simp,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩⟩
    have opClause : [P (ix n s 0 j 0),P (ix n s 0 j 1),P (ix n s 0 j 2)] ∈ fOp n s :=
      List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
    have srcOK : ClauseSat a ((List.range (n+j+1)).map (fun k => P (ix n s 1 j k))) :=
      ok _ (by delta enc2 enc;simp only [List.mem_append];tauto)
    have opOK : ClauseSat a [P (ix n s 0 j 0),P (ix n s 0 j 1),P (ix n s 0 j 2)] :=
      ok _ (by delta enc2 enc;simp only [List.mem_append];tauto)
    obtain ⟨v,hv,hlit⟩ := srcOK
    obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hv
    have lt : src<n+s := width ▸ List.mem_range.mp hsrc
    obtain ⟨u,hu,hop⟩ := opOK
    have ex : ∃ o<3, litVal a (P (ix n s 0 j o))=true := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl|rfl|rfl
      · exact ⟨0,by decide,hop⟩
      · exact ⟨1,by decide,hop⟩
      · exact ⟨2,by decide,hop⟩
    obtain ⟨o,ho,oplit⟩ := ex
    let k := src+(n+s)*o
    have q : k/(n+s)=o := by
      dsimp [k];rw [Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt lt,Nat.zero_add]
    have r : k % (n + s) = src := by simp [k,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lt]
    refine ⟨k,?_,a,?_⟩
    · change src+(n+s)*o<3*(n+s)
      interval_cases o <;> omega
    · intro c hc
      rcases List.mem_append.mp hc with old|cube
      · exact ok c old
      · delta enc2Cube at cube
        simp only [r,q,List.mem_cons,List.not_mem_nil,or_false] at cube
        rcases cube with rfl|rfl
        · exact ⟨_,List.mem_cons_self,hlit⟩
        · exact ⟨_,List.mem_cons_self,oplit⟩

  have restrict_rows (n s : Nat) (f g : Nat → Bool) (small big : List Nat)
      (inc : ∀ r ∈ small, r ∈ big) (agree : ∀ r ∈ small, f r = g r) :
      ∀ c ∈ enc2 n s g small, c ∈ enc2 n s f big := by
    have source : ∀ c ∈ fSrcEq n s small, c ∈ fSrcEq n s big := by
      intro c h
      delta fSrcEq at h ⊢
      simp only [List.mem_flatMap] at h ⊢
      obtain ⟨e,he,j,hj,r,hr,k,hk,h⟩ := h
      exact ⟨e,he,j,hj,r,inc r hr,k,hk,h⟩
    have gates : ∀ c ∈ fGate n s small, c ∈ fGate n s big := by
      intro c h
      delta fGate at h ⊢
      simp only [List.mem_flatMap] at h ⊢
      obtain ⟨j,hj,r,hr,h⟩ := h
      exact ⟨j,hj,r,inc r hr,h⟩
    have output : ∀ c ∈ fOutEq n s g small, c ∈ fOutEq n s f big := by
      intro c h
      delta fOutEq at h ⊢
      simp only [List.mem_flatMap] at h ⊢
      obtain ⟨r,hr,k,hk,h⟩ := h
      refine ⟨r,inc r hr,k,hk,?_⟩
      delta outEq at h ⊢
      rw [agree r hr]
      exact h
    intro c h
    delta enc2 enc at h ⊢
    simp only [List.mem_append,or_assoc] at h ⊢
    exact Or.imp id (Or.imp id (Or.imp (source c) (Or.imp (gates c)
      (Or.imp id (Or.imp (output c) id))))) h
  intro n s g rows C hs range mono size fits
  apply cover n s g rows hs
  obtain ⟨a,ok⟩ := order n s _ hs (encode n s C hs mono size)
  exact ⟨a,fun c hc => ok c (restrict_rows n s _ g rows _
    (fun r hr => List.mem_range.mpr (range r hr)) fits c hc)⟩
