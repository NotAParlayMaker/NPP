import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.DeMorganFormula

namespace PEqualNP.Outside

open PEqualNP.MetaComplexity

private def pathPair {N : ℕ} (t : ℕ) (x : Fin N → Bool) : Prop :=
  ∃ i j : Fin N, j.val < t ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true

private lemma pathUpper (N t : ℕ) (ht : 2 ≤ t) (hN : t ≤ N) :
    ∃ f : DMFormula N, f.leaves + 1 = t + t / 2 ∧
      ∀ x, f.eval x = true ↔ pathPair t x := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    by_cases hsmall : t ≤ 3
    · let a : Fin N := ⟨0, by omega⟩
      let b : Fin N := ⟨1, by omega⟩
      by_cases ht2 : t = 2
      · subst t
        refine ⟨.and (.lit a true) (.lit b true), rfl, ?_⟩
        intro x
        simp only [DMFormula.eval, Bool.and_eq_true, ite_true]
        constructor
        · exact fun ⟨ha,hb⟩ => ⟨a,b,by dsimp [b]; omega,rfl,ha,hb⟩
        · rintro ⟨i,j,hj,he,hi,hx⟩
          have : i = a := Fin.ext (by dsimp [a]; omega)
          have : j = b := Fin.ext (by dsimp [b]; omega)
          grind
      · have h3 : t = 3 := by omega
        subst t
        let c : Fin N := ⟨2, by omega⟩
        refine ⟨.and (.lit b true) (.or (.lit a true) (.lit c true)), rfl, ?_⟩
        intro x
        simp only [DMFormula.eval, Bool.and_eq_true, Bool.or_eq_true, ite_true]
        constructor
        · rintro ⟨hb,ha|hc⟩
          · exact ⟨a,b,by dsimp [b]; omega,rfl,ha,hb⟩
          · exact ⟨b,c,by dsimp [c]; omega,rfl,hb,hc⟩
        · rintro ⟨i,j,hj,he,hi,hx⟩
          by_cases h : i.val = 0
          · have : i = a := Fin.ext h
            have : j = b := Fin.ext (by dsimp [b]; omega)
            grind
          · have : i = b := Fin.ext (by dsimp [b]; omega)
            have : j = c := Fin.ext (by dsimp [c]; omega)
            grind
    · obtain ⟨f,hsize,hf⟩ := ih (t-2) (by omega) (by omega) (by omega)
      let a : Fin N := ⟨t-3, by omega⟩
      let b : Fin N := ⟨t-2, by omega⟩
      let c : Fin N := ⟨t-1, by omega⟩
      refine ⟨.or f (.and (.lit b true) (.or (.lit a true) (.lit c true))), ?_, ?_⟩
      · simp only [DMFormula.leaves]
        omega
      intro x
      simp only [DMFormula.eval, Bool.or_eq_true, Bool.and_eq_true, ite_true, hf]
      constructor
      · rintro (⟨i,j,hj,he,hi,hx⟩ | ⟨hb,ha|hc⟩)
        · exact ⟨i,j,by omega,he,hi,hx⟩
        · exact ⟨a,b,by dsimp [b]; omega,by dsimp [a,b]; omega,ha,hb⟩
        · exact ⟨b,c,by dsimp [c]; omega,by dsimp [b,c]; omega,hb,hc⟩
      · rintro ⟨i,j,hj,he,hi,hx⟩
        by_cases h : j.val < t-2
        · exact Or.inl ⟨i,j,h,he,hi,hx⟩
        by_cases h2 : j.val = t-2
        · have : j = b := Fin.ext h2
          have : i = a := Fin.ext (by dsimp [a]; omega)
          grind
        · have : j = c := Fin.ext (by dsimp [c]; omega)
          have : i = b := Fin.ext (by dsimp [b]; omega)
          grind

private def occ {N : ℕ} (i : Fin N) : DMFormula N → ℕ
  | .lit j _ => if i = j then 1 else 0
  | .and f g | .or f g => occ i f + occ i g

private lemma evalAgree {N : ℕ} (f : DMFormula N) (x y : Fin N → Bool)
    (h : ∀ i, 0 < occ i f → x i = y i) : f.eval x = f.eval y := by
  induction f with
  | lit i b => simp [DMFormula.eval,h i (by simp [occ])]
  | and f g hf hg =>
    have hl := hf (fun i hi => h i (by simp only [occ]; omega))
    have hr := hg (fun i hi => h i (by simp only [occ]; omega))
    simp [DMFormula.eval,hl,hr]
  | or f g hf hg =>
    have hl := hf (fun i hi => h i (by simp only [occ]; omega))
    have hr := hg (fun i hi => h i (by simp only [occ]; omega))
    simp [DMFormula.eval,hl,hr]

private def input {N : ℕ} (i j : Fin N) (x : Fin N → Bool) (a b : Bool) (v : Fin N) :=
  if v = i then a else if v = j then b else x v

private abbrev Table := Prop × Prop × Prop × Prop

private def tab {N : ℕ} (i j : Fin N) (x : Fin N → Bool) (f : DMFormula N) : Table :=
  ⟨f.eval (input i j x false false) = true, f.eval (input i j x false true) = true,
   f.eval (input i j x true false) = true, f.eval (input i j x true true) = true⟩
private def noI (t : Table) := (t.1 ↔ t.2.2.1) ∧ (t.2.1 ↔ t.2.2.2)
private def noJ (t : Table) := (t.1 ↔ t.2.1) ∧ (t.2.2.1 ↔ t.2.2.2)
private def both (t : Table) := ¬ t.1 ∧ ¬ t.2.1 ∧ ¬ t.2.2.1 ∧ t.2.2.2
private def eitherB (t : Table) := ¬ t.1 ∧ t.2.1 ∧ t.2.2.1 ∧ t.2.2.2
private def joinT (op : Prop → Prop → Prop) (t u : Table) : Table :=
  ⟨op t.1 u.1, op t.2.1 u.2.1, op t.2.2.1 u.2.2.1, op t.2.2.2 u.2.2.2⟩

private lemma absentI {N} (i j : Fin N) (x) (f : DMFormula N) (h : occ i f = 0) :
    noI (tab i j x f) := by
  have e (b : Bool) : f.eval (input i j x false b) = f.eval (input i j x true b) :=
    evalAgree _ _ _ (fun v hv => by
      have hvi : v ≠ i := by rintro rfl; omega
      simp [input,hvi])
  simp [noI,tab,e]
private lemma absentJ {N} (i j : Fin N) (x) (f : DMFormula N) (h : occ j f = 0) :
    noJ (tab i j x f) := by
  have e (a : Bool) : f.eval (input i j x a false) = f.eval (input i j x a true) :=
    evalAgree _ _ _ (fun v hv => by
      have hvj : v ≠ j := by rintro rfl; omega
      simp [input,hvj])
  simp [noJ,tab,e]

private lemma join_obstruction (op : Prop → Prop → Prop) (hop : op = And ∨ op = Or)
    (l r l' r' : Table)
    (hI : (noI l ∧ noI l') ∨ (noI r ∧ noI r'))
    (hJ : (noJ l ∧ noJ l') ∨ (noJ r ∧ noJ r'))
    (hl : ¬ (both l ∧ eitherB l')) (hr : ¬ (both r ∧ eitherB r')) :
    ¬ (both (joinT op l r) ∧ eitherB (joinT op l' r')) := by
  rcases hop with rfl|rfl <;> unfold noI noJ both eitherB joinT at * <;> dsimp at * <;> grind only

private lemma tabAnd {N} (i j : Fin N) (x) (f g : DMFormula N) :
    tab i j x (.and f g) = joinT And (tab i j x f) (tab i j x g) := by
  simp [tab,joinT,DMFormula.eval,Bool.and_eq_true]
private lemma tabOr {N} (i j : Fin N) (x) (f g : DMFormula N) :
    tab i j x (.or f g) = joinT Or (tab i j x f) (tab i j x g) := by
  simp [tab,joinT,DMFormula.eval,Bool.or_eq_true]

private lemma distinctGate {N} (i j : Fin N) (hne : i ≠ j) (x y : Fin N → Bool)
    (f : DMFormula N) (hi : occ i f ≤ 1) (hj : occ j f ≤ 1) :
    ¬ (both (tab i j x f) ∧ eitherB (tab i j y f)) := by
  induction f with
  | lit v b =>
    by_cases h : i = v
    · have hz : occ j (.lit v b) = 0 := by simp [occ, ← h, Ne.symm hne]
      have e := absentJ i j x (.lit v b) hz
      unfold noJ at e
      unfold both
      grind only
    · have e := absentI i j x (.lit v b) (by simp [occ,h])
      unfold noI at e
      unfold both
      grind only
  | and f g hf hg | or f g hf hg =>
    simp only [occ] at hi hj
    have hI : (noI (tab i j x f) ∧ noI (tab i j y f)) ∨
        (noI (tab i j x g) ∧ noI (tab i j y g)) := by
      by_cases h : occ i f = 0
      · exact Or.inl ⟨absentI _ _ _ _ h, absentI _ _ _ _ h⟩
      · exact Or.inr ⟨absentI _ _ _ _ (by omega), absentI _ _ _ _ (by omega)⟩
    have hJ : (noJ (tab i j x f) ∧ noJ (tab i j y f)) ∨
        (noJ (tab i j x g) ∧ noJ (tab i j y g)) := by
      by_cases h : occ j f = 0
      · exact Or.inl ⟨absentJ _ _ _ _ h, absentJ _ _ _ _ h⟩
      · exact Or.inr ⟨absentJ _ _ _ _ (by omega), absentJ _ _ _ _ (by omega)⟩
    simp only [tabAnd,tabOr]
    exact join_obstruction _ (by first | exact Or.inl rfl | exact Or.inr rfl) _ _ _ _ hI hJ
      (hf (by omega) (by omega)) (hg (by omega) (by omega))

private def AdjTrue {N} (x : Fin N → Bool) : Prop :=
  ∃ i j : Fin N, i.val + 1 = j.val ∧ x i = true ∧ x j = true

private lemma switchPair {N} (i j : Fin N) (e : i.val + 1 = j.val)
    (hi : 0 < i.val) (hj : j.val + 1 < N) (a b : Bool) (outside : Bool) :
    AdjTrue (input i j (fun v => outside && decide (v.val + 1 = i.val ∨ v.val = j.val + 1)) a b) ↔
      (a = true ∧ b = true) ∨ (outside = true ∧ (a = true ∨ b = true)) := by
  have hs (v : Fin N) : input i j (fun v => outside && decide (v.val + 1 = i.val ∨ v.val = j.val + 1)) a b v = true ↔
      (v.val = i.val ∧ a = true) ∨ (v.val = j.val ∧ b = true) ∨
      (outside = true ∧ (v.val + 1 = i.val ∨ v.val = j.val + 1)) := by
    unfold input
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  constructor
  · rintro ⟨u,v,hu,h1,h2⟩
    rw [hs] at h1 h2
    grind only
  · rintro (⟨ha,hb⟩|⟨hout,ha|hb⟩)
    · exact ⟨i,j,e,(hs i).2 (Or.inl ⟨rfl,ha⟩),(hs j).2 (Or.inr (Or.inl ⟨rfl,hb⟩))⟩
    · let u : Fin N := ⟨i.val-1,by omega⟩
      exact ⟨u,i,by dsimp [u]; omega,(hs u).2 (Or.inr (Or.inr ⟨hout,Or.inl (by dsimp [u]; omega)⟩)),
        (hs i).2 (Or.inl ⟨rfl,ha⟩)⟩
    · let v : Fin N := ⟨j.val+1,hj⟩
      exact ⟨j,v,rfl,(hs j).2 (Or.inr (Or.inl ⟨rfl,hb⟩)),
        (hs v).2 (Or.inr (Or.inr ⟨hout,Or.inr rfl⟩))⟩

private lemma pairCost {N} (f : DMFormula N) (hf : ∀ x, f.eval x = true ↔ AdjTrue x)
    (i j : Fin N) (e : i.val + 1 = j.val) (hi : 0 < i.val) (hj : j.val + 1 < N) :
    2 ≤ occ i f ∨ 2 ≤ occ j f := by
  by_contra! h
  let z (o : Bool) := fun v : Fin N => o && decide (v.val + 1 = i.val ∨ v.val = j.val + 1)
  have ht := distinctGate i j (by intro he; subst j; omega) (z false) (z true) f (by omega) (by omega)
  apply ht
  simp only [both,eitherB,tab,hf,z,switchPair i j e hi hj]
  decide

private lemma essential {N} (hN : 2 ≤ N) (f : DMFormula N) (hf : ∀ x, f.eval x = true ↔ AdjTrue x)
    (i : Fin N) : 0 < occ i f := by
  let j : Fin N := if h : i.val = 0 then ⟨1,by omega⟩ else ⟨i.val-1,by omega⟩
  have hj : i.val+1 = j.val ∨ j.val+1 = i.val := by
    dsimp [j]; split <;> dsimp only <;> omega
  let x (v : Fin N) := decide (v = i ∨ v = j)
  let y (v : Fin N) := decide (v = j)
  have hx : AdjTrue x := by
    rcases hj with h|h
    · exact ⟨i,j,h,by simp [x],by simp [x]⟩
    · exact ⟨j,i,h,by simp [x],by simp [x]⟩
  have hy : ¬ AdjTrue y := by
    rintro ⟨v,w,he,hv,hw⟩
    simp [y] at hv hw
    subst v; subst w; omega
  by_contra! h
  have he := evalAgree f x y (fun v hv => by
    have hvi : v ≠ i := by rintro rfl; omega
    simp [x,y,hvi])
  exact hy ((hf y).1 (he ▸ (hf x).2 hx))

private lemma sum_occ {N} (f : DMFormula N) : (∑ i : Fin N, occ i f) = f.leaves := by
  induction f with
  | lit i b => simp [occ,DMFormula.leaves]
  | and f g hf hg | or f g hf hg => simp [occ,DMFormula.leaves,Finset.sum_add_distrib,hf,hg]

private lemma lower {N} (hN : 2 ≤ N) (f : DMFormula N) (hf : ∀ x, f.eval x = true ↔ AdjTrue x) :
    N + N / 2 ≤ f.leaves + 1 := by
  let w (i : ℕ) := if h : i < N then occ ⟨i,h⟩ f else 0
  have pos (i : ℕ) (h : i < N) : 1 ≤ w i := by
    have hp := essential hN f hf ⟨i,h⟩
    simp [w,h]
    omega
  have sumBound (s : ℕ) (hs : 2*s+1 < N) :
      3*s+1 ≤ ∑ i ∈ Finset.range (2*s+1), w i := by
    induction s with
    | zero => simpa using pos 0 (by omega)
    | succ s ih =>
      have h1 : 2*s+1 < N := by omega
      have h2 : 2*s+2 < N := by omega
      have hplus : 2 ≤ w (2*s+1) ∨ 2 ≤ w (2*s+2) := by
        simpa [w,h1,h2] using pairCost f hf ⟨2*s+1,h1⟩ ⟨2*s+2,h2⟩ rfl (by dsimp; omega) (by dsimp; omega)
      have ha := pos _ h1
      have hb := pos _ h2
      have hc := ih h1
      rw [show 2*(s+1)+1 = (2*s+1)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ]
      omega
  have total : (∑ i ∈ Finset.range N, w i) = f.leaves := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [w] using sum_occ f
  let s := N / 2 - 1
  have hp := sumBound s (by dsimp [s]; omega)
  have hlast : 2*s+1 < N := by dsimp [s]; omega
  have ha := pos _ hlast
  have hcases : N = 2*s+1+1 ∨ N = 2*s+1+1+1 := by dsimp [s]; omega
  rcases hcases with h|h
  · have hh := congrArg (fun q => ∑ i ∈ Finset.range q, w i) h
    simp only [Finset.sum_range_succ] at hh hp
    omega

  · have hb := pos (2*s+2) (by omega)
    have hh := congrArg (fun q => ∑ i ∈ Finset.range q, w i) h
    simp only [Finset.sum_range_succ] at hh hp
    omega


theorem L_meta_121 :
    ∀ n s : ℕ, 2 ≤ n → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) s ↔ n + n / 2 ≤ s + 1) := by
  intro n s hn
  constructor
  · rintro ⟨f,hsize,hf⟩
    have hl := lower hn f (fun x => by rw [hf]; simp [AdjTrue])
    omega
  · intro h
    obtain ⟨f,hsize,hf⟩ := pathUpper n n hn (by omega)
    refine ⟨f,by omega,?_⟩
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa [pathPair] using hf x

end PEqualNP.Outside