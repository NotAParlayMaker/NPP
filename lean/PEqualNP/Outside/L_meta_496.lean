import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

lemma PEqualNP.Outside.L_meta_496_vars (φ : CNF) (x : ℕ) :
    x ∈ vars (cvcFormula φ) ↔ x ∈ vars φ ∨ x = fresh φ := by
  simp only [vars, cvcFormula, List.mem_toFinset, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨C, hC, l, hl, rfl⟩
    rcases hC with ⟨D, hD, rfl⟩ | rfl
    · rcases List.mem_append.mp hl with hl | hl
      · exact Or.inl ⟨D, hD, l, hl, rfl⟩
      · simp at hl
        subst hl
        exact Or.inr rfl
    · simp at hl
      subst hl
      exact Or.inr rfl
  · rintro (⟨D, hD, l, hl, rfl⟩ | rfl)
    · exact ⟨D ++ [(fresh φ, true)], Or.inl ⟨D, hD, rfl⟩, l, List.mem_append_left _ hl, rfl⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), by simp, rfl⟩

lemma PEqualNP.Outside.L_meta_496_lt (φ : CNF) (i : ℕ) (h : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD, List.getElem?_append_left, h]

lemma PEqualNP.Outside.L_meta_496_eq (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD]

lemma PEqualNP.Outside.L_meta_496_gt (φ : CNF) (i : ℕ) (h : φ.length < i) :
    clauseAt (cvcFormula φ) i = [] := by
  unfold clauseAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simp [cvcFormula]
    omega

lemma PEqualNP.Outside.L_meta_496_lit (C : Clause) :
    4 * C.length ≤ (C.flatMap encodeLiteral).length := by
  induction C with
  | nil => simp
  | cons l C ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : 4 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
    omega

lemma PEqualNP.Outside.L_meta_496_enc (φ : CNF) :
    2 * (φ.map (fun c : Clause => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons C φ ih =>
    have h1 := PEqualNP.Outside.L_meta_496_lit C
    simp only [encodeCNF, List.flatMap_cons, List.length_append, List.map_cons,
      List.sum_cons, encodeClause] at ih ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at ⊢
    omega

theorem PEqualNP.Outside.L_meta_496 : ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ u v : Fin N, u < v → H.Adj u v → (TH u.val ∨ TH v.val) ∧ ((u.val % 2 = 0 ∧ v.val = u.val + 1 ∧ v.val < 2 * (E + 1) ∧ ¬ TH u.val) ∨ (∃ i < φ.length, ∃ j l : ℕ, j < l ∧ l ≤ (φ.getD i []).length ∧ u.val = 2 * (E + 1) + off i + j ∧ v.val = 2 * (E + 1) + off i + l ∧ (TH u.val ↔ j ≠ f i)) ∨ (u.val < 2 * (E + 1) ∧ 2 * (E + 1) ≤ v.val ∧ (TH u.val ↔ u.val % 2 = 1))) := by
  intro φ E N off e hE hN hoff he hinj num hnl hny hno hnlast H hH f hf TH hTH u v huv hadj
  have offS : ∀ i < φ.length, off (i + 1) = off i + (φ.getD i []).length + 1 := by
    intro i hi
    rw [hoff, hoff, List.map_take, List.map_take, List.take_add_one, List.sum_append,
      List.getElem?_map, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    simp only [Option.map_some, Option.toList_some, List.sum_cons, List.sum_nil,
      Option.getD_some]
    omega
  have offM : ∀ i j, i ≤ j → off i ≤ off j := by
    intro i j h
    rw [hoff, hoff, List.map_take, List.map_take]
    exact List.monotone_sum_take _ h
  have offL : 2 * off φ.length ≤ E := by
    rw [hoff, List.take_length, hE]
    exact PEqualNP.Outside.L_meta_496_enc φ
  have occLt : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length, off i + j < E := by
    intro i hi j hj
    have h1 := offS i hi
    have h2 := offM (i + 1) φ.length (by omega)
    omega
  have occInj : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length, ∀ i' < φ.length,
      ∀ j' ≤ (φ.getD i' []).length, off i + j = off i' + j' → i = i' ∧ j = j' := by
    intro i hi j hj i' hi' j' hj' h
    rcases lt_trichotomy i i' with h3 | h3 | h3
    · have h1 := offS i hi
      have h2 := offM (i + 1) i' h3
      omega
    · subst h3
      omega
    · have h1 := offS i' hi'
      have h2 := offM (i' + 1) i h3
      omega
  have THeven : ∀ k ≤ E, ¬ TH (2 * k) := by
    intro k hk h
    rw [hTH] at h
    rcases h with ⟨z, hz, h⟩ | h | ⟨i, hi, j, hj, -, h⟩ | h <;> omega
  have THy : TH (2 * E + 1) := (hTH _).2 (Or.inr (Or.inl rfl))
  have THlast : TH (3 * E + 2) := (hTH _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have THocc : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length,
      (TH (2 * (E + 1) + off i + j) ↔ j ≠ f i) := by
    intro i hi j hj
    rw [hTH]
    constructor
    · rintro (⟨z, hz, h⟩ | h | ⟨i', hi', j', hj', hne, h⟩ | h)
      · have := he z hz
        omega
      · omega
      · obtain ⟨rfl, rfl⟩ := occInj i hi j hj i' hi' j' hj' (by omega)
        exact hne
      · have := occLt i hi j hj
        omega
    · intro hne
      exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hne, rfl⟩))
  have litI : ∀ x, x ∈ vars φ ∨ x = fresh φ → ∃ k, k ≤ E ∧ TH (2 * k + 1) ∧
      ∀ b : Bool, num (Sum.inl (x, b)) = 2 * k + (if b then 1 else 0) := by
    rintro x (hx | rfl)
    · exact ⟨e x, (he x hx).le, (hTH _).2 (Or.inl ⟨x, hx, rfl⟩), hnl x hx⟩
    · exact ⟨E, le_rfl, THy, hny⟩
  have occLit : ∀ i < φ.length, ∀ j a,
      (φ.getD i [] ++ [(fresh φ, true)])[j]? = some a →
      (a.1 ∈ vars φ ∨ a.1 = fresh φ) ∧ (a.2 = false → j ≠ f i) := by
    intro i hi j a ha
    constructor
    · have hm := List.mem_of_getElem? ha
      rcases List.mem_append.mp hm with hm | hm
      · left
        simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
        refine ⟨φ.getD i [], ?_, a, hm, rfl⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact List.getElem_mem hi
      · simp at hm
        subst hm
        exact Or.inr rfl
    · intro hneg heq
      have hw : (φ.getD i [] ++ [(fresh φ, true)]).findIdx (fun l => l.2) <
          (φ.getD i [] ++ [(fresh φ, true)]).length :=
        List.findIdx_lt_length_of_exists ⟨(fresh φ, true), by simp, rfl⟩
      have h1 := List.findIdx_getElem (w := hw)
      rw [hf] at heq
      rw [heq, List.getElem?_eq_getElem hw] at ha
      simp only [Option.some.injEq] at ha
      rw [ha] at h1
      simp [hneg] at h1
  have occInfo : ∀ i j a, (clauseAt (cvcFormula φ) i)[j]? = some a →
      (a.1 ∈ vars φ ∨ a.1 = fresh φ) ∧ 2 * (E + 1) ≤ num (Sum.inr (i, j)) := by
    intro i j a ha
    obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.1 ha
    rcases lt_trichotomy i φ.length with hi | rfl | hi
    · rw [PEqualNP.Outside.L_meta_496_lt φ i hi] at ha hjl
      simp only [List.length_append, List.length_cons, List.length_nil] at hjl
      refine ⟨(occLit i hi j a ha).1, ?_⟩
      rw [hno i j hi (by omega)]
      omega
    · rw [PEqualNP.Outside.L_meta_496_eq φ] at ha hjl
      simp only [List.length_cons, List.length_nil] at hjl
      have hj0 : j = 0 := by omega
      subst hj0
      obtain rfl : (fresh φ, false) = a := by simpa using ha
      refine ⟨Or.inr rfl, ?_⟩
      rw [hnlast]
      omega
    · rw [PEqualNP.Outside.L_meta_496_gt φ i hi] at hjl
      simp at hjl
  obtain ⟨u', v', hadj', hu, hv⟩ := (hH u v).1 hadj
  have hlt : u.val < v.val := huv
  change satAdj (cvcFormula φ) u' v' at hadj'
  rcases u' with ⟨x, a⟩ | ⟨i, j⟩ <;> rcases v' with ⟨x', b⟩ | ⟨i', j'⟩ <;>
    simp only [satAdj] at hadj'
  · obtain ⟨hxx, hab, hx⟩ := hadj'
    subst hxx
    obtain ⟨k, hk, hTk, hnk⟩ := litI x ((PEqualNP.Outside.L_meta_496_vars φ x).1 hx)
    rw [hnk] at hu hv
    rw [← hu, ← hv]
    rw [← hu, ← hv] at hlt
    cases a <;> cases b <;> simp at hab hlt ⊢
    exact ⟨Or.inr hTk, Or.inl ⟨by omega, THeven k hk⟩⟩
  · obtain ⟨hvar, hge⟩ := occInfo i' j' (x, a) hadj'
    obtain ⟨k, hk, hTk, hnk⟩ := litI x hvar
    rw [hnk] at hu
    rw [← hu, ← hv]
    rw [← hu, ← hv] at hlt
    have hlo : 2 * k + (if a then 1 else 0) < 2 * (E + 1) := by
      cases a <;> simp <;> omega
    refine ⟨?_, Or.inr (Or.inr ⟨hlo, hge, ?_⟩)⟩
    · cases a
      · right
        obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.1 hadj'
        rcases lt_trichotomy i' φ.length with hi | rfl | hi
        · rw [PEqualNP.Outside.L_meta_496_lt φ i' hi] at hadj' hjl
          simp only [List.length_append, List.length_cons, List.length_nil] at hjl
          have hneg := (occLit i' hi j' (x, false) hadj').2 rfl
          rw [hno i' j' hi (by omega)]
          exact (THocc i' hi j' (by omega)).2 hneg
        · rw [PEqualNP.Outside.L_meta_496_eq φ] at hjl
          simp only [List.length_cons, List.length_nil] at hjl
          have hj0 : j' = 0 := by omega
          subst hj0
          rw [hnlast]
          exact THlast
        · rw [PEqualNP.Outside.L_meta_496_gt φ i' hi] at hjl
          simp at hjl
      · left
        simpa using hTk
    · cases a
      · simp only [Bool.false_eq_true, ite_false, add_zero]
        constructor
        · intro h
          exact absurd h (THeven k hk)
        · intro h
          omega
      · simp only [ite_true]
        constructor
        · intro _
          omega
        · intro _
          exact hTk
  · obtain ⟨hvar, hge⟩ := occInfo i j (x', b) hadj'
    obtain ⟨k, hk, -, hnk⟩ := litI x' hvar
    rw [hnk] at hv
    have : 2 * k + (if b then 1 else 0) < 2 * (E + 1) := by
      cases b <;> simp <;> omega
    omega
  · obtain ⟨hii, hjj, hj, hl⟩ := hadj'
    subst hii
    rcases lt_trichotomy i φ.length with hi | rfl | hi
    · rw [PEqualNP.Outside.L_meta_496_lt φ i hi] at hj hl
      simp only [List.length_append, List.length_cons, List.length_nil] at hj hl
      rw [hno i j hi (by omega)] at hu
      rw [hno i j' hi (by omega)] at hv
      rw [← hu, ← hv]
      rw [← hu, ← hv] at hlt
      refine ⟨?_, Or.inr (Or.inl ⟨i, hi, j, j', by omega, by omega, rfl, rfl,
        THocc i hi j (by omega)⟩)⟩
      by_cases h : j = f i
      · right
        exact (THocc i hi j' (by omega)).2 (by omega)
      · left
        exact (THocc i hi j (by omega)).2 h
    · rw [PEqualNP.Outside.L_meta_496_eq φ] at hj hl
      simp only [List.length_cons, List.length_nil] at hj hl
      omega
    · rw [PEqualNP.Outside.L_meta_496_gt φ i hi] at hj
      simp at hj
