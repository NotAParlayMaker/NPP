import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

private def onGraph (φ : CNF) : Vertex → Prop
  | .inl (x, _) => x ∈ vars φ ∨ x = fresh φ
  | .inr (i, j) => (i < φ.length ∧ j ≤ (φ.getD i []).length) ∨ (i = φ.length ∧ j = 0)

private lemma onGraph_of_adj {φ : CNF} {u v : Vertex} (h : (cvcGraph φ).Adj u v) :
    onGraph φ u := by
  have literal (x : ℕ) (hx : x ∈ vars (cvcFormula φ)) : x ∈ vars φ ∨ x = fresh φ := by
    simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map] at hx ⊢
    obtain ⟨C, hC, a, ha, rfl⟩ := hx
    rcases List.mem_append.mp hC with old | last
    · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp old
      rcases List.mem_append.mp ha with hd | hy
      · exact Or.inl ⟨D, hD, a, hd, rfl⟩
      · simp only [List.mem_singleton] at hy
        exact Or.inr (by rw [hy])
    · simp only [List.mem_singleton] at last
      subst C
      simp only [List.mem_singleton] at ha
      exact Or.inr (by rw [ha])
  have idx (i j : ℕ) (hj : j < (clauseAt (cvcFormula φ) i).length) :
      i < (cvcFormula φ).length := by
    by_contra! bad
    rw [clauseAt, List.getD_eq_default _ [] bad] at hj
    simp at hj
  have occ (i j : ℕ) (hj : j < (clauseAt (cvcFormula φ) i).length) :
      onGraph φ (.inr (i, j)) := by
    by_cases hi : i < φ.length
    · left
      refine ⟨hi, ?_⟩
      simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD, List.getElem?_append, hi] at hj
      rw [List.getD_eq_getElem _ [] hi]
      omega
    · have hlen := idx i j hj
      simp [cvcFormula] at hlen
      have eq : i = φ.length := by omega
      subst i
      right
      simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD] at hj
      exact ⟨rfl, by omega⟩
  change satAdj (cvcFormula φ) u v at h
  rcases u with ⟨x, b⟩ | ⟨i, j⟩ <;> rcases v with ⟨y, d⟩ | ⟨n, m⟩
  · exact literal _ h.2.2
  · obtain ⟨hm, he⟩ := List.getElem?_eq_some_iff.mp h
    have hn := idx n m hm
    have hc : clauseAt (cvcFormula φ) n ∈ cvcFormula φ := by
      rw [clauseAt, List.getD_eq_getElem _ [] hn]
      exact List.getElem_mem hn
    apply literal
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨_, hc,
      List.mem_map.mpr ⟨_, List.getElem_mem hm, congrArg Prod.fst he⟩⟩)
  · exact occ _ _ (List.getElem?_eq_some_iff.mp h).choose
  · exact occ _ _ h.2.2.1

private lemma roomForOffsets (φ : CNF) :
    (φ.map (fun C => C.length + 1)).sum ≤ (encodeCNF φ).length := by
  have room (C : Clause) : C.length ≤ (C.flatMap encodeLiteral).length := by
    induction C with
    | nil => simp
    | cons a C ih =>
      have ha : 1 ≤ (encodeLiteral a).length := by simp [encodeLiteral]
      simp only [List.flatMap_cons, List.length_cons, List.length_append]
      omega
  induction φ with
  | nil => simp [encodeCNF]
  | cons C φ ih =>
    change _ ≤ ((C :: φ).flatMap encodeClause).length
    change _ ≤ (φ.flatMap encodeClause).length at ih
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    have hc : (encodeClause C).length = (C.flatMap encodeLiteral).length + 2 := by simp [encodeClause]
    have := room C
    omega

private lemma bitCodeInj (i j : ℕ) (a b : Bool)
    (h : 2 * i + (if a then 1 else 0) = 2 * j + (if b then 1 else 0)) :
    i = j ∧ a = b := by
  cases a <;> cases b <;> simp_all <;> omega

theorem PEqualNP.Outside.L_meta_479 : ∀ (φ : PEqualNP.Search.CNF) (E : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ u v w z : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v → (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj w z → num u = num w → u = w := by
  intro φ E off e size offsets bounded einj num lit freshlit occurrence last
  have nextOff (i : ℕ) (hi : i < φ.length) :
      off (i + 1) = off i + (φ.getD i []).length + 1 := by
    rw [offsets (i+1), offsets i, List.take_succ_eq_append_getElem hi, List.getD_eq_getElem _ [] hi]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, Nat.add_zero, Nat.add_assoc]
  have mono : Monotone off := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < φ.length
    · rw [nextOff i hi]
      omega
    · rw [offsets i, offsets (i+1), List.take_of_length_le (by omega : φ.length ≤ i),
        List.take_of_length_le (by omega : φ.length ≤ i+1)]
  have total : off φ.length ≤ E := by simpa [offsets, size] using roomForOffsets φ
  have before (i j n : ℕ) (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) (hin : i < n) :
      off i + j < off n := by
    have h := mono (show i + 1 ≤ n by omega)
    have := nextOff i hi
    omega
  have litSmall (x : ℕ) (b : Bool) (hx : onGraph φ (.inl (x,b))) :
      num (.inl (x,b)) < 2 * (E+1) := by
    rcases hx with hx | rfl
    · rw [lit x hx b]
      have := bounded x hx
      cases b <;> simp <;> omega
    · rw [freshlit b]
      cases b <;> simp <;> omega
  have occBig (i j : ℕ) (h : onGraph φ (.inr (i,j))) :
      2 * (E+1) ≤ num (.inr (i,j)) := by
    rcases h with ⟨hi,hj⟩ | ⟨rfl,rfl⟩
    · rw [occurrence i j hi hj]
      omega
    · rw [last]
      omega
  intro u v w z huv hwz eq
  have hu := onGraph_of_adj huv
  have hw := onGraph_of_adj hwz
  rcases u with ⟨x,b⟩ | ⟨i,j⟩ <;> rcases w with ⟨y,d⟩ | ⟨n,m⟩
  · rcases hu with hx | rfl <;> rcases hw with hy | rfl
    · rw [lit x hx b, lit y hy d] at eq
      obtain ⟨he, rfl⟩ := bitCodeInj _ _ _ _ eq
      rw [einj x hx y hy he]
    · rw [lit x hx b, freshlit d] at eq
      have := (bitCodeInj _ _ _ _ eq).1
      have := bounded x hx
      omega
    · rw [freshlit b, lit y hy d] at eq
      have := (bitCodeInj _ _ _ _ eq).1
      have := bounded y hy
      omega
    · rw [freshlit b, freshlit d] at eq
      rw [(bitCodeInj _ _ _ _ eq).2]
  · have := litSmall x b hu
    have := occBig n m hw
    omega
  · have := occBig i j hu
    have := litSmall y d hw
    omega
  · rcases hu with ⟨hi,hj⟩ | ⟨rfl,rfl⟩ <;> rcases hw with ⟨hn,hm⟩ | ⟨rfl,rfl⟩
    · rw [occurrence i j hi hj, occurrence n m hn hm] at eq
      rcases lt_trichotomy i n with il | rfl | ni
      · have := before i j n hi hj il
        omega
      · have e : j = m := by omega
        rw [e]
      · have := before n m i hn hm ni
        omega
    · rw [occurrence i j hi hj, last] at eq
      have := before i j φ.length hi hj hi
      omega
    · rw [last, occurrence n m hn hm] at eq
      have := before n m φ.length hn hm hn
      omega
    · rfl
