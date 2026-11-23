import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

private lemma encodeLiteral_length (l : Literal) : 4 ≤ (encodeLiteral l).length := by
  simp [encodeLiteral]

private lemma encodeClause_length (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [encodeClause]
  | cons l cs ih =>
    simp only [encodeClause, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have hl := encodeLiteral_length l
    omega

private lemma sum_clause_le_encodeCNF (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c φ' ih =>
    simp only [encodeCNF, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    have hc := encodeClause_length c
    omega

private lemma off_succ (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    ((φ.take (i + 1)).map (fun c => c.length + 1)).sum =
      ((φ.take i).map (fun c => c.length + 1)).sum + (φ.getD i []).length + 1 := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.getD_eq_getElem _ _ hi]
  simp [add_assoc]

private lemma off_mono (φ : CNF) {i j : ℕ} (h : i ≤ j) :
    ((φ.take i).map (fun c => c.length + 1)).sum ≤
      ((φ.take j).map (fun c => c.length + 1)).sum := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp h
    subst this; rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · have hij : i ≤ j := Nat.lt_succ_iff.mp hlt
      calc ((φ.take i).map (fun c => c.length + 1)).sum
          ≤ ((φ.take j).map (fun c => c.length + 1)).sum := ih hij
        _ ≤ ((φ.take (j + 1)).map (fun c => c.length + 1)).sum := by
            by_cases hj : j < φ.length
            · rw [off_succ φ j hj]; omega
            · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

private lemma off_add_lt_encode (φ : CNF) {i j : ℕ}
    (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
    ((φ.take i).map (fun c => c.length + 1)).sum + j < (encodeCNF φ).length := by
  have h1 : ((φ.take i).map (fun c => c.length + 1)).sum + j <
      ((φ.take (i + 1)).map (fun c => c.length + 1)).sum := by
    rw [off_succ φ i hi]; omega
  have h2 : ((φ.take (i + 1)).map (fun c => c.length + 1)).sum ≤
      ((φ.take φ.length).map (fun c => c.length + 1)).sum := off_mono φ (Nat.succ_le_of_lt hi)
  rw [List.take_length] at h2
  have h3 := sum_clause_le_encodeCNF φ
  omega

private lemma off_add_inj (φ : CNF) {i₁ j₁ i₂ j₂ : ℕ}
    (hi₁ : i₁ < φ.length) (hj₁ : j₁ ≤ (φ.getD i₁ []).length)
    (hi₂ : i₂ < φ.length) (hj₂ : j₂ ≤ (φ.getD i₂ []).length)
    (heq : ((φ.take i₁).map (fun c => c.length + 1)).sum + j₁ =
           ((φ.take i₂).map (fun c => c.length + 1)).sum + j₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · have h1 : ((φ.take i₁).map (fun c => c.length + 1)).sum + j₁ <
        ((φ.take (i₁ + 1)).map (fun c => c.length + 1)).sum := by
      rw [off_succ φ i₁ hi₁]; omega
    have h2 : ((φ.take (i₁ + 1)).map (fun c => c.length + 1)).sum ≤
        ((φ.take i₂).map (fun c => c.length + 1)).sum := off_mono φ (by omega)
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 : ((φ.take i₂).map (fun c => c.length + 1)).sum + j₂ <
        ((φ.take (i₂ + 1)).map (fun c => c.length + 1)).sum := by
      rw [off_succ φ i₂ hi₂]; omega
    have h2 : ((φ.take (i₂ + 1)).map (fun c => c.length + 1)).sum ≤
        ((φ.take i₁).map (fun c => c.length + 1)).sum := off_mono φ (by omega)
    omega

private lemma flat_length (φ : CNF) :
    (φ.flatMap (fun c => c.map some ++ [none])).length =
      (φ.map (fun c => c.length + 1)).sum := by
  induction φ with
  | nil => simp
  | cons c φ' ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_singleton,
      List.map_cons, List.sum_cons, ih]

private lemma flat_getElem?_off (φ : CNF) :
    ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (φ.flatMap (fun c => c.map some ++ [none]))[((φ.take i).map (fun c => c.length + 1)).sum + j]? =
        if j < (φ.getD i []).length then some (some ((φ.getD i []).getD j (0, false)))
        else some none := by
  induction φ with
  | nil => intro i j hi; simp at hi
  | cons c φ' ih =>
    intro i j hi hj
    cases i with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add,
        List.getD_cons_zero, List.flatMap_cons] at hj ⊢
      have hlt : j < (c.map some ++ [none]).length := by simp; omega
      rw [List.getElem?_append_left hlt]
      by_cases hjc : j < c.length
      · rw [if_pos hjc, List.getElem?_append_left (by simp; omega), List.getElem?_map,
          List.getElem?_eq_getElem hjc, List.getD_eq_getElem _ _ hjc]
        rfl
      · have hjeq : j = c.length := by omega
        subst hjeq
        rw [if_neg (lt_irrefl _), List.getElem?_append_right (by simp)]
        simp
    | succ i' =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simp only [List.getD_cons_succ] at hj ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons]
      have hlen : (c.map some ++ [none]).length = c.length + 1 := by simp
      rw [add_assoc, List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]
      exact ih i' j hi hj

private lemma flat_index_decompose (φ : CNF) :
    ∀ p, p < (φ.flatMap (fun c => c.map some ++ [none])).length →
      ∃ i < φ.length, ∃ j ≤ (φ.getD i []).length,
        ((φ.take i).map (fun c => c.length + 1)).sum + j = p := by
  induction φ with
  | nil => intro p hp; simp at hp
  | cons c φ' ih =>
    intro p hp
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_singleton] at hp
    by_cases hpc : p ≤ c.length
    · exact ⟨0, by simp, p, by simpa, by simp⟩
    · have hp' : p - (c.length + 1) < (φ'.flatMap (fun c => c.map some ++ [none])).length := by omega
      obtain ⟨i', hi', j, hj, heq⟩ := ih (p - (c.length + 1)) hp'
      refine ⟨i' + 1, by simp; omega, j, by simpa, ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

private lemma fresh_not_mem_vars (φ : CNF) : fresh φ ∉ vars φ := by
  intro h
  have hle : fresh φ ≤ (vars φ).sup id := Finset.le_sup (f := id) h
  dsimp only [fresh] at hle
  omega

private lemma mem_vars_of_clause_lit (φ : CNF) {i j : ℕ}
    (hi : i < φ.length) (hj : j < (φ.getD i []).length) :
    ((φ.getD i []).getD j (0, false)).1 ∈ vars φ := by
  rw [vars, List.mem_toFinset, List.mem_flatMap]
  refine ⟨φ.getD i [], ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.mem_map]
    refine ⟨(φ.getD i []).getD j (0, false), ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj

private lemma vars_cvcFormula_iff (φ : CNF) (z : ℕ) :
    z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
  simp only [vars, cvcFormula, List.mem_toFinset, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨c, (⟨c', hc', rfl⟩ | rfl), ⟨l, hl, rfl⟩⟩
    · simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · left; exact ⟨c', hc', ⟨l, hl, rfl⟩⟩
      · right; rfl
    · simp only [List.mem_singleton] at hl
      subst hl; right; rfl
  · rintro (⟨c', hc', ⟨l, hl, rfl⟩⟩ | rfl)
    · exact ⟨c' ++ [(fresh φ, true)], Or.inl ⟨c', hc', rfl⟩, ⟨l, List.mem_append_left _ hl, rfl⟩⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, ⟨(fresh φ, false), List.mem_singleton_self _, rfl⟩⟩

private lemma clauseAt_cvcFormula_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = (φ.getD i []) ++ [(fresh φ, true)] := by
  have hlen : i < (φ.map (fun C => C ++ [(fresh φ, true)])).length := by simp [hi]
  rw [clauseAt, cvcFormula, List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_left hlen, List.getElem_map, List.getD_eq_getElem _ _ hi]

private lemma clauseAt_cvcFormula_eq (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  have hlen : (φ.map (fun C => C ++ [(fresh φ, true)])).length = φ.length := by simp
  rw [clauseAt, cvcFormula, List.getD_eq_getElem _ _ (by simp),
    List.getElem_append_right (by omega)]
  simp [hlen]

private lemma clauseAt_cvcFormula_gt (φ : CNF) {i : ℕ} (hi : φ.length < i) :
    clauseAt (cvcFormula φ) i = [] := by
  rw [clauseAt, List.getD_eq_default]
  simp [cvcFormula]; omega

private lemma decode_triple {N k u₁ v₁ t₁ u₂ v₂ t₂ : ℕ}
    (hv₁ : v₁ < N) (ht₁ : t₁ < 2 * k) (hv₂ : v₂ < N) (ht₂ : t₂ < 2 * k)
    (heq : N + 2 * k * (u₁ * N + v₁) + t₁ = N + 2 * k * (u₂ * N + v₂) + t₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ t₁ = t₂ := by
  have hk : 0 < 2 * k := by omega
  have hN : 0 < N := by omega
  have h1 : 2 * k * (u₁ * N + v₁) + t₁ = 2 * k * (u₂ * N + v₂) + t₂ := by omega
  have ht : t₁ = t₂ := by
    have hm1 : (2 * k * (u₁ * N + v₁) + t₁) % (2 * k) = t₁ := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht₁]
    have hm2 : (2 * k * (u₂ * N + v₂) + t₂) % (2 * k) = t₂ := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht₂]
    have hm := congrArg (· % (2 * k)) h1
    rw [hm1, hm2] at hm
    exact hm
  have h2 : u₁ * N + v₁ = u₂ * N + v₂ := by
    have : 2 * k * (u₁ * N + v₁) = 2 * k * (u₂ * N + v₂) := by omega
    exact Nat.eq_of_mul_eq_mul_left hk this
  have hv : v₁ = v₂ := by
    have hm1 : (u₁ * N + v₁) % N = v₁ := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv₁]
    have hm2 : (u₂ * N + v₂) % N = v₂ := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv₂]
    have hm := congrArg (· % N) h2
    rw [hm1, hm2] at hm
    exact hm
  have hu : u₁ = u₂ := by
    have : u₁ * N = u₂ * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  exact ⟨hu, hv, ht⟩

private lemma nodup_inner_def (k N u v : ℕ) (b : Bool) :
    (((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
      (fun t => N + 2 * k * (u * N + v) + t)).Nodup := by
  apply List.Nodup.map
  · intro t₁ t₂ h; exact Nat.add_left_cancel h
  · exact (List.nodup_range).filter _

private lemma mem_inner_iff (k N u v : ℕ) (b : Bool) (x : ℕ) :
    x ∈ (((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
      (fun t => N + 2 * k * (u * N + v) + t)) ↔
    ∃ t < 2 * k, x = N + 2 * k * (u * N + v) + t ∧ (t % 2 = 1 ↔ b = true) := by
  simp only [List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨t, ⟨ht, hb⟩, rfl⟩
    refine ⟨t, ht, rfl, ?_⟩
    cases b <;> simp at hb ⊢ <;> omega
  · rintro ⟨t, ht, rfl, hb⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    cases b <;> simp at hb ⊢ <;> omega

private lemma nodup_append_of_disjoint {α : Type*} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hd : ∀ x, x ∈ l₁ → x ∉ l₂) :
    (l₁ ++ l₂).Nodup := by
  rw [List.nodup_append]
  exact ⟨h₁, h₂, fun a ha b hb hab => hd a ha (hab ▸ hb)⟩

end PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise PEqualNP.Outside.L_meta_497_aux in
theorem PEqualNP.Outside.L_meta_497 : ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff he_lt he_inj he_idx num hnum_var hnum_fresh hnum_occ hnum_last
    H hH f hf TH hTH lit hlit inner hinner TL hTL
  have hoff_lt : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → off i + j < E := by
    intro i j hi hj
    rw [hoff i, hE]
    exact off_add_lt_encode φ hi hj
  have hoff_inj : ∀ i₁ j₁ i₂ j₂,
      i₁ < φ.length → j₁ ≤ (φ.getD i₁ []).length →
      i₂ < φ.length → j₂ ≤ (φ.getD i₂ []).length →
      off i₁ + j₁ = off i₂ + j₂ → i₁ = i₂ ∧ j₁ = j₂ := by
    intro i₁ j₁ i₂ j₂ hi₁ hj₁ hi₂ hj₂ heq
    rw [hoff i₁, hoff i₂] at heq
    exact off_add_inj φ hi₁ hj₁ hi₂ hj₂ heq
  have hlit_lt : ∀ i j, j < (φ.getD i []).length →
      lit i j = (φ.getD i []).getD j (0, false) := by
    intro i j hj
    rw [hlit i j, List.getD_eq_getElem _ _ (by simp only [List.length_append, List.length_singleton]; omega),
      List.getElem_append_left hj, List.getD_eq_getElem _ _ hj]
  have hlit_eq : ∀ i, lit i (φ.getD i []).length = (fresh φ, true) := by
    intro i
    rw [hlit i _, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
    simp
  have hlit_var : ∀ i j, i < φ.length → j < (φ.getD i []).length → (lit i j).1 ∈ vars φ := by
    intro i j hi hj
    rw [hlit_lt i j hj]
    exact mem_vars_of_clause_lit φ hi hj
  have hnum_lit_lt : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inl (lit i j)) < 2 * (E + 1) := by
    intro i j hi hj
    by_cases hlt : j < (φ.getD i []).length
    · have hv := hlit_var i j hi hlt
      have hnv := hnum_var (lit i j).1 hv (lit i j).2
      have hltE := he_lt (lit i j).1 hv
      have hpair : ((lit i j).1, (lit i j).2) = lit i j := rfl
      rw [hpair] at hnv
      cases hpol : (lit i j).2 <;> simp [hpol] at hnv <;> omega
    · have hjeq : j = (φ.getD i []).length := by omega
      subst hjeq
      rw [hlit_eq i, hnum_fresh true]
      simp; omega
  have hnum_occ_bounds : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      2 * (E + 1) ≤ num (Sum.inr (i, j)) ∧ num (Sum.inr (i, j)) < 3 * E + 2 := by
    intro i j hi hj
    rw [hnum_occ i j hi hj]
    have := hoff_lt i j hi hj
    omega
  have hvar_unique_ij : ∀ z ∈ vars φ, ∃ i < φ.length, ∃ j < (φ.getD i []).length,
      off i + j = e z ∧ (lit i j).1 = z := by
    intro z hz
    obtain ⟨l, hl_get, hl_fst⟩ := he_idx z hz
    have hlt_flat : e z < (φ.flatMap (fun c => c.map some ++ [none])).length := by
      by_contra hge
      have hnone : (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = none :=
        List.getElem?_eq_none (Nat.le_of_not_lt hge)
      rw [hnone] at hl_get
      cases hl_get
    obtain ⟨i, hi, j, hj, heq⟩ := flat_index_decompose φ (e z) hlt_flat
    have hget := flat_getElem?_off φ i j hi hj
    rw [heq, hl_get] at hget
    by_cases hlt : j < (φ.getD i []).length
    · rw [if_pos hlt] at hget
      have hle : l = (φ.getD i []).getD j (0, false) := by
        injection hget with h1; injection h1
      refine ⟨i, hi, j, hlt, ?_, ?_⟩
      · rw [hoff i]; exact heq
      · rw [hlit_lt i j hlt, ← hle, hl_fst]
    · rw [if_neg hlt] at hget
      cases hget
  have hTH_lt : ∀ a, TH a → a < N := by
    intro a ha
    rw [hTH] at ha
    rcases ha with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, _, rfl⟩ | rfl
    · have := he_lt z hz; omega
    · omega
    · have := hoff_lt i j hi hj; omega
    · omega
  have hTH_var : ∀ z ∈ vars φ, ∀ b : Bool, TH (num (Sum.inl (z, b))) ↔ b = true := by
    intro z hz b
    rw [hnum_var z hz b, hTH]
    have hltE := he_lt z hz
    cases b
    · simp only [Bool.false_eq_true, iff_false, ite_false, add_zero]
      rintro (⟨z', hz', heq⟩ | heq | ⟨i, hi, j, hj, _, heq⟩ | heq)
      · omega
      · omega
      · omega
      · omega
    · simp only [ite_true, iff_true]
      left; exact ⟨z, hz, rfl⟩
  have hTH_fresh : ∀ b : Bool, TH (num (Sum.inl (fresh φ, b))) ↔ b = true := by
    intro b
    rw [hnum_fresh b, hTH]
    cases b
    · simp only [Bool.false_eq_true, iff_false, ite_false, add_zero]
      rintro (⟨z', hz', heq⟩ | heq | ⟨i, hi, j, hj, _, heq⟩ | heq)
      · omega
      · omega
      · omega
      · omega
    · simp
  have hTH_lit : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2 = true) := by
    intro i j hi hj
    by_cases hlt : j < (φ.getD i []).length
    · have hv := hlit_var i j hi hlt
      exact hTH_var (lit i j).1 hv (lit i j).2
    · have hjeq : j = (φ.getD i []).length := by omega
      subst hjeq
      rw [hlit_eq i]
      exact hTH_fresh true
  have hTH_occ : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (num (Sum.inr (i, j))) ↔ j ≠ f i) := by
    intro i j hi hj
    rw [hnum_occ i j hi hj, hTH]
    have hltE := hoff_lt i j hi hj
    constructor
    · rintro (⟨z, hz, heq⟩ | heq | ⟨i', hi', j', hj', hne, heq⟩ | heq)
      · have := he_lt z hz; omega
      · omega
      · have heq' : off i + j = off i' + j' := by omega
        obtain ⟨rfl, rfl⟩ := hoff_inj i j i' j' hi hj hi' hj' heq'
        exact hne
      · omega
    · intro hne
      right; right; left
      exact ⟨i, hi, j, hj, hne, rfl⟩
  have hTH_last : TH (num (Sum.inr (φ.length, 0))) := by
    rw [hnum_last, hTH]; right; right; right; rfl
  have hinner_mem : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t < 2 * k, x = N + 2 * k * (u * N + v) + t ∧ (t % 2 = 1 ↔ b = true) := by
    intro u v b x
    rw [hinner u v b]
    exact mem_inner_iff k N u v b x
  have hinner_nodup : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner u v b]
    exact nodup_inner_def k N u v b
  have hinner_ge : ∀ u v b x, x ∈ inner u v b → N ≤ x := by
    intro u v b x hx
    rw [hinner_mem] at hx
    rcases hx with ⟨t, _, rfl, _⟩
    omega
  have hinner_disj : ∀ u₁ v₁ b₁ u₂ v₂ b₂,
      v₁ < N → v₂ < N → (u₁ ≠ u₂ ∨ v₁ ≠ v₂) →
      ∀ x, x ∈ inner u₁ v₁ b₁ → x ∉ inner u₂ v₂ b₂ := by
    intro u₁ v₁ b₁ u₂ v₂ b₂ hv₁ hv₂ hne x hx₁ hx₂
    rw [hinner_mem] at hx₁ hx₂
    rcases hx₁ with ⟨t₁, ht₁, rfl, _⟩
    rcases hx₂ with ⟨t₂, ht₂, heq, _⟩
    obtain ⟨hu, hv, _⟩ := decode_triple hv₁ ht₁ hv₂ ht₂ heq
    rcases hne with h | h
    · exact h hu
    · exact h hv
  -- Characterize directed edges (a < b) of H
  have hH_dir : ∀ a b : Fin N, a < b → (H.Adj a b ↔
      (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length,
        a.val = num (Sum.inl (lit i j)) ∧ b.val = num (Sum.inr (i, j))) ∨
      (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, ∃ l ≤ (φ.getD i []).length, j < l ∧
        a.val = num (Sum.inr (i, j)) ∧ b.val = num (Sum.inr (i, l))) ∨
      (∃ z ∈ vars φ, a.val = num (Sum.inl (z, false)) ∧ b.val = num (Sum.inl (z, true))) ∨
      (a.val = num (Sum.inl (fresh φ, false)) ∧ b.val = num (Sum.inl (fresh φ, true))) ∨
      (a.val = num (Sum.inl (fresh φ, false)) ∧ b.val = num (Sum.inr (φ.length, 0)))) := by
    intro a b hab
    rw [hH a b]
    have habv : a.val < b.val := hab
    constructor
    · rintro ⟨u, v, hadj, hu, hv⟩
      cases u with
      | inl l₁ =>
        cases v with
        | inl l₂ =>
          simp only [cvcGraph, satGraph, satAdj] at hadj
          obtain ⟨hvar, hpol, hmem⟩ := hadj
          rw [vars_cvcFormula_iff] at hmem
          rcases hmem with hmem | hmem
          · have h1 := hnum_var l₁.1 hmem l₁.2
            have h2 := hnum_var l₁.1 hmem l₂.2
            have hpair1 : (l₁.1, l₁.2) = l₁ := rfl
            have hpair2 : (l₁.1, l₂.2) = l₂ := by ext; exact hvar; rfl
            rw [hpair1] at h1; rw [hpair2] at h2
            cases h1p : l₁.2 <;> cases h2p : l₂.2
            · exact absurd (h1p.trans h2p.symm) hpol
            · right; right; left
              refine ⟨l₁.1, hmem, ?_, ?_⟩
              · rw [← hu, hnum_var l₁.1 hmem false, h1, h1p]
              · rw [← hv, hnum_var l₁.1 hmem true, h2, h2p]
            · rw [h1p] at h1; rw [h2p] at h2; simp at h1 h2; omega
            · exact absurd (h1p.trans h2p.symm) hpol
          · have h1 := hnum_fresh l₁.2
            have h2 := hnum_fresh l₂.2
            have hl1 : l₁ = (fresh φ, l₁.2) := by ext; exact hmem; rfl
            have hl2 : l₂ = (fresh φ, l₂.2) := by ext; exact hvar.symm.trans hmem; rfl
            rw [← hl1] at h1; rw [← hl2] at h2
            cases h1p : l₁.2 <;> cases h2p : l₂.2
            · exact absurd (h1p.trans h2p.symm) hpol
            · right; right; right; left
              refine ⟨?_, ?_⟩
              · rw [← hu, hnum_fresh false, h1, h1p]
              · rw [← hv, hnum_fresh true, h2, h2p]
            · rw [h1p] at h1; rw [h2p] at h2; simp at h1 h2; omega
            · exact absurd (h1p.trans h2p.symm) hpol
        | inr p =>
          rcases p with ⟨i, j⟩
          simp only [cvcGraph, satGraph, satAdj] at hadj
          rcases lt_trichotomy i φ.length with hi | rfl | hi
          · rw [clauseAt_cvcFormula_lt φ hi] at hadj
            have hj : j ≤ (φ.getD i []).length := by
              by_contra hgt
              have hge : ((φ.getD i []) ++ [(fresh φ, true)]).length ≤ j := by
                simp only [List.length_append, List.length_singleton]; omega
              rw [List.getElem?_eq_none hge] at hadj
              cases hadj
            have hlit_eq' : lit i j = l₁ := by
              rw [hlit i j, List.getD_eq_getElem?_getD, hadj]; rfl
            left
            exact ⟨i, hi, j, hj, by rw [← hu, hlit_eq'], hv.symm⟩
          · rw [clauseAt_cvcFormula_eq φ] at hadj
            have hj0 : j = 0 := by
              cases j with
              | zero => rfl
              | succ j' => simp at hadj
            subst hj0
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hadj
            subst hadj
            right; right; right; right
            exact ⟨hu.symm, hv.symm⟩
          · rw [clauseAt_cvcFormula_gt φ hi] at hadj
            simp at hadj
      | inr p =>
        rcases p with ⟨i, j⟩
        cases v with
        | inl l₂ =>
          simp only [cvcGraph, satGraph, satAdj] at hadj
          exfalso
          rcases lt_trichotomy i φ.length with hi | rfl | hi
          · rw [clauseAt_cvcFormula_lt φ hi] at hadj
            have hj : j ≤ (φ.getD i []).length := by
              by_contra hgt
              have hge : ((φ.getD i []) ++ [(fresh φ, true)]).length ≤ j := by
                simp only [List.length_append, List.length_singleton]; omega
              rw [List.getElem?_eq_none hge] at hadj
              cases hadj
            have hlit_eq' : lit i j = l₂ := by
              rw [hlit i j, List.getD_eq_getElem?_getD, hadj]; rfl
            have hb1 := hnum_occ_bounds i j hi hj
            have hb2 := hnum_lit_lt i j hi hj
            rw [hlit_eq'] at hb2
            omega
          · rw [clauseAt_cvcFormula_eq φ] at hadj
            have hj0 : j = 0 := by
              cases j with
              | zero => rfl
              | succ j' => simp at hadj
            subst hj0
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hadj
            subst hadj
            rw [hnum_last] at hu
            rw [hnum_fresh false] at hv
            simp at hv; omega
          · rw [clauseAt_cvcFormula_gt φ hi] at hadj
            simp at hadj
        | inr q =>
          rcases q with ⟨i', l⟩
          simp only [cvcGraph, satGraph, satAdj] at hadj
          obtain ⟨rfl, hne, hj, hl⟩ := hadj
          rcases lt_trichotomy i φ.length with hi | rfl | hi
          · rw [clauseAt_cvcFormula_lt φ hi] at hj hl
            simp only [List.length_append, List.length_singleton] at hj hl
            have hj' : j ≤ (φ.getD i []).length := by omega
            have hl' : l ≤ (φ.getD i []).length := by omega
            have hnu := hnum_occ i j hi hj'
            have hnv := hnum_occ i l hi hl'
            have hjl : j < l := by omega
            right; left
            exact ⟨i, hi, j, hj', l, hl', hjl, hu.symm, hv.symm⟩
          · rw [clauseAt_cvcFormula_eq φ] at hj hl
            simp at hj hl; omega
          · rw [clauseAt_cvcFormula_gt φ hi] at hj
            simp at hj
    · rintro (⟨i, hi, j, hj, ha, hb⟩ | ⟨i, hi, j, hj, l, hl, hjl, ha, hb⟩ |
              ⟨z, hz, ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩)
      · refine ⟨Sum.inl (lit i j), Sum.inr (i, j), ?_, ha.symm, hb.symm⟩
        change satAdj (cvcFormula φ) (Sum.inl (lit i j)) (Sum.inr (i, j))
        simp only [satAdj]
        have hlen : j < ((φ.getD i []) ++ [(fresh φ, true)]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [clauseAt_cvcFormula_lt φ hi, hlit i j, List.getElem?_eq_getElem hlen,
          List.getD_eq_getElem _ _ hlen]
      · refine ⟨Sum.inr (i, j), Sum.inr (i, l), ?_, ha.symm, hb.symm⟩
        change satAdj (cvcFormula φ) (Sum.inr (i, j)) (Sum.inr (i, l))
        simp only [satAdj]
        rw [clauseAt_cvcFormula_lt φ hi]
        exact ⟨trivial, by omega, by simp only [List.length_append, List.length_singleton]; omega,
          by simp only [List.length_append, List.length_singleton]; omega⟩
      · refine ⟨Sum.inl (z, false), Sum.inl (z, true), ?_, ha.symm, hb.symm⟩
        change satAdj (cvcFormula φ) (Sum.inl (z, false)) (Sum.inl (z, true))
        simp only [satAdj]
        exact ⟨trivial, by decide, (vars_cvcFormula_iff φ z).mpr (Or.inl hz)⟩
      · refine ⟨Sum.inl (fresh φ, false), Sum.inl (fresh φ, true), ?_, ha.symm, hb.symm⟩
        change satAdj (cvcFormula φ) (Sum.inl (fresh φ, false)) (Sum.inl (fresh φ, true))
        simp only [satAdj]
        exact ⟨trivial, by decide, (vars_cvcFormula_iff φ (fresh φ)).mpr (Or.inr rfl)⟩
      · refine ⟨Sum.inl (fresh φ, false), Sum.inr (φ.length, 0), ?_, ha.symm, hb.symm⟩
        change satAdj (cvcFormula φ) (Sum.inl (fresh φ, false)) (Sum.inr (φ.length, 0))
        simp only [satAdj]
        rw [clauseAt_cvcFormula_eq φ]
        rfl
  -- Define pieces of TL for clarity
  let cell (i j : ℕ) : List ℕ :=
    inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
    ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
      (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++
    (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
      inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
    else []) ++
    (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
    (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
      [num (Sum.inl ((lit i j).1, true))]
    else [])
  let mainList : List ℕ :=
    (List.range φ.length).flatMap (fun i =>
      (List.range ((φ.getD i []).length + 1)).flatMap (fun j => cell i j))
  let tailList : List ℕ :=
    inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++
    inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++
    [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]
  have hTL_eq : TL = mainList ++ tailList := hTL
  -- Membership characterization of cell i j
  have hcell_mem : ∀ i j x, x ∈ cell i j ↔
      x ∈ inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ∨
      (∃ l ≤ (φ.getD i []).length, j < l ∧
        x ∈ inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ∨
      (j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
        x ∈ inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false) ∨
      (j ≠ f i ∧ x = num (Sum.inr (i, j))) ∨
      (j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
        x = num (Sum.inl ((lit i j).1, true))) := by
    intro i j x
    dsimp only [cell]
    simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    have hite1 : ∀ (P : Prop) [Decidable P] (L : List ℕ),
        x ∈ (if P then L else []) ↔ P ∧ x ∈ L := by
      intro P _ L; split_ifs with h <;> simp [h]
    rw [hite1, hite1, hite1, List.mem_singleton, List.mem_singleton]
    constructor
    · rintro (((((h1 | ⟨l, ⟨hl, hjl⟩, h2⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2⟩) | ⟨⟨h1, h2⟩, h3⟩))
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨l, by omega, hjl, h2⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, h3⟩)))
    · rintro (h1 | ⟨l, hl, hjl, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, ⟨by omega, hjl⟩, h2⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨⟨h1, h2⟩, h3⟩))
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr ⟨⟨h1, h2⟩, h3⟩
  -- Nodup of cell i j
  have hcell_nodup : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length, (cell i j).Nodup := by
    intro i hi j hj
    dsimp only [cell]
    have hb_occ := hnum_occ_bounds i j hi hj
    have hb_lit := hnum_lit_lt i j hi hj
    have hN_lit : num (Sum.inl (lit i j)) < N := by omega
    have hN_occ : num (Sum.inr (i, j)) < N := by omega
    have hpart1 : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2).Nodup :=
      hinner_nodup _ _ _
    have hpart2 : (((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
        (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))).Nodup := by
      rw [List.nodup_flatMap]
      refine ⟨fun l _ => hinner_nodup _ _ _, ?_⟩
      refine List.Pairwise.imp_of_mem ?_ ((List.nodup_range).filter _)
      intro l₁ l₂ hl₁ hl₂ hne
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl₁ hl₂
      have hb₁ := hnum_occ_bounds i l₁ hi (by omega)
      have hb₂ := hnum_occ_bounds i l₂ hi (by omega)
      dsimp only [Function.onFun]
      rw [List.disjoint_iff_ne]
      intro x hx₁ y hy₂ hxy
      subst hxy
      refine hinner_disj _ _ _ _ _ _ (by omega) (by omega) (Or.inr ?_) x hx₁ hy₂
      rw [hnum_occ i l₁ hi (by omega), hnum_occ i l₂ hi (by omega)]
      omega
    have h12 : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))).Nodup := by
      refine nodup_append_of_disjoint hpart1 hpart2 ?_
      intro x hx₁ hx₂
      simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx₂
      rcases hx₂ with ⟨l, ⟨hl, _⟩, hx₂⟩
      have hbl := hnum_occ_bounds i l hi (by omega)
      exact hinner_disj _ _ _ _ _ _ hN_occ (by omega) (Or.inl (by omega)) x hx₁ hx₂
    have hpart3 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
      else []).Nodup := by
      split_ifs
      · exact hinner_nodup _ _ _
      · exact List.nodup_nil
    have h123 : ((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
        else [])).Nodup := by
      refine nodup_append_of_disjoint h12 hpart3 ?_
      intro x hx12 hx3
      split_ifs at hx3 with hc
      · have hv := hlit_var i j hi hc.1
        have hltE := he_lt (lit i j).1 hv
        have hnT := hnum_var (lit i j).1 hv true
        have hnF := hnum_var (lit i j).1 hv false
        simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
          decide_eq_true_eq] at hx12
        rcases hx12 with hx1 | ⟨l, ⟨hl, _⟩, hx2⟩
        · exact hinner_disj _ _ _ _ _ _ hN_occ (by simp at hnT; omega)
            (Or.inr (by simp at hnT; omega)) x hx1 hx3
        · have hbl := hnum_occ_bounds i l hi (by omega)
          exact hinner_disj _ _ _ _ _ _ (by omega) (by simp at hnT; omega)
            (Or.inr (by simp at hnT; omega)) x hx2 hx3
      · simp at hx3
    have hpart4 : (if j ≠ f i then [num (Sum.inr (i, j))] else []).Nodup := by
      split_ifs <;> simp
    have h1234 : (((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
        else [])) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else [])).Nodup := by
      refine nodup_append_of_disjoint h123 hpart4 ?_
      intro x hx123 hx4
      split_ifs at hx4 with hne
      · simp only [List.mem_singleton] at hx4
        subst hx4
        have hge : N ≤ num (Sum.inr (i, j)) := by
          simp only [List.mem_append, List.mem_flatMap] at hx123
          rcases hx123 with (h1 | ⟨_, _, h2⟩) | h3
          · exact hinner_ge _ _ _ _ h1
          · exact hinner_ge _ _ _ _ h2
          · split_ifs at h3
            · exact hinner_ge _ _ _ _ h3
            · simp at h3
        omega
      · simp at hx4
    have hpart5 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        [num (Sum.inl ((lit i j).1, true))] else []).Nodup := by
      split_ifs <;> simp
    refine nodup_append_of_disjoint h1234 hpart5 ?_
    intro x hx1234 hx5
    split_ifs at hx5 with hc
    · simp only [List.mem_singleton] at hx5
      subst hx5
      have hv := hlit_var i j hi hc.1
      have hltE := he_lt (lit i j).1 hv
      have hnT := hnum_var (lit i j).1 hv true
      simp only [List.mem_append, List.mem_flatMap] at hx1234
      rcases hx1234 with ((h1 | ⟨_, _, h2⟩) | h3) | h4
      · have := hinner_ge _ _ _ _ h1; simp at hnT; omega
      · have := hinner_ge _ _ _ _ h2; simp at hnT; omega
      · rw [if_pos hc] at h3
        have := hinner_ge _ _ _ _ h3; simp at hnT; omega
      · split_ifs at h4
        · simp only [List.mem_singleton] at h4
          simp at hnT; omega
        · simp at h4
    · simp at hx5
  -- Disjointness between distinct cells (i₁, j₁) ≠ (i₂, j₂)
  have hcell_disj : ∀ i₁ j₁ i₂ j₂,
      i₁ < φ.length → j₁ ≤ (φ.getD i₁ []).length →
      i₂ < φ.length → j₂ ≤ (φ.getD i₂ []).length →
      (i₁ ≠ i₂ ∨ j₁ ≠ j₂) →
      ∀ x, x ∈ cell i₁ j₁ → x ∉ cell i₂ j₂ := by
    intro i₁ j₁ i₂ j₂ hi₁ hj₁ hi₂ hj₂ hne x hx₁ hx₂
    have hocc_ne : num (Sum.inr (i₁, j₁)) ≠ num (Sum.inr (i₂, j₂)) := by
      intro heq
      rw [hnum_occ i₁ j₁ hi₁ hj₁, hnum_occ i₂ j₂ hi₂ hj₂] at heq
      obtain ⟨rfl, rfl⟩ := hoff_inj i₁ j₁ i₂ j₂ hi₁ hj₁ hi₂ hj₂ (by omega)
      rcases hne with h | h <;> exact h rfl
    have hb₁ := hnum_occ_bounds i₁ j₁ hi₁ hj₁
    have hb₂ := hnum_occ_bounds i₂ j₂ hi₂ hj₂
    have hl₁ := hnum_lit_lt i₁ j₁ hi₁ hj₁
    have hl₂ := hnum_lit_lt i₂ j₂ hi₂ hj₂
    rw [hcell_mem] at hx₁ hx₂
    -- Split by whether x < N or x ≥ N
    by_cases hxN : x < N
    · -- Only branches 4 and 5 can have x < N
      have hx₁' : (j₁ ≠ f i₁ ∧ x = num (Sum.inr (i₁, j₁))) ∨
          (j₁ < (φ.getD i₁ []).length ∧ off i₁ + j₁ = e (lit i₁ j₁).1 ∧
            x = num (Sum.inl ((lit i₁ j₁).1, true))) := by
        rcases hx₁ with h | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | h | h
        · exact absurd (hinner_ge _ _ _ _ h) (by omega)
        · exact absurd (hinner_ge _ _ _ _ h) (by omega)
        · exact absurd (hinner_ge _ _ _ _ h) (by omega)
        · exact Or.inl h
        · exact Or.inr h
      have hx₂' : (j₂ ≠ f i₂ ∧ x = num (Sum.inr (i₂, j₂))) ∨
          (j₂ < (φ.getD i₂ []).length ∧ off i₂ + j₂ = e (lit i₂ j₂).1 ∧
            x = num (Sum.inl ((lit i₂ j₂).1, true))) := by
        rcases hx₂ with h | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | h | h
        · exact absurd (hinner_ge _ _ _ _ h) (by omega)
        · exact absurd (hinner_ge _ _ _ _ h) (by omega)
        · exact absurd (hinner_ge _ _ _ _ h) (by omega)
        · exact Or.inl h
        · exact Or.inr h
      rcases hx₁' with ⟨_, rfl⟩ | ⟨hjl₁, heq₁, rfl⟩
      · rcases hx₂' with ⟨_, heq⟩ | ⟨hjl₂, _, heq⟩
        · exact hocc_ne heq
        · have hv₂ := hlit_var i₂ j₂ hi₂ hjl₂
          have hn₂ := hnum_var (lit i₂ j₂).1 hv₂ true
          have hlt₂ := he_lt (lit i₂ j₂).1 hv₂
          simp at hn₂; omega
      · have hv₁ := hlit_var i₁ j₁ hi₁ hjl₁
        have hn₁ := hnum_var (lit i₁ j₁).1 hv₁ true
        have hlt₁ := he_lt (lit i₁ j₁).1 hv₁
        rcases hx₂' with ⟨_, heq⟩ | ⟨hjl₂, heq₂, heq⟩
        · simp at hn₁; omega
        · have hv₂ := hlit_var i₂ j₂ hi₂ hjl₂
          have hn₂ := hnum_var (lit i₂ j₂).1 hv₂ true
          rw [hn₁, hn₂] at heq
          simp at heq
          have heqe : e (lit i₁ j₁).1 = e (lit i₂ j₂).1 := by omega
          have hoff_eq : off i₁ + j₁ = off i₂ + j₂ := by omega
          obtain ⟨rfl, rfl⟩ := hoff_inj i₁ j₁ i₂ j₂ hi₁ hj₁ hi₂ hj₂ hoff_eq
          rcases hne with h | h <;> exact h rfl
    · -- Only branches 1, 2, 3 can have x ≥ N
      have hx₁' : x ∈ inner (num (Sum.inl (lit i₁ j₁))) (num (Sum.inr (i₁, j₁))) (lit i₁ j₁).2 ∨
          (∃ l₁ ≤ (φ.getD i₁ []).length, j₁ < l₁ ∧
            x ∈ inner (num (Sum.inr (i₁, j₁))) (num (Sum.inr (i₁, l₁))) (decide (j₁ ≠ f i₁))) ∨
          (j₁ < (φ.getD i₁ []).length ∧ off i₁ + j₁ = e (lit i₁ j₁).1 ∧
            x ∈ inner (num (Sum.inl ((lit i₁ j₁).1, false))) (num (Sum.inl ((lit i₁ j₁).1, true))) false) := by
        rcases hx₁ with h | h | h | ⟨_, rfl⟩ | ⟨hjl₁, _, rfl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · omega
        · have hv₁ := hlit_var i₁ j₁ hi₁ hjl₁
          have hn₁ := hnum_var (lit i₁ j₁).1 hv₁ true
          have hlt₁ := he_lt (lit i₁ j₁).1 hv₁
          simp at hn₁; omega
      have hx₂' : x ∈ inner (num (Sum.inl (lit i₂ j₂))) (num (Sum.inr (i₂, j₂))) (lit i₂ j₂).2 ∨
          (∃ l₂ ≤ (φ.getD i₂ []).length, j₂ < l₂ ∧
            x ∈ inner (num (Sum.inr (i₂, j₂))) (num (Sum.inr (i₂, l₂))) (decide (j₂ ≠ f i₂))) ∨
          (j₂ < (φ.getD i₂ []).length ∧ off i₂ + j₂ = e (lit i₂ j₂).1 ∧
            x ∈ inner (num (Sum.inl ((lit i₂ j₂).1, false))) (num (Sum.inl ((lit i₂ j₂).1, true))) false) := by
        rcases hx₂ with h | h | h | ⟨_, rfl⟩ | ⟨hjl₂, _, rfl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · omega
        · have hv₂ := hlit_var i₂ j₂ hi₂ hjl₂
          have hn₂ := hnum_var (lit i₂ j₂).1 hv₂ true
          have hlt₂ := he_lt (lit i₂ j₂).1 hv₂
          simp at hn₂; omega
      rcases hx₁' with h₁ | ⟨l₁, hl₁', _, h₁⟩ | ⟨hjl₁, heq₁, h₁⟩
      · rcases hx₂' with h₂ | ⟨l₂, hl₂', _, h₂⟩ | ⟨hjl₂, _, h₂⟩
        · exact hinner_disj _ _ _ _ _ _ (by omega) (by omega) (Or.inr hocc_ne) x h₁ h₂
        · have hbl₂ := hnum_occ_bounds i₂ l₂ hi₂ hl₂'
          exact hinner_disj _ _ _ _ _ _ (by omega) (by omega) (Or.inl (by omega)) x h₁ h₂
        · have hv₂ := hlit_var i₂ j₂ hi₂ hjl₂
          have hn₂ := hnum_var (lit i₂ j₂).1 hv₂ true
          have hlt₂ := he_lt (lit i₂ j₂).1 hv₂
          exact hinner_disj _ _ _ _ _ _ (by omega) (by simp at hn₂; omega)
            (Or.inr (by simp at hn₂; omega)) x h₁ h₂
      · have hbl₁ := hnum_occ_bounds i₁ l₁ hi₁ hl₁'
        rcases hx₂' with h₂ | ⟨l₂, hl₂', _, h₂⟩ | ⟨hjl₂, _, h₂⟩
        · exact hinner_disj _ _ _ _ _ _ (by omega) (by omega) (Or.inl (by omega)) x h₁ h₂
        · have hbl₂ := hnum_occ_bounds i₂ l₂ hi₂ hl₂'
          exact hinner_disj _ _ _ _ _ _ (by omega) (by omega) (Or.inl hocc_ne) x h₁ h₂
        · have hv₂ := hlit_var i₂ j₂ hi₂ hjl₂
          have hn₂ := hnum_var (lit i₂ j₂).1 hv₂ true
          have hlt₂ := he_lt (lit i₂ j₂).1 hv₂
          exact hinner_disj _ _ _ _ _ _ (by omega) (by simp at hn₂; omega)
            (Or.inr (by simp at hn₂; omega)) x h₁ h₂
      · have hv₁ := hlit_var i₁ j₁ hi₁ hjl₁
        have hn₁T := hnum_var (lit i₁ j₁).1 hv₁ true
        have hn₁F := hnum_var (lit i₁ j₁).1 hv₁ false
        have hlt₁ := he_lt (lit i₁ j₁).1 hv₁
        rcases hx₂' with h₂ | ⟨l₂, hl₂', _, h₂⟩ | ⟨hjl₂, heq₂, h₂⟩
        · exact hinner_disj _ _ _ _ _ _ (by simp at hn₁T; omega) (by omega)
            (Or.inr (by simp at hn₁T; omega)) x h₁ h₂
        · have hbl₂ := hnum_occ_bounds i₂ l₂ hi₂ hl₂'
          exact hinner_disj _ _ _ _ _ _ (by simp at hn₁T; omega) (by omega)
            (Or.inr (by simp at hn₁T; omega)) x h₁ h₂
        · have hv₂ := hlit_var i₂ j₂ hi₂ hjl₂
          have hn₂T := hnum_var (lit i₂ j₂).1 hv₂ true
          have hn₂F := hnum_var (lit i₂ j₂).1 hv₂ false
          have hlt₂ := he_lt (lit i₂ j₂).1 hv₂
          refine hinner_disj _ _ _ _ _ _ (by simp at hn₁T; omega) (by simp at hn₂T; omega)
            (Or.inl ?_) x h₁ h₂
          intro heq
          rw [hn₁F, hn₂F] at heq
          simp at heq
          have hoff_eq : off i₁ + j₁ = off i₂ + j₂ := by omega
          obtain ⟨rfl, rfl⟩ := hoff_inj i₁ j₁ i₂ j₂ hi₁ hj₁ hi₂ hj₂ hoff_eq
          rcases hne with h | h <;> exact h rfl
  -- Nodup of mainList
  have hmain_nodup : mainList.Nodup := by
    dsimp only [mainList]
    rw [List.nodup_flatMap]
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [List.mem_range] at hi
      rw [List.nodup_flatMap]
      refine ⟨fun j hj => ?_, ?_⟩
      · simp only [List.mem_range] at hj
        exact hcell_nodup i hi j (by omega)
      · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
        intro j₁ j₂ hj₁ hj₂ hne
        simp only [List.mem_range] at hj₁ hj₂
        dsimp only [Function.onFun]
        rw [List.disjoint_iff_ne]
        intro x hx₁ y hy₂ hxy
        subst hxy
        exact hcell_disj i j₁ i j₂ hi (by omega) hi (by omega) (Or.inr hne) x hx₁ hy₂
    · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
      intro i₁ i₂ hi₁ hi₂ hne
      simp only [List.mem_range] at hi₁ hi₂
      dsimp only [Function.onFun]
      rw [List.disjoint_iff_ne]
      intro x hx₁ y hy₂ hxy
      subst hxy
      simp only [List.mem_flatMap, List.mem_range] at hx₁ hy₂
      rcases hx₁ with ⟨j₁, hj₁, hx₁⟩
      rcases hy₂ with ⟨j₂, hj₂, hx₂⟩
      exact hcell_disj i₁ j₁ i₂ j₂ hi₁ (by omega) hi₂ (by omega) (Or.inl hne) x hx₁ hx₂
  -- Nodup of tailList
  have htail_nodup : tailList.Nodup := by
    dsimp only [tailList]
    have hnfF := hnum_fresh false
    have hnfT := hnum_fresh true
    have hnl := hnum_last
    have h12 : (inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++
        inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false).Nodup := by
      refine nodup_append_of_disjoint (hinner_nodup _ _ _) (hinner_nodup _ _ _) ?_
      exact hinner_disj _ _ _ _ _ _ (by simp at hnfT; omega) (by omega)
        (Or.inr (by simp at hnfT; omega))
    have h3 : ([num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
        not_false_eq_true, and_true]
      simp at hnfT; omega
    refine nodup_append_of_disjoint h12 h3 ?_
    intro x hx12 hx3
    have hge : N ≤ x := by
      simp only [List.mem_append] at hx12
      rcases hx12 with h | h <;> exact hinner_ge _ _ _ _ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx3
    rcases hx3 with rfl | rfl <;> simp at hnfT <;> omega
  -- Disjointness of mainList and tailList
  have hmain_tail_disj : ∀ x, x ∈ mainList → x ∉ tailList := by
    intro x hxm hxt
    have hnfF := hnum_fresh false
    have hnfT := hnum_fresh true
    have hnl := hnum_last
    dsimp only [mainList, tailList] at hxm hxt
    simp only [List.mem_flatMap, List.mem_range] at hxm
    rcases hxm with ⟨i, hi, j, hj, hxc⟩
    have hj' : j ≤ (φ.getD i []).length := by omega
    have hb_occ := hnum_occ_bounds i j hi hj'
    have hb_lit := hnum_lit_lt i j hi hj'
    rw [hcell_mem] at hxc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hxt
    rcases hxt with (ht1 | ht2) | (rfl | rfl)
    · -- ht1: inner (2E, 2E+1)
      rcases hxc with hc1 | ⟨l, hl, _, hc2⟩ | ⟨hjl, _, hc3⟩ | ⟨_, rfl⟩ | ⟨hjl, _, rfl⟩
      · exact hinner_disj _ _ _ _ _ _ (by omega) (by simp at hnfT; omega)
          (Or.inr (by simp at hnfT; omega)) x hc1 ht1
      · have hbl := hnum_occ_bounds i l hi hl
        exact hinner_disj _ _ _ _ _ _ (by omega) (by simp at hnfT; omega)
          (Or.inr (by simp at hnfT; omega)) x hc2 ht1
      · have hv := hlit_var i j hi hjl
        have hnT := hnum_var (lit i j).1 hv true
        have hltE := he_lt (lit i j).1 hv
        exact hinner_disj _ _ _ _ _ _ (by simp at hnT; omega) (by simp at hnfT; omega)
          (Or.inr (by simp at hnT hnfT; omega)) x hc3 ht1
      · have := hinner_ge _ _ _ _ ht1; omega
      · have hv := hlit_var i j hi hjl
        have hnT := hnum_var (lit i j).1 hv true
        have hltE := he_lt (lit i j).1 hv
        have := hinner_ge _ _ _ _ ht1; simp at hnT; omega
    · -- ht2: inner (2E, 3E+2)
      rcases hxc with hc1 | ⟨l, hl, _, hc2⟩ | ⟨hjl, _, hc3⟩ | ⟨_, rfl⟩ | ⟨hjl, _, rfl⟩
      · exact hinner_disj _ _ _ _ _ _ (by omega) (by omega)
          (Or.inr (by omega)) x hc1 ht2
      · have hbl := hnum_occ_bounds i l hi hl
        exact hinner_disj _ _ _ _ _ _ (by omega) (by omega)
          (Or.inr (by omega)) x hc2 ht2
      · have hv := hlit_var i j hi hjl
        have hnT := hnum_var (lit i j).1 hv true
        have hltE := he_lt (lit i j).1 hv
        exact hinner_disj _ _ _ _ _ _ (by simp at hnT; omega) (by omega)
          (Or.inr (by simp at hnT; omega)) x hc3 ht2
      · have := hinner_ge _ _ _ _ ht2; omega
      · have hv := hlit_var i j hi hjl
        have hnT := hnum_var (lit i j).1 hv true
        have hltE := he_lt (lit i j).1 hv
        have := hinner_ge _ _ _ _ ht2; simp at hnT; omega
    · -- x = 2E + 1
      rcases hxc with hc1 | ⟨_, _, _, hc2⟩ | ⟨_, _, hc3⟩ | ⟨_, heq⟩ | ⟨hjl, _, heq⟩
      · have := hinner_ge _ _ _ _ hc1; simp at hnfT; omega
      · have := hinner_ge _ _ _ _ hc2; simp at hnfT; omega
      · have := hinner_ge _ _ _ _ hc3; simp at hnfT; omega
      · simp at hnfT; omega
      · have hv := hlit_var i j hi hjl
        have hnT := hnum_var (lit i j).1 hv true
        have hltE := he_lt (lit i j).1 hv
        simp at hnT hnfT; omega
    · -- x = 3E + 2
      rcases hxc with hc1 | ⟨_, _, _, hc2⟩ | ⟨_, _, hc3⟩ | ⟨_, heq⟩ | ⟨hjl, _, heq⟩
      · have := hinner_ge _ _ _ _ hc1; omega
      · have := hinner_ge _ _ _ _ hc2; omega
      · have := hinner_ge _ _ _ _ hc3; omega
      · omega
      · have hv := hlit_var i j hi hjl
        have hnT := hnum_var (lit i j).1 hv true
        have hltE := he_lt (lit i j).1 hv
        simp at hnT; omega
  -- Combine Nodup and membership
  refine ⟨?_, ?_⟩
  · rw [hTL_eq]
    exact nodup_append_of_disjoint hmain_nodup htail_nodup hmain_tail_disj
  · intro x
    rw [hTL_eq]
    simp only [List.mem_append]
    constructor
    · rintro (hxm | hxt)
      · dsimp only [mainList] at hxm
        simp only [List.mem_flatMap, List.mem_range] at hxm
        rcases hxm with ⟨i, hi, j, hj, hxc⟩
        have hj' : j ≤ (φ.getD i []).length := by omega
        have hb_occ := hnum_occ_bounds i j hi hj'
        have hb_lit := hnum_lit_lt i j hi hj'
        rw [hcell_mem] at hxc
        rcases hxc with hc1 | ⟨l, hl, hjl, hc2⟩ | ⟨hjl, _, hc3⟩ | ⟨hne, rfl⟩ | ⟨hjl, _, rfl⟩
        · right
          rw [hinner_mem] at hc1
          rcases hc1 with ⟨t, ht, rfl, hpar⟩
          refine ⟨⟨num (Sum.inl (lit i j)), by omega⟩, ⟨num (Sum.inr (i, j)), by omega⟩,
            by show num (Sum.inl (lit i j)) < num (Sum.inr (i, j)); omega, ?_,
            t, ht, rfl, ?_⟩
          · rw [hH_dir _ _ (by show num (Sum.inl (lit i j)) < num (Sum.inr (i, j)); omega)]
            exact Or.inl ⟨i, hi, j, hj', rfl, rfl⟩
          · rw [hTH_lit i j hi hj']; exact hpar
        · right
          have hbl := hnum_occ_bounds i l hi hl
          rw [hinner_mem] at hc2
          rcases hc2 with ⟨t, ht, rfl, hpar⟩
          have hlt_occ : num (Sum.inr (i, j)) < num (Sum.inr (i, l)) := by
            rw [hnum_occ i j hi hj', hnum_occ i l hi hl]; omega
          refine ⟨⟨num (Sum.inr (i, j)), by omega⟩, ⟨num (Sum.inr (i, l)), by omega⟩,
            hlt_occ, ?_, t, ht, rfl, ?_⟩
          · rw [hH_dir _ _ hlt_occ]
            exact Or.inr (Or.inl ⟨i, hi, j, hj', l, hl, hjl, rfl, rfl⟩)
          · rw [hTH_occ i j hi hj']
            simpa [decide_eq_true_eq] using hpar
        · right
          have hv := hlit_var i j hi hjl
          have hnF := hnum_var (lit i j).1 hv false
          have hnT := hnum_var (lit i j).1 hv true
          have hltE := he_lt (lit i j).1 hv
          rw [hinner_mem] at hc3
          rcases hc3 with ⟨t, ht, rfl, hpar⟩
          have hlt_v : num (Sum.inl ((lit i j).1, false)) < num (Sum.inl ((lit i j).1, true)) := by
            simp at hnF hnT; omega
          refine ⟨⟨num (Sum.inl ((lit i j).1, false)), by simp at hnF; omega⟩,
            ⟨num (Sum.inl ((lit i j).1, true)), by simp at hnT; omega⟩,
            hlt_v, ?_, t, ht, rfl, ?_⟩
          · rw [hH_dir _ _ hlt_v]
            exact Or.inr (Or.inr (Or.inl ⟨(lit i j).1, hv, rfl, rfl⟩))
          · rw [hTH_var (lit i j).1 hv false]; exact hpar
        · left
          exact (hTH_occ i j hi hj').mpr hne
        · left
          have hv := hlit_var i j hi hjl
          exact (hTH_var (lit i j).1 hv true).mpr rfl
      · dsimp only [tailList] at hxt
        have hnfF := hnum_fresh false
        have hnfT := hnum_fresh true
        have hnl := hnum_last
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hxt
        rcases hxt with (ht1 | ht2) | (rfl | rfl)
        · right
          rw [hinner_mem] at ht1
          rcases ht1 with ⟨t, ht, rfl, hpar⟩
          have hlt_f : num (Sum.inl (fresh φ, false)) < num (Sum.inl (fresh φ, true)) := by
            simp at hnfF hnfT; omega
          refine ⟨⟨num (Sum.inl (fresh φ, false)), by simp at hnfF; omega⟩,
            ⟨num (Sum.inl (fresh φ, true)), by simp at hnfT; omega⟩,
            hlt_f, ?_, t, ht, rfl, ?_⟩
          · rw [hH_dir _ _ hlt_f]
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
          · rw [hTH_fresh false]; exact hpar
        · right
          rw [hinner_mem] at ht2
          rcases ht2 with ⟨t, ht, rfl, hpar⟩
          have hlt_fl : num (Sum.inl (fresh φ, false)) < num (Sum.inr (φ.length, 0)) := by
            simp at hnfF; omega
          refine ⟨⟨num (Sum.inl (fresh φ, false)), by simp at hnfF; omega⟩,
            ⟨num (Sum.inr (φ.length, 0)), by omega⟩,
            hlt_fl, ?_, t, ht, rfl, ?_⟩
          · rw [hH_dir _ _ hlt_fl]
            exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
          · rw [hTH_fresh false]; exact hpar
        · left; exact (hTH_fresh true).mpr rfl
        · left; exact hTH_last
    · rintro (hTx | ⟨u, v, huv, hadj, t, ht, rfl, hpar⟩)
      · rw [hTH] at hTx
        rcases hTx with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
        · obtain ⟨i, hi, j, hjl, hoff_eq, hlz⟩ := hvar_unique_ij z hz
          left
          dsimp only [mainList]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          rw [hcell_mem]
          right; right; right; right
          refine ⟨hjl, by rw [hlz]; exact hoff_eq, ?_⟩
          rw [hlz, hnum_var z hz true]; simp
        · right
          dsimp only [tailList]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          right; left
          rw [hnum_fresh true]; simp
        · left
          dsimp only [mainList]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          rw [hcell_mem]
          right; right; right; left
          exact ⟨hne, (hnum_occ i j hi hj).symm⟩
        · right
          dsimp only [tailList]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          right; right
          exact hnum_last.symm
      · rw [hH_dir u v huv] at hadj
        rcases hadj with ⟨i, hi, j, hj, hu, hv⟩ | ⟨i, hi, j, hj, l, hl, hjl, hu, hv⟩ |
            ⟨z, hz, hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
        · left
          dsimp only [mainList]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          rw [hcell_mem]
          left
          rw [hinner_mem]
          refine ⟨t, ht, by rw [hu, hv], ?_⟩
          rw [hu, hTH_lit i j hi hj] at hpar
          exact hpar
        · left
          dsimp only [mainList]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          rw [hcell_mem]
          right; left
          refine ⟨l, hl, hjl, ?_⟩
          rw [hinner_mem]
          refine ⟨t, ht, by rw [hu, hv], ?_⟩
          rw [hu, hTH_occ i j hi hj] at hpar
          simpa [decide_eq_true_eq] using hpar
        · obtain ⟨i, hi, j, hjl, hoff_eq, hlz⟩ := hvar_unique_ij z hz
          left
          dsimp only [mainList]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i, hi, j, by omega, ?_⟩
          rw [hcell_mem]
          right; right; left
          refine ⟨hjl, by rw [hlz]; exact hoff_eq, ?_⟩
          rw [hlz, hinner_mem]
          refine ⟨t, ht, by rw [hu, hv], ?_⟩
          rw [hu, hTH_var z hz false] at hpar
          exact hpar
        · right
          dsimp only [tailList]
          simp only [List.mem_append]
          left; left
          rw [hinner_mem]
          refine ⟨t, ht, by rw [hu, hv], ?_⟩
          rw [hu, hTH_fresh false] at hpar
          exact hpar
        · right
          dsimp only [tailList]
          simp only [List.mem_append]
          left; right
          rw [hinner_mem]
          refine ⟨t, ht, by rw [hu, hv], ?_⟩
          rw [hu, hTH_fresh false] at hpar
          exact hpar
