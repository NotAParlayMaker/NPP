import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

lemma PEqualNP.Outside.L_meta_497_dm {m a b c d : ℕ} (hb : b < m) (hd : d < m)
    (h : m * a + b = m * c + d) : a = c ∧ b = d := by
  have hm : 0 < m := by omega
  have h1 : (m * a + b) / m = a := by
    rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hb, add_zero]
  have h2 : (m * c + d) / m = c := by
    rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hd, add_zero]
  have h3 : (m * a + b) % m = b := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have h4 : (m * c + d) % m = d := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
  exact ⟨by rw [← h1, ← h2, h], by rw [← h3, ← h4, h]⟩

lemma PEqualNP.Outside.L_meta_497_pd {N k u v t u' v' t' : ℕ} (hv : v < N) (hv' : v' < N)
    (ht : t < 2 * k) (ht' : t' < 2 * k)
    (h : N + 2 * k * (u * N + v) + t = N + 2 * k * (u' * N + v') + t') :
    u = u' ∧ v = v' ∧ t = t' := by
  rw [add_assoc, add_assoc] at h
  obtain ⟨h2, h3⟩ := PEqualNP.Outside.L_meta_497_dm ht ht' (Nat.add_left_cancel h)
  have h4 : N * u + v = N * u' + v' := by
    rw [mul_comm N u, mul_comm N u']
    exact h2
  obtain ⟨h5, h6⟩ := PEqualNP.Outside.L_meta_497_dm hv hv' h4
  exact ⟨h5, h6, h3⟩

def PEqualNP.Outside.L_meta_497_key (N k E x : ℕ) : ℕ :=
  if x < N then (if x < 2 * (E + 1) then x / 2 else x - 2 * (E + 1))
  else if 2 * (E + 1) ≤ (x - N) / (2 * k) / N then (x - N) / (2 * k) / N - 2 * (E + 1)
  else if 2 * (E + 1) ≤ (x - N) / (2 * k) % N then (x - N) / (2 * k) % N - 2 * (E + 1)
  else (x - N) / (2 * k) / N / 2

lemma PEqualNP.Outside.L_meta_497_keyP {N k E u v t : ℕ} (hv : v < N) (ht : t < 2 * k) :
    PEqualNP.Outside.L_meta_497_key N k E (N + 2 * k * (u * N + v) + t) =
      if 2 * (E + 1) ≤ u then u - 2 * (E + 1)
      else if 2 * (E + 1) ≤ v then v - 2 * (E + 1) else u / 2 := by
  have hk : 0 < 2 * k := by omega
  have hN : 0 < N := by omega
  have e1 : (N + 2 * k * (u * N + v) + t - N) / (2 * k) = u * N + v := by
    rw [show N + 2 * k * (u * N + v) + t - N = 2 * k * (u * N + v) + t by omega,
      Nat.mul_add_div hk, Nat.div_eq_of_lt ht, add_zero]
  have e2 : (u * N + v) / N = u := by
    rw [mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hv, add_zero]
  have e3 : (u * N + v) % N = v := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  have e0 : ¬ (N + 2 * k * (u * N + v) + t < N) := by omega
  unfold PEqualNP.Outside.L_meta_497_key
  simp only [e0, ↓reduceIte, e1, e2, e3]

def PEqualNP.Outside.L_meta_497_S (φ : CNF) (i : ℕ) : ℕ :=
  ((φ.take i).map (fun c => c.length + 1)).sum

lemma PEqualNP.Outside.L_meta_497_S_zero (φ : CNF) : PEqualNP.Outside.L_meta_497_S φ 0 = 0 := by
  simp [PEqualNP.Outside.L_meta_497_S]

lemma PEqualNP.Outside.L_meta_497_S_cons (c : Clause) (φ : CNF) (i : ℕ) :
    PEqualNP.Outside.L_meta_497_S (c :: φ) (i + 1) =
      c.length + 1 + PEqualNP.Outside.L_meta_497_S φ i := by
  simp [PEqualNP.Outside.L_meta_497_S]

lemma PEqualNP.Outside.L_meta_497_S_succ (φ : CNF) (i : ℕ) :
    PEqualNP.Outside.L_meta_497_S φ (i + 1) = PEqualNP.Outside.L_meta_497_S φ i +
      (if i < φ.length then (φ.getD i []).length + 1 else 0) := by
  induction φ generalizing i with
  | nil => simp [PEqualNP.Outside.L_meta_497_S]
  | cons c φ ih =>
    cases i with
    | zero => simp [PEqualNP.Outside.L_meta_497_S]
    | succ i =>
      rw [PEqualNP.Outside.L_meta_497_S_cons, PEqualNP.Outside.L_meta_497_S_cons, ih]
      simp only [List.length_cons, List.getD_cons_succ, Nat.add_lt_add_iff_right]
      omega

lemma PEqualNP.Outside.L_meta_497_S_mono (φ : CNF) {a b : ℕ} (h : a ≤ b) :
    PEqualNP.Outside.L_meta_497_S φ a ≤ PEqualNP.Outside.L_meta_497_S φ b := by
  refine monotone_nat_of_le_succ (fun i => ?_) h
  rw [PEqualNP.Outside.L_meta_497_S_succ]
  omega

lemma PEqualNP.Outside.L_meta_497_S_len (φ : CNF) :
    PEqualNP.Outside.L_meta_497_S φ φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [PEqualNP.Outside.L_meta_497_S]
  | cons c φ ih =>
    rw [List.length_cons, PEqualNP.Outside.L_meta_497_S_cons]
    have h1 : c.length ≤ (c.flatMap encodeLiteral).length := by
      clear ih
      induction c with
      | nil => simp
      | cons l c ih2 =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        simp only [encodeLiteral, List.length_append, List.length_cons] at ih2 ⊢
        omega
    have h2 : (encodeCNF (c :: φ)).length =
        (c.flatMap encodeLiteral).length + 2 + (encodeCNF φ).length := by
      simp [encodeCNF, encodeClause]
      omega
    omega

lemma PEqualNP.Outside.L_meta_497_flat (φ : CNF) : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length,
    (φ.flatMap (fun c => c.map some ++ [none]))[PEqualNP.Outside.L_meta_497_S φ i + j]? =
      ((φ.getD i []).map some ++ [none])[j]? := by
  induction φ with
  | nil => intro i hi; simp at hi
  | cons c φ ih =>
    intro i hi j hj
    cases i with
    | zero =>
      rw [PEqualNP.Outside.L_meta_497_S_zero, zero_add, List.flatMap_cons,
        List.getElem?_append_left (by simp at hj ⊢; omega)]
      simp
    | succ i =>
      rw [PEqualNP.Outside.L_meta_497_S_cons, List.flatMap_cons,
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simp only [List.getD_cons_succ] at hj ⊢
      rw [← ih i hi j hj]
      congr 1
      simp
      omega

lemma PEqualNP.Outside.L_meta_497_flat_len (φ : CNF) :
    (φ.flatMap (fun c => c.map some ++ [none])).length = PEqualNP.Outside.L_meta_497_S φ φ.length := by
  induction φ with
  | nil => simp [PEqualNP.Outside.L_meta_497_S]
  | cons c φ ih =>
    rw [List.length_cons, PEqualNP.Outside.L_meta_497_S_cons, List.flatMap_cons, List.length_append, ih]
    simp

lemma PEqualNP.Outside.L_meta_497_split (φ : CNF) : ∀ p < PEqualNP.Outside.L_meta_497_S φ φ.length,
    ∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, p = PEqualNP.Outside.L_meta_497_S φ i + j := by
  induction φ with
  | nil => intro p hp; simp [PEqualNP.Outside.L_meta_497_S] at hp
  | cons c φ ih =>
    intro p hp
    rw [List.length_cons, PEqualNP.Outside.L_meta_497_S_cons] at hp
    by_cases hc : p < c.length + 1
    · exact ⟨0, by simp, p, by simp; omega, by rw [PEqualNP.Outside.L_meta_497_S_zero]; omega⟩
    · obtain ⟨i, hi, j, hj, hp'⟩ := ih (p - (c.length + 1)) (by omega)
      refine ⟨i + 1, by simp; omega, j, by simpa using hj, ?_⟩
      rw [PEqualNP.Outside.L_meta_497_S_cons]
      omega

lemma PEqualNP.Outside.L_meta_497_ms {C : List Literal} {j : ℕ} {l0 : Literal}
    (h : (C.map some ++ [none])[j]? = some (some l0)) : j < C.length ∧ C[j]? = some l0 := by
  by_cases hj : j < C.length
  · rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map] at h
    refine ⟨hj, ?_⟩
    simpa using h
  · rw [List.getElem?_append_right (by simp; omega)] at h
    exfalso
    rcases hk : j - (C.map some).length with _ | m
    · rw [hk] at h
      simp at h
    · rw [hk] at h
      simp at h

theorem PEqualNP.Outside.L_meta_497 : ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff hel hei hep num hnl hnf hno hnlast H hH f hf TH hTH lit hlit
    inner hinner TL hTL
  have hoffS : ∀ i, off i = PEqualNP.Outside.L_meta_497_S φ i := fun i => hoff i
  have hSE : PEqualNP.Outside.L_meta_497_S φ φ.length ≤ E :=
    hE ▸ PEqualNP.Outside.L_meta_497_S_len φ
  have hFV : ∀ z ∈ vars φ, z < fresh φ := fun z hz =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hz)
  have hlt : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length, off i + j < E := by
    intro i hi j hj
    have h1 := PEqualNP.Outside.L_meta_497_S_succ φ i
    simp only [hi, ↓reduceIte] at h1
    have h2 := PEqualNP.Outside.L_meta_497_S_mono φ (show i + 1 ≤ φ.length by omega)
    rw [hoffS]
    omega
  have hinj : ∀ i i' j j', i < φ.length → i' < φ.length → j ≤ (φ.getD i []).length →
      j' ≤ (φ.getD i' []).length → off i + j = off i' + j' → i = i' ∧ j = j' := by
    intro i i' j j' hi hi' hj hj' h
    rw [hoffS, hoffS] at h
    rcases lt_trichotomy i i' with c | c | c
    · exfalso
      have h1 := PEqualNP.Outside.L_meta_497_S_succ φ i
      simp only [hi, ↓reduceIte] at h1
      have h2 := PEqualNP.Outside.L_meta_497_S_mono φ (show i + 1 ≤ i' by omega)
      omega
    · subst c
      exact ⟨rfl, by omega⟩
    · exfalso
      have h1 := PEqualNP.Outside.L_meta_497_S_succ φ i'
      simp only [hi', ↓reduceIte] at h1
      have h2 := PEqualNP.Outside.L_meta_497_S_mono φ (show i' + 1 ≤ i by omega)
      omega
  have hlit1 : ∀ i j, j < (φ.getD i []).length → (φ.getD i [])[j]? = some (lit i j) := by
    intro i j hj
    rw [hlit]
    generalize φ.getD i [] = C at hj ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  have hlit2 : ∀ i, lit i (φ.getD i []).length = (fresh φ, true) := by
    intro i
    rw [hlit]
    generalize φ.getD i [] = C
    simp [List.getD_eq_getElem?_getD]
  have hvar : ∀ i < φ.length, ∀ j < (φ.getD i []).length, (lit i j).1 ∈ vars φ := by
    intro i hi j hj
    simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
    refine ⟨φ.getD i [], ?_, lit i j, List.mem_of_getElem? (hlit1 i j hj), rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hTHl : ∀ z ∈ vars φ, ∀ b : Bool, TH (2 * e z + (if b then 1 else 0)) ↔ b = true := by
    intro z hz b
    have := hel z hz
    rw [hTH]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, iff_false]
      rintro (⟨z', -, h⟩ | h | ⟨i, -, j, -, -, h⟩ | h) <;> omega
    · simp only [↓reduceIte, iff_true]
      exact Or.inl ⟨z, hz, rfl⟩
  have hTHf : ∀ b : Bool, TH (2 * E + (if b then 1 else 0)) ↔ b = true := by
    intro b
    rw [hTH]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, iff_false]
      rintro (⟨z', hz', h⟩ | h | ⟨i, -, j, -, -, h⟩ | h)
      · have := hel z' hz'
        omega
      all_goals omega
    · simp only [↓reduceIte, iff_true]
      simp
  have hTHo : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length,
      TH (2 * (E + 1) + off i + j) ↔ j ≠ f i := by
    intro i hi j hj
    have := hlt i hi j hj
    rw [hTH]
    constructor
    · rintro (⟨z', hz', h⟩ | h | ⟨i', hi', j', hj', hne, h⟩ | h)
      · have := hel z' hz'
        omega
      · omega
      · obtain ⟨rfl, rfl⟩ := hinj i i' j j' hi hi' hj hj' (by omega)
        exact hne
      · omega
    · intro hne
      exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hne, rfl⟩))
  have hNL : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length,
      num (Sum.inl (lit i j)) < 2 * (E + 1) ∧
        (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2 = true) := by
    intro i hi j hj
    rcases Nat.lt_or_ge j (φ.getD i []).length with h | h
    · have hz := hvar i hi j h
      have e1 : num (Sum.inl (lit i j)) =
          2 * e (lit i j).1 + (if (lit i j).2 then 1 else 0) := by
        have := hnl _ hz (lit i j).2
        rwa [Prod.mk.eta] at this
      rw [e1, hTHl _ hz]
      have := hel _ hz
      exact ⟨by split <;> omega, Iff.rfl⟩
    · have hj' : j = (φ.getD i []).length := by omega
      rw [hj', hlit2, hnf, hTHf]
      refine ⟨?_, ?_⟩ <;> simp <;> omega
  have hmi : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t < 2 * k, (t % 2 = 1 ↔ b = true) ∧ x = N + 2 * k * (u * N + v) + t := by
    intro u v b x
    rw [hinner]
    simp only [List.mem_map, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨t, ⟨ht, hb⟩, rfl⟩
      refine ⟨t, ht, ?_, rfl⟩
      cases b <;> simp at hb ⊢ <;> omega
    · rintro ⟨t, ht, hb, rfl⟩
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      cases b <;> simp at hb ⊢ <;> omega
  have hcl1 : ∀ i < φ.length,
      clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
    intro i hi
    simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD, List.getElem?_append, hi]
  have hcl2 : clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
    simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD, List.getElem?_append]
  have hcl3 : ∀ i, φ.length < i → clauseAt (cvcFormula φ) i = [] := by
    intro i hi
    have h1 : ¬ i < φ.length := by omega
    have h2 : 1 ≤ i - φ.length := by omega
    simp [clauseAt, cvcFormula, List.getD_eq_getElem?_getD, List.getElem?_append, h1]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
  have hvc : ∀ z, z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
    intro z
    simp only [vars, cvcFormula, List.mem_toFinset, List.mem_flatMap, List.mem_map,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨a, (⟨c, hc, rfl⟩ | rfl), l, hl, rfl⟩
      · rw [List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact Or.inl ⟨c, hc, l, hl, rfl⟩
        · exact Or.inr rfl
      · rw [List.mem_singleton] at hl
        subst hl
        exact Or.inr rfl
    · rintro (⟨c, hc, l, hl, rfl⟩ | rfl)
      · exact ⟨c ++ [(fresh φ, true)], Or.inl ⟨c, hc, rfl⟩, l, List.mem_append_left _ hl, rfl⟩
      · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), List.mem_singleton_self _, rfl⟩
  have eA : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length,
      (cvcGraph φ).Adj (Sum.inl (lit i j)) (Sum.inr (i, j)) := by
    intro i hi j hj
    show (clauseAt (cvcFormula φ) i)[j]? = some (lit i j)
    rw [hcl1 i hi, hlit]
    generalize φ.getD i [] = C at hj ⊢
    obtain ⟨x, hx⟩ : ∃ x, (C ++ [(fresh φ, true)])[j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by simp; omega)⟩
    rw [List.getD_eq_getElem?_getD, hx]
    rfl
  have eB : ∀ i < φ.length, ∀ j l, j < l → l ≤ (φ.getD i []).length →
      (cvcGraph φ).Adj (Sum.inr (i, j)) (Sum.inr (i, l)) := by
    intro i hi j l hjl hl
    show i = i ∧ j ≠ l ∧ j < (clauseAt (cvcFormula φ) i).length ∧
      l < (clauseAt (cvcFormula φ) i).length
    rw [hcl1 i hi]
    simp only [List.length_append, List.length_cons, List.length_nil]
    exact ⟨trivial, by omega, by omega, by omega⟩
  have eC : ∀ z, z ∈ vars (cvcFormula φ) →
      (cvcGraph φ).Adj (Sum.inl (z, false)) (Sum.inl (z, true)) := by
    intro z hz
    exact ⟨rfl, Bool.false_ne_true, hz⟩
  have eE : (cvcGraph φ).Adj (Sum.inl (fresh φ, false)) (Sum.inr (φ.length, 0)) := by
    show (clauseAt (cvcFormula φ) φ.length)[0]? = some (fresh φ, false)
    rw [hcl2]
    rfl
  obtain ⟨blk, hblk, hTL2⟩ : ∃ blk : ℕ → ℕ → List ℕ, (∀ i j, blk i j =
      inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
          else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else [])) ∧
      TL = (List.range φ.length).flatMap (fun i =>
          (List.range ((φ.getD i []).length + 1)).flatMap (fun j => blk i j)) ++
        (inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++
          inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++
          [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]) :=
    ⟨_, fun _ _ => rfl, hTL⟩
  clear hTL
  have hnF0 : num (Sum.inl (fresh φ, false)) = 2 * E := by
    rw [hnf]
    simp
  have hnF1 : num (Sum.inl (fresh φ, true)) = 2 * E + 1 := by
    rw [hnf]
    simp
  rw [hnF0, hnF1, hnlast] at hTL2
  have hbm : ∀ i j x, x ∈ blk i j ↔
      (∃ t < 2 * k, (t % 2 = 1 ↔ (lit i j).2 = true) ∧
          x = N + 2 * k * (num (Sum.inl (lit i j)) * N + num (Sum.inr (i, j))) + t) ∨
      (∃ l, (l < (φ.getD i []).length + 1 ∧ j < l) ∧ ∃ t < 2 * k, (t % 2 = 1 ↔ j ≠ f i) ∧
          x = N + 2 * k * (num (Sum.inr (i, j)) * N + num (Sum.inr (i, l))) + t) ∨
      ((j < (φ.getD i []).length ∧ off i + j = e (lit i j).1) ∧ ∃ t < 2 * k,
          (t % 2 = 1 ↔ False) ∧ x = N + 2 * k * (num (Sum.inl ((lit i j).1, false)) * N +
            num (Sum.inl ((lit i j).1, true))) + t) ∨
      (j ≠ f i ∧ x = num (Sum.inr (i, j))) ∨
      ((j < (φ.getD i []).length ∧ off i + j = e (lit i j).1) ∧
          x = num (Sum.inl ((lit i j).1, true))) := by
    intro i j x
    rw [hblk]
    simp only [List.mem_append, hmi, List.mem_flatMap, List.mem_filter, List.mem_range,
      decide_eq_true_eq, List.mem_ite_nil_right, List.mem_singleton, Bool.false_eq_true, or_assoc]
  have htm : ∀ x, x ∈ (inner (2 * E) (2 * E + 1) false ++ inner (2 * E) (3 * E + 2) false ++
      [2 * E + 1, 3 * E + 2]) ↔
      (∃ t < 2 * k, (t % 2 = 1 ↔ False) ∧ x = N + 2 * k * (2 * E * N + (2 * E + 1)) + t) ∨
      (∃ t < 2 * k, (t % 2 = 1 ↔ False) ∧ x = N + 2 * k * (2 * E * N + (3 * E + 2)) + t) ∨
      x = 2 * E + 1 ∨ x = 3 * E + 2 := by
    intro x
    simp only [List.mem_append, hmi, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      Bool.false_eq_true, or_assoc, or_false]
  have hn0 : ∀ z ∈ vars φ, num (Sum.inl (z, false)) = 2 * e z := fun z hz => by
    rw [hnl z hz]
    simp
  have hn1 : ∀ z ∈ vars φ, num (Sum.inl (z, true)) = 2 * e z + 1 := fun z hz => by
    rw [hnl z hz]
    simp
  have hTH0 : ∀ z ∈ vars φ, ¬ TH (2 * e z) := fun z hz h => by
    have := (hTHl z hz false).mp (by simpa using h)
    simp at this
  have hTH1 : ∀ z ∈ vars φ, TH (2 * e z + 1) := fun z hz => by
    have := (hTHl z hz true).mpr rfl
    simpa using this
  have hTHE0 : ¬ TH (2 * E) := fun h => by
    have := (hTHf false).mp (by simpa using h)
    simp at this
  have hTHE1 : TH (2 * E + 1) := (hTH _).mpr (Or.inr (Or.inl rfl))
  have hTHE2 : TH (3 * E + 2) := (hTH _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hpos : ∀ z ∈ vars φ, ∃ i < φ.length, ∃ j < (φ.getD i []).length,
      off i + j = e z ∧ (lit i j).1 = z := by
    intro z hz
    obtain ⟨l0, hl0, hl0z⟩ := hep z hz
    have hb : e z < PEqualNP.Outside.L_meta_497_S φ φ.length := by
      rw [← PEqualNP.Outside.L_meta_497_flat_len]
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hl0
      simp at hl0
    obtain ⟨i, hi, j, hj, hp⟩ := PEqualNP.Outside.L_meta_497_split φ (e z) hb
    have h2 := PEqualNP.Outside.L_meta_497_flat φ i hi j hj
    rw [← hp, hl0] at h2
    obtain ⟨hjL, hC⟩ := PEqualNP.Outside.L_meta_497_ms h2.symm
    rw [hlit1 i j hjL] at hC
    refine ⟨i, hi, j, hjL, by rw [hoffS]; omega, ?_⟩
    rw [Option.some_inj.mp hC, hl0z]
  have hinnd : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner]
    exact (List.nodup_range.filter _).map (fun a b h => Nat.add_left_cancel h)
  have mkE : ∀ (a b : Vertex) (ua vb t : ℕ), (cvcGraph φ).Adj a b → num a = ua → num b = vb →
      ua < vb → vb < N → t < 2 * k → (t % 2 = 1 ↔ TH ua) →
      ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t' < 2 * k,
        N + 2 * k * (ua * N + vb) + t = N + 2 * k * (u.val * N + v.val) + t' ∧
          (t' % 2 = 1 ↔ TH u.val) := by
    intro a b ua vb t hab ha hb huv hvN ht hpar
    exact ⟨⟨ua, by omega⟩, ⟨vb, hvN⟩, Fin.mk_lt_mk.mpr huv,
      (hH _ _).mpr ⟨a, b, hab, ha, hb⟩, t, ht, rfl, hpar⟩
  subst hTL2
  refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hkey : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length, ∀ x ∈ blk i j,
        PEqualNP.Outside.L_meta_497_key N k E x = off i + j := by
      intro i hi j hj x hx
      have hNOj := hno i j hi hj
      have hltj := hlt i hi j hj
      rw [hbm] at hx
      rcases hx with ⟨t, ht, -, rfl⟩ | ⟨l, ⟨hl, hjl⟩, t, ht, -, rfl⟩ |
          ⟨⟨hjL, hc⟩, t, ht, -, rfl⟩ | ⟨-, rfl⟩ | ⟨⟨hjL, hc⟩, rfl⟩
      · have := (hNL i hi j hj).1
        rw [PEqualNP.Outside.L_meta_497_keyP (by omega) ht]
        split_ifs <;> omega
      · have hNOl := hno i l hi (by omega)
        have hltl := hlt i hi l (by omega)
        rw [PEqualNP.Outside.L_meta_497_keyP (by omega) ht]
        split_ifs <;> omega
      · have hz := hvar i hi j hjL
        have := hel _ hz
        rw [hn0 _ hz, hn1 _ hz, PEqualNP.Outside.L_meta_497_keyP (by omega) ht]
        split_ifs <;> omega
      · unfold PEqualNP.Outside.L_meta_497_key
        split_ifs <;> omega
      · have hz := hvar i hi j hjL
        have := hel _ hz
        rw [hn1 _ hz]
        unfold PEqualNP.Outside.L_meta_497_key
        split_ifs <;> omega
    have hkeyT : ∀ x ∈ (inner (2 * E) (2 * E + 1) false ++ inner (2 * E) (3 * E + 2) false ++
        [2 * E + 1, 3 * E + 2]), PEqualNP.Outside.L_meta_497_key N k E x = E := by
      intro x hx
      rw [htm] at hx
      rcases hx with ⟨t, ht, -, rfl⟩ | ⟨t, ht, -, rfl⟩ | rfl | rfl
      · rw [PEqualNP.Outside.L_meta_497_keyP (by omega) ht]
        split_ifs <;> omega
      · rw [PEqualNP.Outside.L_meta_497_keyP (by omega) ht]
        split_ifs <;> omega
      · unfold PEqualNP.Outside.L_meta_497_key
        split_ifs <;> omega
      · unfold PEqualNP.Outside.L_meta_497_key
        split_ifs <;> omega
    have hblkND : ∀ i < φ.length, ∀ j ≤ (φ.getD i []).length, (blk i j).Nodup := by
      intro i hi j hj
      have hNOj := hno i j hi hj
      have hltj := hlt i hi j hj
      have hNLj := (hNL i hi j hj).1
      have hNOl : ∀ l ≤ (φ.getD i []).length,
          num (Sum.inr (i, l)) = 2 * (E + 1) + off i + l ∧ off i + l < E :=
        fun l hl => ⟨hno i l hi hl, hlt i hi l hl⟩
      rw [hblk]
      refine List.Nodup.append (List.Nodup.append (List.Nodup.append
        (List.Nodup.append (hinnd _ _ _) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
      · refine List.nodup_flatMap.mpr ⟨fun l _ => hinnd _ _ _, ?_⟩
        refine (List.nodup_range.filter _).pairwise_of_forall_ne
          (fun l hl l' hl' hne x h1 h2 => ?_)
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl hl'
        rw [hmi] at h1 h2
        obtain ⟨t, ht, -, rfl⟩ := h1
        obtain ⟨t', ht', -, h⟩ := h2
        have a := hNOl l (by omega)
        have b := hNOl l' (by omega)
        obtain ⟨-, h2, -⟩ :=
          PEqualNP.Outside.L_meta_497_pd (by omega) (by omega) (by omega) (by omega) h
        omega
      · intro x h1 h2
        simp only [hmi, List.mem_flatMap, List.mem_filter, List.mem_range,
          decide_eq_true_eq] at h1 h2
        obtain ⟨t, ht, -, rfl⟩ := h1
        obtain ⟨l, ⟨hl, hjl⟩, t', ht', -, h⟩ := h2
        have b := hNOl l (by omega)
        obtain ⟨h3, -, -⟩ :=
          PEqualNP.Outside.L_meta_497_pd (by omega) (by omega) (by omega) (by omega) h
        omega
      · split <;> simp [hinnd]
      · intro x h1 h2
        split at h2
        · rename_i hc
          have hz := hvar i hi j hc.1
          have := hel _ hz
          rw [hmi, hn0 _ hz, hn1 _ hz] at h2
          obtain ⟨t', ht', -, rfl⟩ := h2
          simp only [List.mem_append, hmi, List.mem_flatMap, List.mem_filter, List.mem_range,
            decide_eq_true_eq] at h1
          rcases h1 with ⟨t, ht, -, h⟩ | ⟨l, ⟨hl, hjl⟩, t, ht, -, h⟩
          · obtain ⟨-, h3, -⟩ :=
              PEqualNP.Outside.L_meta_497_pd (by omega) (by omega) (by omega) (by omega) h
            omega
          · have b := hNOl l (by omega)
            obtain ⟨h3, -, -⟩ :=
              PEqualNP.Outside.L_meta_497_pd (by omega) (by omega) (by omega) (by omega) h
            omega
        · simp at h2
      · split <;> simp
      · intro x h1 h2
        split at h2
        · rw [List.mem_singleton] at h2
          subst h2
          simp only [List.mem_append, hmi, List.mem_flatMap, List.mem_filter, List.mem_range,
            decide_eq_true_eq, List.mem_ite_nil_right] at h1
          rcases h1 with (⟨t, ht, -, h⟩ | ⟨l, -, t, ht, -, h⟩) | ⟨-, t, ht, -, h⟩ <;> omega
        · simp at h2
      · split <;> simp
      · intro x h1 h2
        split at h2
        · rename_i hc
          have hz := hvar i hi j hc.1
          have := hel _ hz
          rw [List.mem_singleton, hn1 _ hz] at h2
          subst h2
          simp only [List.mem_append, hmi, List.mem_flatMap, List.mem_filter, List.mem_range,
            decide_eq_true_eq, List.mem_ite_nil_right, List.mem_singleton] at h1
          rcases h1 with ((⟨t, ht, -, h⟩ | ⟨l, -, t, ht, -, h⟩) | ⟨-, t, ht, -, h⟩) | ⟨-, h⟩ <;>
            omega
        · simp at h2
    refine List.Nodup.append ?_ ?_ ?_
    · refine List.nodup_flatMap.mpr ⟨fun i hi => ?_, ?_⟩
      · rw [List.mem_range] at hi
        refine List.nodup_flatMap.mpr
          ⟨fun j hj => hblkND i hi j (by rw [List.mem_range] at hj; omega), ?_⟩
        refine List.nodup_range.pairwise_of_forall_ne (fun j hj j' hj' hne x h1 h2 => hne ?_)
        rw [List.mem_range] at hj hj'
        have a := hkey i hi j (by omega) x h1
        have b := hkey i hi j' (by omega) x h2
        omega
      · refine List.nodup_range.pairwise_of_forall_ne (fun i hi i' hi' hne x h1 h2 => hne ?_)
        rw [List.mem_range] at hi hi'
        simp only [List.mem_flatMap, List.mem_range] at h1 h2
        obtain ⟨j, hj, h1⟩ := h1
        obtain ⟨j', hj', h2⟩ := h2
        have a := hkey i hi j (by omega) x h1
        have b := hkey i' hi' j' (by omega) x h2
        exact (hinj i i' j j' hi hi' (by omega) (by omega) (by omega)).1
    · refine List.Nodup.append (List.Nodup.append (hinnd _ _ _) (hinnd _ _ _) ?_) ?_ ?_
      · intro x h1 h2
        rw [hmi] at h1 h2
        obtain ⟨t, ht, -, rfl⟩ := h1
        obtain ⟨t', ht', -, h⟩ := h2
        obtain ⟨-, h3, -⟩ :=
          PEqualNP.Outside.L_meta_497_pd (by omega) (by omega) (by omega) (by omega) h
        omega
      · rw [List.nodup_cons]
        exact ⟨by simp only [List.mem_singleton]; omega, List.nodup_singleton _⟩
      · intro x h1 h2
        simp only [List.mem_append, hmi, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at h1 h2
        rcases h1 with ⟨t, ht, -, rfl⟩ | ⟨t, ht, -, rfl⟩ <;> rcases h2 with h | h <;> omega
    · intro x h1 h2
      simp only [List.mem_flatMap, List.mem_range] at h1
      obtain ⟨i, hi, j, hj, h1⟩ := h1
      have a := hkey i hi j (by omega) x h1
      have b := hkeyT x h2
      have := hlt i hi j (by omega)
      omega
  · rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_flatMap, List.mem_range] at hx
      obtain ⟨i, hi, j, hj, hx⟩ := hx
      have hj' : j ≤ (φ.getD i []).length := by omega
      have hNOj := hno i j hi hj'
      have hltj := hlt i hi j hj'
      rw [hbm] at hx
      rcases hx with ⟨t, ht, hpar, rfl⟩ | ⟨l, ⟨hl, hjl⟩, t, ht, hpar, rfl⟩ |
          ⟨⟨hjL, hc⟩, t, ht, hpar, rfl⟩ | ⟨hne, rfl⟩ | ⟨⟨hjL, hc⟩, rfl⟩
      · right
        have := (hNL i hi j hj').1
        exact mkE _ _ _ _ t (eA i hi j hj') rfl rfl (by omega) (by omega) ht
          (hpar.trans (hNL i hi j hj').2.symm)
      · right
        have hNOl := hno i l hi (by omega)
        have hltl := hlt i hi l (by omega)
        refine mkE _ _ _ _ t (eB i hi j l hjl (by omega)) rfl rfl (by omega) (by omega) ht ?_
        rw [hNOj, hTHo i hi j hj']
        exact hpar
      · right
        have hz := hvar i hi j hjL
        have := hel _ hz
        refine mkE _ _ _ _ t (eC _ ((hvc _).mpr (Or.inl hz))) rfl rfl
          (by rw [hn0 _ hz, hn1 _ hz]; omega) (by rw [hn1 _ hz]; omega) ht ?_
        rw [hn0 _ hz]
        exact hpar.trans (iff_false_intro (hTH0 _ hz)).symm
      · left
        rw [hNOj, hTHo i hi j hj']
        exact hne
      · left
        have hz := hvar i hi j hjL
        rw [hn1 _ hz]
        exact hTH1 _ hz
    · rw [htm] at hx
      rcases hx with ⟨t, ht, hpar, rfl⟩ | ⟨t, ht, hpar, rfl⟩ | rfl | rfl
      · right
        exact mkE _ _ _ _ t (eC _ ((hvc _).mpr (Or.inr rfl))) hnF0 hnF1 (by omega) (by omega) ht
          (hpar.trans (iff_false_intro hTHE0).symm)
      · right
        exact mkE _ _ _ _ t eE hnF0 hnlast (by omega) (by omega) ht
          (hpar.trans (iff_false_intro hTHE0).symm)
      · exact Or.inl hTHE1
      · exact Or.inl hTHE2
  · rcases hx with hT | ⟨u, v, huv, hadj, t, ht, rfl, hpar⟩
    · rw [hTH] at hT
      rcases hT with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
      · obtain ⟨i, hi, j, hjL, hc, hlz⟩ := hpos z hz
        apply List.mem_append_left
        simp only [List.mem_flatMap, List.mem_range]
        refine ⟨i, hi, j, by omega, ?_⟩
        rw [hbm]
        right; right; right; right
        exact ⟨⟨hjL, by rw [hlz]; exact hc⟩, by rw [hlz, hn1 _ hz]⟩
      · apply List.mem_append_right
        rw [htm]
        right; right; left; rfl
      · apply List.mem_append_left
        simp only [List.mem_flatMap, List.mem_range]
        refine ⟨i, hi, j, by omega, ?_⟩
        rw [hbm]
        right; right; right; left
        exact ⟨hne, (hno i j hi hj).symm⟩
      · apply List.mem_append_right
        rw [htm]
        right; right; right; rfl
    · obtain ⟨a, b, hab, ha, hb⟩ := (hH u v).mp hadj
      have huv' : u.val < v.val := huv
      have hvN := v.isLt
      rcases a with ⟨z1, b1⟩ | ⟨i1, j1⟩ <;> rcases b with ⟨z2, b2⟩ | ⟨i2, j2⟩
      · obtain ⟨rfl, hb12, hz⟩ : z1 = z2 ∧ b1 ≠ b2 ∧ z1 ∈ vars (cvcFormula φ) := hab
        rcases (hvc z1).mp hz with hz | rfl
        · cases b1 <;> cases b2
          · exact absurd rfl hb12
          · obtain ⟨i, hi, j, hjL, hc, hlz⟩ := hpos z1 hz
            apply List.mem_append_left
            simp only [List.mem_flatMap, List.mem_range]
            refine ⟨i, hi, j, by omega, ?_⟩
            rw [hbm]
            right; right; left
            refine ⟨⟨hjL, by rw [hlz]; exact hc⟩, t, ht, ?_, by rw [hlz, ha, hb]⟩
            rw [hn0 _ hz] at ha
            rw [← ha] at hpar
            exact hpar.trans (iff_false_intro (hTH0 _ hz))
          · rw [hn1 _ hz] at ha
            rw [hn0 _ hz] at hb
            omega
          · exact absurd rfl hb12
        · cases b1 <;> cases b2
          · exact absurd rfl hb12
          · apply List.mem_append_right
            rw [htm]
            left
            rw [hnF0] at ha
            rw [hnF1] at hb
            refine ⟨t, ht, ?_, by rw [← ha, ← hb]⟩
            rw [← ha] at hpar
            exact hpar.trans (iff_false_intro hTHE0)
          · rw [hnF1] at ha
            rw [hnF0] at hb
            omega
          · exact absurd rfl hb12
      · have hab' : (clauseAt (cvcFormula φ) i2)[j2]? = some (z1, b1) := hab
        rcases lt_trichotomy i2 φ.length with h2 | rfl | h2
        · rw [hcl1 i2 h2] at hab'
          have hj2 : j2 ≤ (φ.getD i2 []).length := by
            by_contra hc
            rw [List.getElem?_eq_none (by
              simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at hab'
            simp at hab'
          have hl : lit i2 j2 = (z1, b1) := by
            rw [hlit]
            simp only [List.getD_eq_getElem?_getD] at hab' ⊢
            rw [hab']
            rfl
          apply List.mem_append_left
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i2, h2, j2, by omega, ?_⟩
          rw [hbm]
          left
          refine ⟨t, ht, ?_, by rw [hl, ha, hb]⟩
          have := (hNL i2 h2 j2 hj2).2
          rw [hl, ha] at this
          rw [hl]
          exact hpar.trans this
        · rw [hcl2] at hab'
          have hj0 : j2 = 0 := by
            by_contra hc
            rw [List.getElem?_eq_none (by simp; omega)] at hab'
            simp at hab'
          subst hj0
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hab'
          obtain ⟨rfl, rfl⟩ := hab'
          apply List.mem_append_right
          rw [htm]
          right; left
          rw [hnF0] at ha
          rw [hnlast] at hb
          refine ⟨t, ht, ?_, by rw [← ha, ← hb]⟩
          rw [← ha] at hpar
          exact hpar.trans (iff_false_intro hTHE0)
        · rw [hcl3 i2 h2] at hab'
          simp at hab'
      · have hab' : (clauseAt (cvcFormula φ) i1)[j1]? = some (z2, b2) := hab
        exfalso
        rcases lt_trichotomy i1 φ.length with h1 | rfl | h1
        · rw [hcl1 i1 h1] at hab'
          have hj1 : j1 ≤ (φ.getD i1 []).length := by
            by_contra hc
            rw [List.getElem?_eq_none (by
              simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at hab'
            simp at hab'
          have hl : lit i1 j1 = (z2, b2) := by
            rw [hlit]
            simp only [List.getD_eq_getElem?_getD] at hab' ⊢
            rw [hab']
            rfl
          have h3 := (hNL i1 h1 j1 hj1).1
          rw [hl, hb] at h3
          rw [hno i1 j1 h1 hj1] at ha
          omega
        · rw [hcl2] at hab'
          have hj0 : j1 = 0 := by
            by_contra hc
            rw [List.getElem?_eq_none (by simp; omega)] at hab'
            simp at hab'
          subst hj0
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hab'
          obtain ⟨rfl, rfl⟩ := hab'
          rw [hnlast] at ha
          rw [hnF0] at hb
          omega
        · rw [hcl3 i1 h1] at hab'
          simp at hab'
      · obtain ⟨h12, hne, hj1, hj2⟩ : i1 = i2 ∧ j1 ≠ j2 ∧
            j1 < (clauseAt (cvcFormula φ) i1).length ∧
            j2 < (clauseAt (cvcFormula φ) i1).length := hab
        rw [← h12] at hb
        rcases lt_trichotomy i1 φ.length with h1 | rfl | h1
        · rw [hcl1 i1 h1] at hj1 hj2
          simp only [List.length_append, List.length_cons, List.length_nil] at hj1 hj2
          have e1 := hno i1 j1 h1 (by omega)
          have e2 := hno i1 j2 h1 (by omega)
          have hjl : j1 < j2 := by omega
          apply List.mem_append_left
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨i1, h1, j1, by omega, ?_⟩
          rw [hbm]
          right; left
          refine ⟨j2, ⟨by omega, hjl⟩, t, ht, ?_, by rw [ha, hb]⟩
          rw [← hTHo i1 h1 j1 (by omega), ← e1, ha]
          exact hpar
        · rw [hcl2] at hj1 hj2
          simp at hj1 hj2
          omega
        · rw [hcl3 i1 h1] at hj1
          simp at hj1
