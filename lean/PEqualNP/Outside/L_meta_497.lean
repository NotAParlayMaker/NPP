import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

lemma memVars {φ : CNF} {x : ℕ} :
    x ∈ vars φ ↔ ∃ c ∈ φ, ∃ l ∈ c, l.1 = x := by
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]

lemma clauseAtIndex {φ : CNF} {i : ℕ} (h : 0 < (clauseAt φ i).length) :
    i < φ.length := by
  by_contra hi
  rw [clauseAt, List.getD_eq_default _ _ (by omega)] at h
  simp at h

lemma cvcPosition {φ : CNF} {i j : ℕ}
    (hi : i < (cvcFormula φ).length) (hj : j < (clauseAt (cvcFormula φ) i).length) :
    (i < φ.length ∧ j ≤ (φ.getD i []).length) ∨ (i = φ.length ∧ j = 0) := by
  by_cases h : i < φ.length
  · left
    refine ⟨h, ?_⟩
    have hm : i < (φ.map (fun c => c ++ [(fresh φ, true)])).length := by simpa using h
    rw [clauseAt, cvcFormula, List.getD_append _ _ _ _ hm,
      List.getD_eq_getElem _ _ hm, List.getElem_map] at hj
    rw [List.getD_eq_getElem _ _ h]
    simp at hj
    omega
  · have he : i = φ.length := by
      simp [cvcFormula] at hi
      omega
    subst i
    have ha : (φ.map (fun c => c ++ [(fresh φ, true)])).length ≤ φ.length := by simp
    rw [clauseAt, cvcFormula, List.getD_append_right _ _ _ _ ha] at hj
    simp at hj
    omega

lemma encodeClauseLength (c : Clause) :
    c.length + 1 ≤ (encodeClause c).length := by
  have h : c.length ≤ (c.flatMap encodeLiteral).length := by
    induction c with
    | nil => simp
    | cons l ls ih =>
        have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        omega
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  omega

lemma encodeCnfLength (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
      simpa only [encodeCNF, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
        using Nat.add_le_add (encodeClauseLength c) ih

lemma mem_vars_cvc (φ : CNF) (x : ℕ) :
    x ∈ vars (cvcFormula φ) ↔ x ∈ vars φ ∨ x = fresh φ := by
  simp [vars, cvcFormula, List.mem_flatMap]
  aesop

lemma clauseAt_cvc_of_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  unfold clauseAt cvcFormula
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma clauseAt_cvc_last (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  unfold clauseAt cvcFormula
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma off_succ (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    ((φ.take (i + 1)).map (fun c => c.length + 1)).sum =
      ((φ.take i).map (fun c => c.length + 1)).sum + ((φ.getD i []).length + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi,
    Option.toList_some, List.map_append, List.sum_append]
  simp

lemma off_mono (φ : CNF) (i i' : ℕ) (h : i ≤ i') (h' : i' ≤ φ.length) :
    ((φ.take i).map (fun c => c.length + 1)).sum ≤
      ((φ.take i').map (fun c => c.length + 1)).sum := by
  induction h with
  | refl => exact le_refl _
  | @step m hm ih =>
    have := off_succ φ m (by omega)
    have := ih (by omega)
    show _ ≤ ((φ.take (m + 1)).map (fun c => c.length + 1)).sum
    omega

lemma off_total (φ : CNF) :
    ((φ.take φ.length).map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  rw [List.take_length]
  exact encodeCnfLength φ

lemma flat_pos (φ : CNF) : ∀ (p : ℕ) (l : Literal),
    (φ.flatMap (fun c => c.map some ++ [none]))[p]? = some (some l) →
    ∃ i j, i < φ.length ∧ j < (φ.getD i []).length ∧
      p = ((φ.take i).map (fun c => c.length + 1)).sum + j ∧ (φ.getD i [])[j]? = some l := by
  induction φ with
  | nil =>
    intro p l h
    simp at h
  | cons c cs ih =>
    intro p l h
    rw [List.flatMap_cons] at h
    by_cases hp : p < (c.map some ++ [none]).length
    · rw [List.getElem?_append_left hp] at h
      by_cases hp2 : p < c.length
      · refine ⟨0, p, by simp, by simpa using hp2, by simp, ?_⟩
        rw [List.getElem?_append_left (by simpa using hp2)] at h
        simpa [List.getElem?_map] using h
      · exfalso
        have hpe : p = c.length := by
          simp at hp
          omega
        subst hpe
        simp at h
    · have hlen : (List.map some c ++ [none]).length = c.length + 1 := by simp
      rw [hlen] at hp
      rw [List.getElem?_append_right (by omega), hlen] at h
      obtain ⟨i, j, hi, hj, hpe, hg⟩ := ih _ l h
      refine ⟨i + 1, j, by simpa using hi, by simpa using hj, ?_, by simpa using hg⟩
      rw [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

lemma parity_flag (t : ℕ) (b : Bool) :
    (((t % 2 == 1) == b) = true) ↔ (t % 2 = 1 ↔ b = true) := by
  cases b <;> simp

lemma mem_ite_nil {c : Prop} [Decidable c] (l : List ℕ) (x : ℕ) :
    x ∈ (if c then l else []) ↔ c ∧ x ∈ l := by
  split_ifs with h <;> simp [h]

lemma nodup_app (g : ℕ → ℕ) (s : ℕ) {l1 l2 : List ℕ}
    (h1 : l1.Nodup ∧ ∀ x ∈ l1, g x < s) (h2 : l2.Nodup) (c2 : ∀ x ∈ l2, g x = s) :
    (l1 ++ l2).Nodup ∧ ∀ x ∈ l1 ++ l2, g x < s + 1 := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨h1.1, h2, ?_⟩
    intro a ha b hb hab
    have := h1.2 a ha
    have := c2 b hb
    subst hab
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := h1.2 x hx
      omega
    · have := c2 x hx
      omega

lemma nodup_disj {l1 l2 : List ℕ} (h1 : l1.Nodup) (h2 : l2.Nodup)
    (hd : ∀ x ∈ l1, x ∈ l2 → False) : (l1 ++ l2).Nodup := by
  rw [List.nodup_append]
  refine ⟨h1, h2, ?_⟩
  intro a ha b hb hab
  subst hab
  exact hd a ha hb

lemma nodup_flatMap' (l : List ℕ) (F : ℕ → List ℕ) (hl : l.Nodup)
    (h1 : ∀ a ∈ l, (F a).Nodup)
    (hd : ∀ a ∈ l, ∀ b ∈ l, ∀ x, x ∈ F a → x ∈ F b → a = b) : (l.flatMap F).Nodup := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.flatMap_cons]
    have hnd := List.nodup_cons.mp hl
    refine nodup_disj (h1 a (by simp)) (ih hnd.2 (fun b hb => h1 b (by simp [hb]))
      (fun b hb c hc x hx hy => hd b (by simp [hb]) c (by simp [hc]) x hx hy)) ?_
    intro x hx hy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hy
    have := hd a (by simp) b (by simp [hb]) x hx hxb
    subst this
    exact hnd.1 hb

def Uq (N K x : ℕ) : ℕ := (x - N) / K / N

def Vq (N K x : ℕ) : ℕ := (x - N) / K % N

lemma dec_thread (N K u v t : ℕ) (hv : v < N) (ht : t < K) :
    Uq N K (N + K * (u * N + v) + t) = u ∧ Vq N K (N + K * (u * N + v) + t) = v ∧
      ¬ (N + K * (u * N + v) + t < N) := by
  have hK : 0 < K := by omega
  have hN : 0 < N := by omega
  have h1 : N + K * (u * N + v) + t - N = K * (u * N + v) + t := by
    generalize K * (u * N + v) = X
    omega
  have e1 : (K * (u * N + v) + t) / K = u * N + v := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt ht, Nat.add_zero]
  have f1 : (u * N + v) / N = u := by
    rw [Nat.mul_comm u N, Nat.mul_add_div hN, Nat.div_eq_of_lt hv, Nat.add_zero]
  have f3 : (u * N + v) % N = v := by
    rw [Nat.mul_comm u N, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  refine ⟨?_, ?_, ?_⟩
  · unfold Uq
    rw [h1, e1, f1]
  · unfold Vq
    rw [h1, e1, f3]
  · generalize K * (u * N + v) = X
    omega

def tagOf (E N K x : ℕ) : ℕ :=
  if x < N then (if 2 * E + 2 ≤ x then x - (2 * E + 2) else (x - 1) / 2)
  else (if 2 * E + 2 ≤ Vq N K x then
    (if 2 * E + 2 ≤ Uq N K x then Uq N K x - (2 * E + 2) else Vq N K x - (2 * E + 2))
    else Uq N K x / 2)

def slotOf (E N K x : ℕ) : ℕ :=
  if x < N then (if 2 * E + 2 ≤ x then 4 else 5)
  else (if 2 * E + 2 ≤ Vq N K x then (if 2 * E + 2 ≤ Uq N K x then 2 else 1) else 3)

lemma tag_thread (E N K u v t : ℕ) (hv : v < N) (ht : t < K) :
    tagOf E N K (N + K * (u * N + v) + t) =
      (if 2 * E + 2 ≤ v then (if 2 * E + 2 ≤ u then u - (2 * E + 2) else v - (2 * E + 2))
        else u / 2) ∧
    slotOf E N K (N + K * (u * N + v) + t) =
      (if 2 * E + 2 ≤ v then (if 2 * E + 2 ≤ u then 2 else 1) else 3) ∧
    Vq N K (N + K * (u * N + v) + t) = v := by
  obtain ⟨h1, h2, h3⟩ := dec_thread N K u v t hv ht
  refine ⟨?_, ?_, h2⟩
  · unfold tagOf
    simp only [h3, ite_false, h1, h2]
  · unfold slotOf
    simp only [h3, ite_false, h1, h2]

def blk (φ : CNF) (off e : ℕ → ℕ) (num : Vertex → ℕ) (f : ℕ → ℕ) (lit : ℕ → ℕ → Literal)
    (inner : ℕ → ℕ → Bool → List ℕ) (i j : ℕ) : List ℕ :=
  inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else [])

lemma mem_blk (φ : CNF) (off e : ℕ → ℕ) (num : Vertex → ℕ) (f : ℕ → ℕ) (lit : ℕ → ℕ → Literal)
    (inner : ℕ → ℕ → Bool → List ℕ) (i j x : ℕ) :
    x ∈ blk φ off e num f lit inner i j ↔
      ((((x ∈ inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ∨
        ∃ l, (l < (φ.getD i []).length + 1 ∧ j < l) ∧
          x ∈ inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ∨
        ((j < (φ.getD i []).length ∧ off i + j = e (lit i j).1) ∧
          x ∈ inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false)) ∨
        (j ≠ f i ∧ x = num (Sum.inr (i, j)))) ∨
        ((j < (φ.getD i []).length ∧ off i + j = e (lit i j).1) ∧
          x = num (Sum.inl ((lit i j).1, true)))) := by
  unfold blk
  simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
    decide_eq_true_eq, mem_ite_nil, List.mem_singleton]

end PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Outside.L_meta_497_aux PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise in
theorem PEqualNP.Outside.L_meta_497 : ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff he_lt he_inj he_pos num hnumv hnumy hnumo hnumlast H hH f hf TH hTH lit hlit inner hinner TL hTL
  have hTL' : TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => blk φ off e num f lit inner i j)) ++ (inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++ inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]) := hTL
  have hoffS : ∀ i, i < φ.length → off (i + 1) = off i + ((φ.getD i []).length + 1) := by
    intro i hi
    rw [hoff, hoff]
    exact off_succ φ i hi
  have hoffM : ∀ i i', i ≤ i' → i' ≤ φ.length → off i ≤ off i' := by
    intro i i' h h'
    rw [hoff, hoff]
    exact off_mono φ i i' h h'
  have hoffE : off φ.length ≤ E := by
    rw [hoff, hE]
    exact off_total φ
  have hpos : ∀ i, i < φ.length → ∀ j, j ≤ (φ.getD i []).length → off i + j < E := by
    intro i hi j hj
    have := hoffS i hi
    have := hoffM (i + 1) φ.length (by omega) (le_refl _)
    omega
  have hposinj : ∀ i, i < φ.length → ∀ j, j ≤ (φ.getD i []).length → ∀ i', i' < φ.length →
      ∀ j', j' ≤ (φ.getD i' []).length → off i + j = off i' + j' → i = i' ∧ j = j' := by
    intro i hi j hj i' hi' j' hj' h
    rcases Nat.lt_trichotomy i i' with hl | hl | hl
    · have := hoffS i hi
      have := hoffM (i + 1) i' (by omega) (by omega)
      omega
    · subst hl
      exact ⟨rfl, by omega⟩
    · have := hoffS i' hi'
      have := hoffM (i' + 1) i (by omega) (by omega)
      omega
  have hlitget : ∀ i j, j ≤ (φ.getD i []).length →
      (φ.getD i [] ++ [(fresh φ, true)])[j]? = some (lit i j) := by
    intro i j hj
    have hlt : j < (φ.getD i [] ++ [(fresh φ, true)]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hlit, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hlitlt : ∀ i, i < φ.length → ∀ j, j < (φ.getD i []).length →
      (φ.getD i [])[j]? = some (lit i j) ∧ (lit i j).1 ∈ vars φ := by
    intro i hi j hj
    have h := hlitget i j (by omega)
    rw [List.getElem?_append_left hj] at h
    refine ⟨h, ?_⟩
    have hm : lit i j ∈ φ.getD i [] := List.mem_of_getElem? h
    have hc : φ.getD i [] ∈ φ := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact memVars.mpr ⟨_, hc, _, hm, rfl⟩
  have hlitlast : ∀ i, lit i (φ.getD i []).length = (fresh φ, true) := by
    intro i
    have h := hlitget i _ (le_refl _)
    rw [List.getElem?_append_right (le_refl _)] at h
    simpa using h.symm
  have hnv0 : ∀ z ∈ vars φ, num (Sum.inl (z, false)) = 2 * e z := by
    intro z hz
    have := hnumv z hz false
    simpa using this
  have hnv1 : ∀ z ∈ vars φ, num (Sum.inl (z, true)) = 2 * e z + 1 := by
    intro z hz
    have := hnumv z hz true
    simpa using this
  have hny0 : num (Sum.inl (fresh φ, false)) = 2 * E := by
    have := hnumy false
    simpa using this
  have hny1 : num (Sum.inl (fresh φ, true)) = 2 * E + 1 := by
    have := hnumy true
    simpa using this
  have hnumL : ∀ i, i < φ.length → ∀ j, j ≤ (φ.getD i []).length →
      ∃ p, num (Sum.inl (lit i j)) = 2 * p + (if (lit i j).2 then 1 else 0) ∧
        ((∃ z ∈ vars φ, p = e z) ∨ p = E) ∧ p ≤ E := by
    intro i hi j hj
    rcases Nat.lt_or_ge j (φ.getD i []).length with h | h
    · have hv := (hlitlt i hi j h).2
      exact ⟨e (lit i j).1, hnumv _ hv _, Or.inl ⟨_, hv, rfl⟩, (he_lt _ hv).le⟩
    · have hj' : j = (φ.getD i []).length := by omega
      subst hj'
      rw [hlitlast]
      exact ⟨E, hnumy true, Or.inr rfl, le_refl _⟩
  have hTH0 : ∀ p, ((∃ z ∈ vars φ, p = e z) ∨ p = E) → p ≤ E → ¬ TH (2 * p) := by
    intro p hp hpE h
    rw [hTH] at h
    rcases h with ⟨z, hz, h⟩ | h | ⟨i, hi, j, hj, hne, h⟩ | h <;> omega
  have hTH1 : ∀ p, ((∃ z ∈ vars φ, p = e z) ∨ p = E) → p ≤ E → TH (2 * p + 1) := by
    intro p hp hpE
    rw [hTH]
    rcases hp with ⟨z, hz, rfl⟩ | rfl
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr (Or.inl rfl)
  have hTHlit : ∀ p, ((∃ z ∈ vars φ, p = e z) ∨ p = E) → p ≤ E → ∀ b : Bool,
      (TH (2 * p + (if b then 1 else 0)) ↔ b = true) := by
    intro p hp hpE b
    cases b
    · have h0 := hTH0 p hp hpE
      simpa using h0
    · have h1 := hTH1 p hp hpE
      simpa using h1
  have hTHocc : ∀ i, i < φ.length → ∀ j, j ≤ (φ.getD i []).length →
      (TH (2 * (E + 1) + off i + j) ↔ j ≠ f i) := by
    intro i hi j hj
    have hp := hpos i hi j hj
    rw [hTH]
    constructor
    · rintro (⟨z, hz, h⟩ | h | ⟨i', hi', j', hj', hne, h⟩ | h)
      · have := he_lt z hz
        omega
      · omega
      · obtain ⟨rfl, rfl⟩ := hposinj i hi j hj i' hi' j' hj' (by omega)
        exact hne
      · omega
    · intro hne
      exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hne, rfl⟩))
  have hin : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t, t < 2 * k ∧ x = N + 2 * k * (u * N + v) + t ∧ (t % 2 = 1 ↔ b = true) := by
    intro u v b x
    rw [hinner]
    simp only [List.mem_map, List.mem_filter, List.mem_range, parity_flag]
    constructor
    · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
      exact ⟨t, ht, rfl, hp⟩
    · rintro ⟨t, ht, rfl, hp⟩
      exact ⟨t, ⟨ht, hp⟩, rfl⟩
  have hind : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner]
    refine List.Nodup.map ?_ (List.Nodup.filter _ List.nodup_range)
    intro a c h
    simp only at h
    omega
  have hblk : ∀ i, i < φ.length → ∀ j, j ≤ (φ.getD i []).length → ∀ x,
      x ∈ blk φ off e num f lit inner i j → tagOf E N (2 * k) x = off i + j := by
    intro i hi j hj x hx
    have hp := hpos i hi j hj
    have hO := hnumo i j hi hj
    rw [mem_blk] at hx
    rcases hx with (((h | ⟨l, ⟨hl, hjl⟩, h⟩) | ⟨hc, h⟩) | ⟨hne, h⟩) | ⟨hc, h⟩
    · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      obtain ⟨p, hnp, -, hpE⟩ := hnumL i hi j hj
      have hu : num (Sum.inl (lit i j)) ≤ 2 * E + 1 := by
        rw [hnp]
        split_ifs <;> omega
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).1]
      split_ifs <;> omega
    · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      have hOl := hnumo i l hi (by omega)
      have hpl := hpos i hi l (by omega)
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).1]
      split_ifs <;> omega
    · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      have hz := (hlitlt i hi j hc.1).2
      have n0 := hnv0 _ hz
      have n1 := hnv1 _ hz
      have he := he_lt _ hz
      have hc2 := hc.2
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).1]
      split_ifs <;> omega
    · rw [h, hO]
      unfold tagOf
      split_ifs <;> omega
    · have hz := (hlitlt i hi j hc.1).2
      have n1 := hnv1 _ hz
      have he := he_lt _ hz
      have hc2 := hc.2
      rw [h, n1]
      unfold tagOf
      split_ifs <;> omega
  have hblknd : ∀ i, i < φ.length → ∀ j, j ≤ (φ.getD i []).length →
      (blk φ off e num f lit inner i j).Nodup := by
    intro i hi j hj
    have hp := hpos i hi j hj
    have hO := hnumo i j hi hj
    unfold blk
    refine (nodup_app (slotOf E N (2 * k)) 5 (nodup_app _ 4 (nodup_app _ 3 (nodup_app _ 2
      ⟨hind _ _ _, ?_⟩ ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_).1
    · intro x h
      obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      obtain ⟨p, hnp, -, hpE⟩ := hnumL i hi j hj
      have hu : num (Sum.inl (lit i j)) ≤ 2 * E + 1 := by
        rw [hnp]
        split_ifs <;> omega
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).2.1]
      split_ifs <;> omega
    · refine nodup_flatMap' _ _ (List.Nodup.filter _ List.nodup_range) (fun l _ => hind _ _ _) ?_
      intro a ha b hb x hxa hxb
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at ha hb
      obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp hxa
      obtain ⟨t', ht', hx', -⟩ := (hin _ _ _ _).mp hxb
      have hOa := hnumo i a hi (by omega)
      have hOb := hnumo i b hi (by omega)
      have hpa := hpos i hi a (by omega)
      have hpb := hpos i hi b (by omega)
      have v1 := (tag_thread E N (2 * k) (num (Sum.inr (i, j))) (num (Sum.inr (i, a))) t
        (by omega) ht).2.2
      have v2 := (tag_thread E N (2 * k) (num (Sum.inr (i, j))) (num (Sum.inr (i, b))) t'
        (by omega) ht').2.2
      rw [← hx'] at v2
      omega
    · intro x h
      obtain ⟨l, hl, h⟩ := List.mem_flatMap.mp h
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
      obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      have hOl := hnumo i l hi (by omega)
      have hpl := hpos i hi l (by omega)
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).2.1]
      split_ifs <;> omega
    · split_ifs
      · exact hind _ _ _
      · exact List.nodup_nil
    · intro x h
      rw [mem_ite_nil] at h
      obtain ⟨hc, h⟩ := h
      obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      have hz := (hlitlt i hi j hc.1).2
      have n0 := hnv0 _ hz
      have n1 := hnv1 _ hz
      have he := he_lt _ hz
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).2.1]
      split_ifs <;> omega
    · split_ifs <;> simp
    · intro x h
      rw [mem_ite_nil] at h
      obtain ⟨hne, h⟩ := h
      rw [List.mem_singleton] at h
      rw [h, hO]
      unfold slotOf
      split_ifs <;> omega
    · split_ifs <;> simp
    · intro x h
      rw [mem_ite_nil] at h
      obtain ⟨hc, h⟩ := h
      rw [List.mem_singleton] at h
      have hz := (hlitlt i hi j hc.1).2
      have n1 := hnv1 _ hz
      have he := he_lt _ hz
      rw [h, n1]
      unfold slotOf
      split_ifs <;> omega
  have hmain : ((List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => blk φ off e num f lit inner i j))).Nodup := by
    refine nodup_flatMap' _ _ List.nodup_range ?_ ?_
    · intro i hi
      have hi' := List.mem_range.mp hi
      refine nodup_flatMap' _ _ List.nodup_range ?_ ?_
      · intro j hj
        have hj' := List.mem_range.mp hj
        exact hblknd i hi' j (by omega)
      · intro a ha b hb x hxa hxb
        have ha' := List.mem_range.mp ha
        have hb' := List.mem_range.mp hb
        have := hblk i hi' a (by omega) x hxa
        have := hblk i hi' b (by omega) x hxb
        omega
    · intro i hi i' hi' x hx hx'
      have hi1 := List.mem_range.mp hi
      have hi2 := List.mem_range.mp hi'
      obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hx
      obtain ⟨j', hj', hxj'⟩ := List.mem_flatMap.mp hx'
      have hj1 := List.mem_range.mp hj
      have hj2 := List.mem_range.mp hj'
      have t1 := hblk i hi1 j (by omega) x hxj
      have t2 := hblk i' hi2 j' (by omega) x hxj'
      exact (hposinj i hi1 j (by omega) i' hi2 j' (by omega) (by omega)).1
  have htailtag : ∀ x, x ∈ (inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++ inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]) → tagOf E N (2 * k) x = E := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (h | h) | h | h
    · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).1]
      split_ifs <;> omega
    · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
      rw [(tag_thread E N (2 * k) _ _ t (by omega) ht).1]
      split_ifs <;> omega
    · rw [h, hny1]
      unfold tagOf
      split_ifs <;> omega
    · rw [h, hnumlast]
      unfold tagOf
      split_ifs <;> omega
  have htailnd : (inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++ inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]).Nodup := by
    refine nodup_disj (nodup_disj (hind _ _ _) (hind _ _ _) ?_) ?_ ?_
    · intro x h1 h2
      obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h1
      obtain ⟨t', ht', hx', -⟩ := (hin _ _ _ _).mp h2
      have v1 := (tag_thread E N (2 * k) (num (Sum.inl (fresh φ, false)))
        (num (Sum.inl (fresh φ, true))) t (by omega) ht).2.2
      have v2 := (tag_thread E N (2 * k) (num (Sum.inl (fresh φ, false)))
        (num (Sum.inr (φ.length, 0))) t' (by omega) ht').2.2
      rw [← hx'] at v2
      omega
    · rw [hny1, hnumlast]
      simp
      omega
    · intro x h1 h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      have hxN : x < N := by
        rcases h2 with h | h <;> omega
      rcases List.mem_append.mp h1 with h | h
      · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
        exact (dec_thread N (2 * k) _ _ t (by omega : num (Sum.inl (fresh φ, true)) < N) ht).2.2 hxN
      · obtain ⟨t, ht, rfl, -⟩ := (hin _ _ _ _).mp h
        exact (dec_thread N (2 * k) _ _ t (by omega : num (Sum.inr (φ.length, 0)) < N) ht).2.2 hxN
  have hmem : ∀ x, x ∈ TL ↔ (∃ i, i < φ.length ∧ ∃ j, j < (φ.getD i []).length + 1 ∧
      x ∈ blk φ off e num f lit inner i j) ∨
      ((x ∈ inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ∨
        x ∈ inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false) ∨
        x = num (Sum.inl (fresh φ, true)) ∨ x = num (Sum.inr (φ.length, 0))) := by
    intro x
    rw [hTL']
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false]
  refine ⟨?_, ?_⟩
  · rw [hTL']
    refine nodup_disj hmain htailnd ?_
    intro x hx hx'
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hx
    obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.mp hxi
    have hi1 := List.mem_range.mp hi
    have hj1 := List.mem_range.mp hj
    have t1 := hblk i hi1 j (by omega) x hxj
    have t2 := htailtag x hx'
    have := hpos i hi1 j (by omega)
    omega
  · intro x
    rw [hmem]
    constructor
    · rintro (⟨i, hi, j, hj, hx⟩ | ((h | h) | h | h))
      · have hj' : j ≤ (φ.getD i []).length := by omega
        have hp := hpos i hi j hj'
        have hO := hnumo i j hi hj'
        rw [mem_blk] at hx
        rcases hx with (((h | ⟨l, ⟨hl, hjl⟩, h⟩) | ⟨hc, h⟩) | ⟨hne, h⟩) | ⟨hc, h⟩
        · obtain ⟨t, ht, rfl, hfl⟩ := (hin _ _ _ _).mp h
          obtain ⟨p, hnp, hpz, hpE⟩ := hnumL i hi j hj'
          have hu : num (Sum.inl (lit i j)) ≤ 2 * E + 1 := by
            rw [hnp]
            split_ifs <;> omega
          right
          refine ⟨⟨num (Sum.inl (lit i j)), by omega⟩, ⟨num (Sum.inr (i, j)), by omega⟩, ?_, ?_,
            t, ht, rfl, ?_⟩
          · show num (Sum.inl (lit i j)) < num (Sum.inr (i, j))
            omega
          · rw [hH]
            refine ⟨Sum.inl (lit i j), Sum.inr (i, j), ?_, rfl, rfl⟩
            show (clauseAt (cvcFormula φ) i)[j]? = some (lit i j)
            rw [clauseAt_cvc_of_lt φ hi]
            exact hlitget i j hj'
          · show (t % 2 = 1 ↔ TH (num (Sum.inl (lit i j))))
            rw [hnp, hTHlit p hpz hpE]
            exact hfl
        · obtain ⟨t, ht, rfl, hfl⟩ := (hin _ _ _ _).mp h
          have hOl := hnumo i l hi (by omega)
          have hpl := hpos i hi l (by omega)
          right
          refine ⟨⟨num (Sum.inr (i, j)), by omega⟩, ⟨num (Sum.inr (i, l)), by omega⟩, ?_, ?_,
            t, ht, rfl, ?_⟩
          · show num (Sum.inr (i, j)) < num (Sum.inr (i, l))
            omega
          · rw [hH]
            refine ⟨Sum.inr (i, j), Sum.inr (i, l), ?_, rfl, rfl⟩
            show (i = i ∧ j ≠ l ∧ j < (clauseAt (cvcFormula φ) i).length ∧
              l < (clauseAt (cvcFormula φ) i).length)
            rw [clauseAt_cvc_of_lt φ hi]
            have hlen : (φ.getD i [] ++ [(fresh φ, true)]).length = (φ.getD i []).length + 1 := by
              simp
            rw [hlen]
            exact ⟨rfl, by omega, by omega, by omega⟩
          · show (t % 2 = 1 ↔ TH (num (Sum.inr (i, j))))
            rw [hO, hTHocc i hi j hj']
            simpa using hfl
        · obtain ⟨t, ht, rfl, hfl⟩ := (hin _ _ _ _).mp h
          have hz := (hlitlt i hi j hc.1).2
          have n0 := hnv0 _ hz
          have n1 := hnv1 _ hz
          have he := he_lt _ hz
          right
          refine ⟨⟨num (Sum.inl ((lit i j).1, false)), by omega⟩,
            ⟨num (Sum.inl ((lit i j).1, true)), by omega⟩, ?_, ?_, t, ht, rfl, ?_⟩
          · show num (Sum.inl ((lit i j).1, false)) < num (Sum.inl ((lit i j).1, true))
            omega
          · rw [hH]
            refine ⟨Sum.inl ((lit i j).1, false), Sum.inl ((lit i j).1, true), ?_, rfl, rfl⟩
            show ((lit i j).1 = (lit i j).1 ∧ false ≠ true ∧ (lit i j).1 ∈ vars (cvcFormula φ))
            exact ⟨rfl, Bool.false_ne_true, (mem_vars_cvc φ _).mpr (Or.inl hz)⟩
          · show (t % 2 = 1 ↔ TH (num (Sum.inl ((lit i j).1, false))))
            rw [n0]
            constructor
            · intro h1
              exact absurd (hfl.mp h1) Bool.false_ne_true
            · intro h1
              exact absurd h1 (hTH0 _ (Or.inl ⟨_, hz, rfl⟩) he.le)
        · left
          rw [h, hO]
          exact (hTHocc i hi j hj').mpr hne
        · have hz := (hlitlt i hi j hc.1).2
          have he := he_lt _ hz
          left
          rw [h, hnv1 _ hz]
          exact hTH1 _ (Or.inl ⟨_, hz, rfl⟩) he.le
      · obtain ⟨t, ht, rfl, hfl⟩ := (hin _ _ _ _).mp h
        right
        refine ⟨⟨num (Sum.inl (fresh φ, false)), by omega⟩,
          ⟨num (Sum.inl (fresh φ, true)), by omega⟩, ?_, ?_, t, ht, rfl, ?_⟩
        · show num (Sum.inl (fresh φ, false)) < num (Sum.inl (fresh φ, true))
          omega
        · rw [hH]
          refine ⟨Sum.inl (fresh φ, false), Sum.inl (fresh φ, true), ?_, rfl, rfl⟩
          show (fresh φ = fresh φ ∧ false ≠ true ∧ fresh φ ∈ vars (cvcFormula φ))
          exact ⟨rfl, Bool.false_ne_true, (mem_vars_cvc φ _).mpr (Or.inr rfl)⟩
        · show (t % 2 = 1 ↔ TH (num (Sum.inl (fresh φ, false))))
          rw [hny0]
          constructor
          · intro h1
            exact absurd (hfl.mp h1) Bool.false_ne_true
          · intro h1
            exact absurd h1 (hTH0 E (Or.inr rfl) (le_refl _))
      · obtain ⟨t, ht, rfl, hfl⟩ := (hin _ _ _ _).mp h
        right
        refine ⟨⟨num (Sum.inl (fresh φ, false)), by omega⟩,
          ⟨num (Sum.inr (φ.length, 0)), by omega⟩, ?_, ?_, t, ht, rfl, ?_⟩
        · show num (Sum.inl (fresh φ, false)) < num (Sum.inr (φ.length, 0))
          omega
        · rw [hH]
          refine ⟨Sum.inl (fresh φ, false), Sum.inr (φ.length, 0), ?_, rfl, rfl⟩
          show (clauseAt (cvcFormula φ) φ.length)[0]? = some (fresh φ, false)
          rw [clauseAt_cvc_last]
          rfl
        · show (t % 2 = 1 ↔ TH (num (Sum.inl (fresh φ, false))))
          rw [hny0]
          constructor
          · intro h1
            exact absurd (hfl.mp h1) Bool.false_ne_true
          · intro h1
            exact absurd h1 (hTH0 E (Or.inr rfl) (le_refl _))
      · left
        rw [h, hny1]
        exact hTH1 E (Or.inr rfl) (le_refl _)
      · left
        rw [h, hnumlast, hTH]
        exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (h | ⟨u, v, huv, hadj, t, ht, rfl, hfl⟩)
      · rw [hTH] at h
        rcases h with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
        · obtain ⟨l, hl, hlz⟩ := he_pos z hz
          obtain ⟨i, j, hi, hj, hpe, hg⟩ := flat_pos φ _ l hl
          rw [← hoff i] at hpe
          have hlj := (hlitlt i hi j hj).1
          have hll : lit i j = l := by
            rw [hlj] at hg
            exact Option.some.inj hg
          left
          refine ⟨i, hi, j, by omega, (mem_blk _ _ _ _ _ _ _ _ _ _).mpr (Or.inr ⟨⟨hj, ?_⟩, ?_⟩)⟩
          · rw [hll, hlz]
            exact hpe.symm
          · rw [hll, hlz, hnv1 z hz]
        · exact Or.inr (Or.inr (Or.inl hny1.symm))
        · left
          exact ⟨i, hi, j, by omega, (mem_blk _ _ _ _ _ _ _ _ _ _).mpr
            (Or.inl (Or.inr ⟨hne, (hnumo i j hi hj).symm⟩))⟩
        · exact Or.inr (Or.inr (Or.inr hnumlast.symm))
      · rw [hH] at hadj
        obtain ⟨U, V, hUV, hU, hV⟩ := hadj
        have huv' : num U < num V := by
          rw [hU, hV]
          exact huv
        rw [← hU] at hfl
        rw [← hU, ← hV]
        cases U with
        | inl a =>
          cases V with
          | inl b =>
            obtain ⟨h1, h2, h3⟩ : a.1 = b.1 ∧ a.2 ≠ b.2 ∧ a.1 ∈ vars (cvcFormula φ) := hUV
            obtain ⟨z, s⟩ := a
            obtain ⟨z', s'⟩ := b
            simp only at h1 h2 h3
            subst h1
            rcases (mem_vars_cvc φ z).mp h3 with hz | hzy
            · have n0 := hnv0 z hz
              have n1 := hnv1 z hz
              have he := he_lt z hz
              cases s <;> cases s'
              · exact absurd rfl h2
              · obtain ⟨l, hl, hlz⟩ := he_pos z hz
                obtain ⟨i, j, hi, hj, hpe, hg⟩ := flat_pos φ _ l hl
                rw [← hoff i] at hpe
                have hlj := (hlitlt i hi j hj).1
                have hll : lit i j = l := by
                  rw [hlj] at hg
                  exact Option.some.inj hg
                left
                refine ⟨i, hi, j, by omega, (mem_blk _ _ _ _ _ _ _ _ _ _).mpr
                  (Or.inl (Or.inl (Or.inr ⟨⟨hj, ?_⟩, (hin _ _ _ _).mpr ⟨t, ht, ?_, ?_⟩⟩)))⟩
                · rw [hll, hlz]
                  exact hpe.symm
                · rw [hll, hlz]
                · constructor
                  · intro h1
                    rw [n0] at hfl
                    exact absurd (hfl.mp h1) (hTH0 _ (Or.inl ⟨z, hz, rfl⟩) he.le)
                  · intro h1
                    exact absurd h1 Bool.false_ne_true
              · omega
              · exact absurd rfl h2
            · subst hzy
              cases s <;> cases s'
              · exact absurd rfl h2
              · right
                left
                left
                refine (hin _ _ _ _).mpr ⟨t, ht, rfl, ?_⟩
                constructor
                · intro h1
                  rw [hny0] at hfl
                  exact absurd (hfl.mp h1) (hTH0 E (Or.inr rfl) (le_refl _))
                · intro h1
                  exact absurd h1 Bool.false_ne_true
              · omega
              · exact absurd rfl h2
          | inr ij =>
            obtain ⟨i, j⟩ := ij
            have hUV' : (clauseAt (cvcFormula φ) i)[j]? = some a := hUV
            obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hUV'
            have hi' := clauseAtIndex (Nat.zero_lt_of_lt hjlt)
            rcases cvcPosition hi' hjlt with ⟨hi, hj⟩ | ⟨hi, hj⟩
            · rw [clauseAt_cvc_of_lt φ hi, hlitget i j hj] at hUV'
              have ha : lit i j = a := Option.some.inj hUV'
              subst ha
              obtain ⟨p, hnp, hpz, hpE⟩ := hnumL i hi j hj
              left
              refine ⟨i, hi, j, by omega, (mem_blk _ _ _ _ _ _ _ _ _ _).mpr
                (Or.inl (Or.inl (Or.inl (Or.inl ((hin _ _ _ _).mpr ⟨t, ht, rfl, ?_⟩)))))⟩
              rw [hnp, hTHlit p hpz hpE] at hfl
              exact hfl
            · subst hi
              subst hj
              rw [clauseAt_cvc_last] at hUV'
              have ha : (fresh φ, false) = a := by
                simpa using hUV'
              subst ha
              right
              left
              right
              refine (hin _ _ _ _).mpr ⟨t, ht, rfl, ?_⟩
              constructor
              · intro h1
                rw [hny0] at hfl
                exact absurd (hfl.mp h1) (hTH0 E (Or.inr rfl) (le_refl _))
              · intro h1
                exact absurd h1 Bool.false_ne_true
        | inr ij =>
          obtain ⟨i, j⟩ := ij
          cases V with
          | inl b =>
            exfalso
            have hUV' : (clauseAt (cvcFormula φ) i)[j]? = some b := hUV
            obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hUV'
            have hi' := clauseAtIndex (Nat.zero_lt_of_lt hjlt)
            rcases cvcPosition hi' hjlt with ⟨hi, hj⟩ | ⟨hi, hj⟩
            · rw [clauseAt_cvc_of_lt φ hi, hlitget i j hj] at hUV'
              have hb : lit i j = b := Option.some.inj hUV'
              subst hb
              obtain ⟨p, hnp, hpz, hpE⟩ := hnumL i hi j hj
              have hO := hnumo i j hi hj
              have hu : num (Sum.inl (lit i j)) ≤ 2 * E + 1 := by
                rw [hnp]
                split_ifs <;> omega
              omega
            · subst hi
              subst hj
              rw [clauseAt_cvc_last] at hUV'
              have hb : (fresh φ, false) = b := by
                simpa using hUV'
              subst hb
              omega
          | inr kl =>
            obtain ⟨i', l⟩ := kl
            obtain ⟨h1, hjl, hj, hl⟩ : i = i' ∧ j ≠ l ∧ j < (clauseAt (cvcFormula φ) i).length ∧
              l < (clauseAt (cvcFormula φ) i).length := hUV
            subst h1
            have hi' := clauseAtIndex (Nat.zero_lt_of_lt hj)
            rcases cvcPosition hi' hj with ⟨hi, hj1⟩ | ⟨hi, hj1⟩
            · rcases cvcPosition hi' hl with ⟨-, hl1⟩ | ⟨hi2, -⟩
              · have hO := hnumo i j hi hj1
                have hOl := hnumo i l hi hl1
                left
                refine ⟨i, hi, j, by omega, (mem_blk _ _ _ _ _ _ _ _ _ _).mpr
                  (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, ⟨by omega, by omega⟩,
                    (hin _ _ _ _).mpr ⟨t, ht, rfl, ?_⟩⟩))))⟩
                rw [hO, hTHocc i hi j hj1] at hfl
                simpa using hfl
              · omega
            · exfalso
              subst hi
              rw [clauseAt_cvc_last] at hl
              simp at hl
              omega
