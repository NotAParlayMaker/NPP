import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

lemma encodeLiteral_len_ge (l : Literal) : 1 ≤ (encodeLiteral l).length := by
  simp [encodeLiteral]

lemma flatMap_encodeLiteral_len_ge (c : Clause) : c.length ≤ (c.flatMap encodeLiteral).length := by
  induction c with
  | nil => simp
  | cons l cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := encodeLiteral_len_ge l
    omega

lemma encodeClause_len_ge (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  have h1 := flatMap_encodeLiteral_len_ge c
  omega

lemma sum_le_encodeCNF (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c rest ih =>
    simp only [encodeCNF, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    have h1 := encodeClause_len_ge c
    omega

lemma off_step (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    ((φ.take (i + 1)).map (fun c => c.length + 1)).sum =
      ((φ.take i).map (fun c => c.length + 1)).sum + ((φ.getD i []).length + 1) := by
  induction φ generalizing i with
  | nil => simp at hi
  | cons c rest ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ]
      have h1 := ih i (by simpa using hi)
      omega

lemma off_mono (φ : CNF) {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) :
    ((φ.take i₁).map (fun c => c.length + 1)).sum ≤
      ((φ.take i₂).map (fun c => c.length + 1)).sum := by
  induction φ generalizing i₁ i₂ with
  | nil => simp
  | cons c rest ih =>
    cases i₁ with
    | zero => simp
    | succ i₁ =>
      cases i₂ with
      | zero => omega
      | succ i₂ =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        have h1 := ih (by omega : i₁ ≤ i₂)
        omega

lemma off_le_all (φ : CNF) (i : ℕ) :
    ((φ.take i).map (fun c => c.length + 1)).sum ≤ (φ.map (fun c => c.length + 1)).sum := by
  induction φ generalizing i with
  | nil => simp
  | cons c rest ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      have h1 := ih i
      omega

lemma off_add_lt_encodeCNF (φ : CNF) {i j : ℕ} (hi : i < φ.length)
    (hj : j ≤ (φ.getD i []).length) :
    ((φ.take i).map (fun c => c.length + 1)).sum + j < (encodeCNF φ).length := by
  have hstep := off_step φ i hi
  have hall := off_le_all φ (i + 1)
  have henc := sum_le_encodeCNF φ
  omega

lemma off_add_inj (φ : CNF) {i₁ i₂ j₁ j₂ : ℕ}
    (hi₁ : i₁ < φ.length) (hi₂ : i₂ < φ.length)
    (hj₁ : j₁ ≤ (φ.getD i₁ []).length) (hj₂ : j₂ ≤ (φ.getD i₂ []).length)
    (heq : ((φ.take i₁).map (fun c => c.length + 1)).sum + j₁ =
      ((φ.take i₂).map (fun c => c.length + 1)).sum + j₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  by_cases hlt : i₁ < i₂
  · have hstep := off_step φ i₁ hi₁
    have hm := off_mono φ (by omega : i₁ + 1 ≤ i₂)
    omega
  · by_cases hgt : i₂ < i₁
    · have hstep := off_step φ i₂ hi₂
      have hm := off_mono φ (by omega : i₂ + 1 ≤ i₁)
      omega
    · have hi : i₁ = i₂ := by omega
      subst hi
      exact ⟨rfl, by omega⟩

lemma flatMap_opt_eq (φ : CNF) (p : ℕ) (l : Literal)
    (hp : (φ.flatMap (fun c => c.map some ++ [none]))[p]? = some (some l)) :
    ∃ i < φ.length, ∃ j < (φ.getD i []).length,
      p = ((φ.take i).map (fun c => c.length + 1)).sum + j ∧
      (φ.getD i [])[j]? = some l := by
  induction φ generalizing p with
  | nil => simp at hp
  | cons c rest ih =>
    simp only [List.flatMap_cons] at hp
    have hlen : (c.map some ++ [none]).length = c.length + 1 := by simp
    by_cases hpc : p < c.length + 1
    · rw [List.getElem?_append_left (by omega)] at hp
      by_cases hpc' : p < c.length
      · rw [List.getElem?_append_left (by simp; omega)] at hp
        rw [List.getElem?_map, List.getElem?_eq_getElem hpc'] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        refine ⟨0, by simp, p, hpc', by simp, ?_⟩
        simp only [List.getD_cons_zero]
        rw [List.getElem?_eq_getElem hpc', hp]
      · have hpeq : p = c.length := by omega
        subst hpeq
        rw [List.getElem?_append_right (by simp)] at hp
        simp at hp
    · rw [List.getElem?_append_right (by omega)] at hp
      rw [hlen] at hp
      obtain ⟨i', hi', j, hj, hp', hget⟩ := ih (p - (c.length + 1)) hp
      refine ⟨i' + 1, by simpa using Nat.succ_lt_succ hi', j, by simpa using hj, ?_, by simpa using hget⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

lemma fresh_not_mem_vars (φ : CNF) : fresh φ ∉ vars φ := by
  intro h
  have hle : fresh φ ≤ (vars φ).sup id := Finset.le_sup (f := id) h
  unfold fresh at hle
  omega

lemma mem_vars_of_getElem? {φ : CNF} {i j : ℕ} {l : Literal}
    (hi : i < φ.length) (hj : (φ.getD i [])[j]? = some l) :
    l.1 ∈ vars φ := by
  unfold vars
  rw [List.mem_toFinset, List.mem_flatMap]
  refine ⟨φ.getD i [], ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.mem_map]
    exact ⟨l, List.mem_of_getElem? hj, rfl⟩

lemma clauseAt_cvcFormula_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  unfold clauseAt cvcFormula
  have hlen : (φ.map (fun C => C ++ [(fresh φ, true)])).length = φ.length := by simp
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getElem_append_left (by omega)]
  rw [List.getElem_map]
  rw [List.getD_eq_getElem _ _ hi]

lemma clauseAt_cvcFormula_eq (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  unfold clauseAt cvcFormula
  rw [List.getD_eq_getElem _ _ (by simp)]
  rw [List.getElem_append_right (by simp)]
  simp

lemma clauseAt_cvcFormula_gt (φ : CNF) {i : ℕ} (hi : φ.length < i) :
    clauseAt (cvcFormula φ) i = [] := by
  unfold clauseAt cvcFormula
  rw [List.getD_eq_default]
  simp
  omega

lemma mem_vars_cvcFormula (φ : CNF) (z : ℕ) :
    z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
  unfold vars cvcFormula
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨c, ⟨c', hc', rfl⟩ | rfl, l, hl, rfl⟩
    · rw [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact Or.inl ⟨c', hc', l, hl, rfl⟩
      · exact Or.inr rfl
    · rw [List.mem_singleton] at hl
      subst hl
      exact Or.inr rfl
  · rintro (⟨c, hc, l, hl, rfl⟩ | rfl)
    · exact ⟨c ++ [(fresh φ, true)], Or.inl ⟨c, hc, rfl⟩, l, List.mem_append_left _ hl, rfl⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), List.mem_singleton_self _, rfl⟩

lemma sub_decode {k N u₁ v₁ t₁ u₂ v₂ t₂ : ℕ}
    (hv₁ : v₁ < N) (hv₂ : v₂ < N) (ht₁ : t₁ < 2 * k) (ht₂ : t₂ < 2 * k)
    (heq : N + 2 * k * (u₁ * N + v₁) + t₁ = N + 2 * k * (u₂ * N + v₂) + t₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ t₁ = t₂ := by
  have hk0 : 0 < 2 * k := by omega
  have hN0 : 0 < N := by omega
  have h1 : 2 * k * (u₁ * N + v₁) + t₁ = 2 * k * (u₂ * N + v₂) + t₂ := by omega
  have ht : t₁ = t₂ := by
    have hm := congrArg (· % (2 * k)) h1
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt ht₁, Nat.mod_eq_of_lt ht₂] at hm
    exact hm
  have huv : u₁ * N + v₁ = u₂ * N + v₂ :=
    Nat.eq_of_mul_eq_mul_left hk0 (by omega)
  have hv : v₁ = v₂ := by
    have hm := congrArg (· % N) huv
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt hv₁, Nat.mod_eq_of_lt hv₂] at hm
    exact hm
  have hu : u₁ = u₂ :=
    Nat.eq_of_mul_eq_mul_right hN0 (by omega)
  exact ⟨hu, hv, ht⟩

lemma nodup_append_of {α : Type} {l₁ l₂ : List α}
    (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hdisj : ∀ x ∈ l₁, x ∉ l₂) :
    (l₁ ++ l₂).Nodup := by
  rw [List.nodup_append]
  exact ⟨h1, h2, fun x hx y hy hxy => hdisj x hx (hxy ▸ hy)⟩

lemma nodup_flatMap_of {α β : Type} {l : List α} {f : α → List β}
    (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons]
    refine nodup_append_of (hf a (by simp))
      (ih hl.2 (fun b hb => hf b (by simp [hb]))
        (fun b hb c hc hbc => hdisj b (by simp [hb]) c (by simp [hc]) hbc)) ?_
    intro x hx hmem
    rw [List.mem_flatMap] at hmem
    obtain ⟨b, hb, hxb⟩ := hmem
    exact hdisj a (by simp) b (by simp [hb]) (fun h => hl.1 (h ▸ hb)) x hx hxb

lemma lt_len_of_getElem?_eq_some {α : Type} {l : List α} {i : ℕ} {x : α}
    (h : (l)[i]? = some x) : i < l.length := by
  by_contra hge
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

lemma getElem?_clause_append_eq {c : Clause} {a : Literal} {j : ℕ} (hj : j ≤ c.length) :
    (c ++ [a])[j]? = some ((c ++ [a]).getD j (0, false)) := by
  rw [List.getD_eq_getElem?_getD]
  have hlt : j < (c ++ [a]).length := by simp; omega
  rw [List.getElem?_eq_getElem hlt]
  rfl

lemma getElem?_of_lt_clause {c : Clause} {a : Literal} {j : ℕ} (hj : j < c.length) :
    (c)[j]? = some ((c ++ [a]).getD j (0, false)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  rfl

lemma getD_append_eq_last {c : Clause} {a : Literal} :
    (c ++ [a]).getD c.length (0, false) = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma bool_beq_iff (t : ℕ) (b : Bool) :
    (((t % 2 == 1) == b) = true) ↔ ((t % 2 = 1) ↔ b = true) := by
  cases b <;> simp

end PEqualNP.Outside.L_meta_497_aux

theorem PEqualNP.Outside.L_meta_497 : ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff he_lt he_inj he_occ num hnum_var hnum_fresh hnum_occ hnum_last
    H hH f hf TH hTH lit hlit inner hinner TL hTL
  have hnum_var_false : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      num (Sum.inl (z, false)) = 2 * e z := by
    intro z hz
    have h := hnum_var z hz false
    simpa using h
  have hnum_var_true : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      num (Sum.inl (z, true)) = 2 * e z + 1 := by
    intro z hz
    have h := hnum_var z hz true
    simpa using h
  have hnum_fresh_false : num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)) = 2 * E := by
    have h := hnum_fresh false
    simpa using h
  have hnum_fresh_true : num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) = 2 * E + 1 := by
    have h := hnum_fresh true
    simpa using h
  have hoff_lt : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → off i + j < E := by
    intro i j hi hj
    rw [hoff i, hE]
    exact PEqualNP.Outside.L_meta_497_aux.off_add_lt_encodeCNF φ hi hj
  have hoff_inj : ∀ i₁ i₂ j₁ j₂, i₁ < φ.length → i₂ < φ.length →
      j₁ ≤ (φ.getD i₁ []).length → j₂ ≤ (φ.getD i₂ []).length →
      off i₁ + j₁ = off i₂ + j₂ → i₁ = i₂ ∧ j₁ = j₂ := by
    intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ heq
    rw [hoff i₁, hoff i₂] at heq
    exact PEqualNP.Outside.L_meta_497_aux.off_add_inj φ hi₁ hi₂ hj₁ hj₂ heq
  have hmem_inner : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t < 2 * k, ((t % 2 = 1) ↔ b = true) ∧ x = N + 2 * k * (u * N + v) + t := by
    intro u v b x
    rw [hinner u v b]
    simp only [List.mem_map, List.mem_filter, List.mem_range,
      PEqualNP.Outside.L_meta_497_aux.bool_beq_iff]
    constructor
    · rintro ⟨t, ⟨ht, hb⟩, rfl⟩
      exact ⟨t, ht, hb, rfl⟩
    · rintro ⟨t, ht, hb, rfl⟩
      exact ⟨t, ⟨ht, hb⟩, rfl⟩
  have hinner_nodup : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner u v b]
    refine List.Nodup.map (fun t₁ t₂ h => by omega) ?_
    exact List.Nodup.filter _ List.nodup_range
  have hlit_var : ∀ i j, i < φ.length → j < (φ.getD i []).length →
      (lit i j).1 ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ := by
    intro i j hi hj
    have hget := PEqualNP.Outside.L_meta_497_aux.getElem?_of_lt_clause
      (a := (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) hj
    rw [← hlit i j] at hget
    exact PEqualNP.Outside.L_meta_497_aux.mem_vars_of_getElem? hi hget
  have hlit_last : ∀ i, lit i (φ.getD i []).length = (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true) := by
    intro i
    rw [hlit i]
    exact PEqualNP.Outside.L_meta_497_aux.getD_append_eq_last
  have hnum_lit_lt : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inl (lit i j)) < 2 * (E + 1) := by
    intro i j hi hj
    by_cases hlt : j < (φ.getD i []).length
    · have hv := hlit_var i j hi hlt
      have he := he_lt _ hv
      have hn := hnum_var (lit i j).1 hv (lit i j).2
      simp only [Prod.mk.eta] at hn
      split_ifs at hn <;> omega
    · have heq : j = (φ.getD i []).length := by omega
      subst heq
      rw [hlit_last i, hnum_fresh_true]
      omega
  have hTH_var : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool,
      TH (num (Sum.inl (z, b))) ↔ b = true := by
    intro z hz b
    cases b
    · rw [hnum_var_false z hz, hTH]
      simp only [Bool.false_eq_true, iff_false]
      rintro (⟨z', hz', heq⟩ | heq | ⟨i, hi, j, hj, _, heq⟩ | heq)
      · omega
      · have := he_lt z hz; omega
      · have := he_lt z hz; omega
      · have := he_lt z hz; omega
    · rw [hnum_var_true z hz, hTH]
      simp only [iff_true]
      exact Or.inl ⟨z, hz, rfl⟩
  have hTH_fresh : ∀ b : Bool,
      TH (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b))) ↔ b = true := by
    intro b
    cases b
    · rw [hnum_fresh_false, hTH]
      simp only [Bool.false_eq_true, iff_false]
      rintro (⟨z', hz', heq⟩ | heq | ⟨i, hi, j, hj, _, heq⟩ | heq)
      · omega
      · omega
      · omega
      · omega
    · rw [hnum_fresh_true, hTH]
      simp
  have hTH_occ : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (num (Sum.inr (i, j))) ↔ j ≠ f i) := by
    intro i j hi hj
    rw [hnum_occ i j hi hj, hTH]
    constructor
    · rintro (⟨z', hz', heq⟩ | heq | ⟨i', hi', j', hj', hne, heq⟩ | heq)
      · have := he_lt z' hz'; omega
      · omega
      · have hij := hoff_inj i i' j j' hi hi' hj hj' (by omega)
        rcases hij with ⟨rfl, rfl⟩
        exact hne
      · have := hoff_lt i j hi hj; omega
    · intro hne
      exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hne, rfl⟩))
  have hTH_lit : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2 = true) := by
    intro i j hi hj
    by_cases hlt : j < (φ.getD i []).length
    · have hv := hlit_var i j hi hlt
      have h1 := hTH_var (lit i j).1 hv (lit i j).2
      simpa using h1
    · have heq : j = (φ.getD i []).length := by omega
      subst heq
      rw [hlit_last i]
      exact hTH_fresh true
  let block : ℕ → ℕ → List ℕ := fun i j =>
    inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
    ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l =>
      inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++
    (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
      inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
    else []) ++
    (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
    (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
      [num (Sum.inl ((lit i j).1, true))]
    else [])
  let mainList : List ℕ :=
    (List.range φ.length).flatMap (fun i =>
      (List.range ((φ.getD i []).length + 1)).flatMap (fun j => block i j))
  let tailList : List ℕ :=
    inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)))
      (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++
    inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)))
      (num (Sum.inr (φ.length, 0))) false ++
    [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]
  have hTL_eq : TL = mainList ++ tailList := hTL
  have hblock_key : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      ∀ x ∈ block i j,
        (x < 2 * E ∧ x = 2 * (off i + j) + 1) ∨
        (2 * (E + 1) ≤ x ∧ x < 3 * E + 2 ∧ x = 2 * (E + 1) + off i + j) ∨
        (∃ u v t, u < N ∧ v < N ∧ t < 2 * k ∧ x = N + 2 * k * (u * N + v) + t ∧
          ((u < 2 * (E + 1) ∧ v = 2 * (E + 1) + off i + j ∧ 2 * (E + 1) ≤ v ∧ v < 3 * E + 2) ∨
           (u = 2 * (E + 1) + off i + j ∧ 2 * (E + 1) ≤ u ∧ u < 3 * E + 2 ∧ 2 * (E + 1) ≤ v ∧ v < 3 * E + 2) ∨
           (u = 2 * (off i + j) ∧ v = 2 * (off i + j) + 1 ∧ v < 2 * E))) := by
    intro i j hi hj x hx
    have hoij := hoff_lt i j hi hj
    simp only [block, List.mem_append] at hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · rw [hmem_inner] at hx
      obtain ⟨t, ht, _, rfl⟩ := hx
      have hu := hnum_lit_lt i j hi hj
      have hv := hnum_occ i j hi hj
      exact Or.inr (Or.inr ⟨num (Sum.inl (lit i j)), num (Sum.inr (i, j)), t,
        by omega, by omega, ht, rfl, Or.inl ⟨hu, hv, by omega, by omega⟩⟩)
    · rw [List.mem_flatMap] at hx
      obtain ⟨l, hl, hx⟩ := hx
      rw [List.mem_filter, List.mem_range] at hl
      have hlj : l ≤ (φ.getD i []).length := by omega
      have hoil := hoff_lt i l hi hlj
      rw [hmem_inner] at hx
      obtain ⟨t, ht, _, rfl⟩ := hx
      have hu := hnum_occ i j hi hj
      have hv := hnum_occ i l hi hlj
      exact Or.inr (Or.inr ⟨num (Sum.inr (i, j)), num (Sum.inr (i, l)), t,
        by omega, by omega, ht, rfl, Or.inr (Or.inl ⟨hu, by omega, by omega, by omega, by omega⟩)⟩)
    · split_ifs at hx with hcond
      · rcases hcond with ⟨hlt, hoff_e⟩
        have hv := hlit_var i j hi hlt
        rw [hmem_inner] at hx
        obtain ⟨t, ht, _, rfl⟩ := hx
        have hu := hnum_var_false (lit i j).1 hv
        have hvv := hnum_var_true (lit i j).1 hv
        exact Or.inr (Or.inr ⟨num (Sum.inl ((lit i j).1, false)), num (Sum.inl ((lit i j).1, true)), t,
          by omega, by omega, ht, rfl, Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)⟩)
      · simp at hx
    · split_ifs at hx with hne
      · simp only [List.mem_singleton] at hx
        rw [hx, hnum_occ i j hi hj]
        exact Or.inr (Or.inl ⟨by omega, by omega, rfl⟩)
      · simp at hx
    · split_ifs at hx with hcond
      · rcases hcond with ⟨hlt, hoff_e⟩
        have hv := hlit_var i j hi hlt
        simp only [List.mem_singleton] at hx
        rw [hx, hnum_var_true (lit i j).1 hv]
        exact Or.inl ⟨by omega, by omega⟩
      · simp at hx
  have hblock_nodup : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → (block i j).Nodup := by
    intro i j hi hj
    have hoij := hoff_lt i j hi hj
    have hP1 : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2).Nodup :=
      hinner_nodup _ _ _
    have hP2 : (((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
        (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))).Nodup := by
      refine PEqualNP.Outside.L_meta_497_aux.nodup_flatMap_of
        (List.Nodup.filter _ List.nodup_range) (fun l _ => hinner_nodup _ _ _) ?_
      intro l₁ hl₁ l₂ hl₂ hne x hx₁ hx₂
      rw [List.mem_filter, List.mem_range] at hl₁ hl₂
      rw [hmem_inner] at hx₁ hx₂
      obtain ⟨t₁, ht₁, _, rfl⟩ := hx₁
      obtain ⟨t₂, ht₂, _, heq⟩ := hx₂
      have hv₁ := hnum_occ i l₁ hi (by omega)
      have hv₂ := hnum_occ i l₂ hi (by omega)
      have ho₁ := hoff_lt i l₁ hi (by omega)
      have ho₂ := hoff_lt i l₂ hi (by omega)
      have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode (by omega) (by omega) ht₁ ht₂ heq
      omega
    have hP3 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
      else []).Nodup := by
      split_ifs
      · exact hinner_nodup _ _ _
      · simp
    have hP4 : (if j ≠ f i then [num (Sum.inr (i, j))] else []).Nodup := by
      split_ifs <;> simp
    have hP5 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        [num (Sum.inl ((lit i j).1, true))] else []).Nodup := by
      split_ifs <;> simp
    have h12 : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l =>
          inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))).Nodup := by
      refine PEqualNP.Outside.L_meta_497_aux.nodup_append_of hP1 hP2 ?_
      intro x hx₁ hx₂
      rw [hmem_inner] at hx₁
      obtain ⟨t₁, ht₁, _, rfl⟩ := hx₁
      rw [List.mem_flatMap] at hx₂
      obtain ⟨l, hl, hx₂⟩ := hx₂
      rw [List.mem_filter, List.mem_range] at hl
      rw [hmem_inner] at hx₂
      obtain ⟨t₂, ht₂, _, heq⟩ := hx₂
      have hu₁ := hnum_lit_lt i j hi hj
      have hv₁ := hnum_occ i j hi hj
      have hu₂ := hnum_occ i j hi hj
      have hv₂ := hnum_occ i l hi (by omega)
      have ho₂ := hoff_lt i l hi (by omega)
      have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode (by omega) (by omega) ht₁ ht₂ heq
      omega
    have h123 : ((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l =>
          inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
        else [])).Nodup := by
      refine PEqualNP.Outside.L_meta_497_aux.nodup_append_of h12 hP3 ?_
      intro x hx₁ hx₂
      split_ifs at hx₂ with hcond
      · rcases hcond with ⟨hlt, hoff_e⟩
        have hv := hlit_var i j hi hlt
        rw [hmem_inner] at hx₂
        obtain ⟨t₂, ht₂, _, hx₂eq⟩ := hx₂
        have hvv₂ := hnum_var_true (lit i j).1 hv
        rw [List.mem_append] at hx₁
        rcases hx₁ with hx₁ | hx₁
        · rw [hmem_inner] at hx₁
          obtain ⟨t₁, ht₁, _, rfl⟩ := hx₁
          have hv₁ := hnum_occ i j hi hj
          have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode (by omega) (by omega) ht₁ ht₂ hx₂eq
          omega
        · rw [List.mem_flatMap] at hx₁
          obtain ⟨l, hl, hx₁⟩ := hx₁
          rw [List.mem_filter, List.mem_range] at hl
          rw [hmem_inner] at hx₁
          obtain ⟨t₁, ht₁, _, rfl⟩ := hx₁
          have hv₁ := hnum_occ i l hi (by omega)
          have ho₁ := hoff_lt i l hi (by omega)
          have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode (by omega) (by omega) ht₁ ht₂ hx₂eq
          omega
      · simp at hx₂
    have h123_ge : ∀ x ∈ (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l =>
          inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
        else []), N ≤ x := by
      intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · rw [hmem_inner] at hx; obtain ⟨t, _, _, rfl⟩ := hx; omega
      · rw [List.mem_flatMap] at hx; obtain ⟨l, _, hx⟩ := hx
        rw [hmem_inner] at hx; obtain ⟨t, _, _, rfl⟩ := hx; omega
      · split_ifs at hx
        · rw [hmem_inner] at hx; obtain ⟨t, _, _, rfl⟩ := hx; omega
        · simp at hx
    have h1234 : (((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l =>
          inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
        else [])) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else [])).Nodup := by
      refine PEqualNP.Outside.L_meta_497_aux.nodup_append_of h123 hP4 ?_
      intro x hx₁ hx₂
      have hge := h123_ge x hx₁
      split_ifs at hx₂
      · simp only [List.mem_singleton] at hx₂
        have hv := hnum_occ i j hi hj
        omega
      · simp at hx₂
    refine PEqualNP.Outside.L_meta_497_aux.nodup_append_of h1234 hP5 ?_
    intro x hx₁ hx₂
    split_ifs at hx₂ with hcond
    · rcases hcond with ⟨hlt, hoff_e⟩
      have hv := hlit_var i j hi hlt
      simp only [List.mem_singleton] at hx₂
      have hn5 := hnum_var_true (lit i j).1 hv
      rw [List.mem_append] at hx₁
      rcases hx₁ with hx₁ | hx₁
      · have hge := h123_ge x hx₁
        omega
      · split_ifs at hx₁
        · simp only [List.mem_singleton] at hx₁
          have hn4 := hnum_occ i j hi hj
          omega
        · simp at hx₁
    · simp at hx₂
  have hblock_disj : ∀ i₁ i₂ j₁ j₂, i₁ < φ.length → i₂ < φ.length →
      j₁ ≤ (φ.getD i₁ []).length → j₂ ≤ (φ.getD i₂ []).length →
      (i₁ ≠ i₂ ∨ j₁ ≠ j₂) → ∀ x ∈ block i₁ j₁, x ∉ block i₂ j₂ := by
    intro i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ hne x hx₁ hx₂
    have hk₁ := hblock_key i₁ j₁ hi₁ hj₁ x hx₁
    have hk₂ := hblock_key i₂ j₂ hi₂ hj₂ x hx₂
    have ho₁ := hoff_lt i₁ j₁ hi₁ hj₁
    have ho₂ := hoff_lt i₂ j₂ hi₂ hj₂
    have hcontra : off i₁ + j₁ = off i₂ + j₂ → False := by
      intro heq
      have hij := hoff_inj i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ heq
      rcases hne with hne | hne
      · exact hne hij.1
      · exact hne hij.2
    rcases hk₁ with ⟨h1a, h1b⟩ | ⟨h1a, h1b, h1c⟩ | ⟨u₁, v₁, t₁, hu₁, hv₁, ht₁, rfl, hc₁⟩ <;>
    rcases hk₂ with ⟨h2a, h2b⟩ | ⟨h2a, h2b, h2c⟩ | ⟨u₂, v₂, t₂, hu₂, hv₂, ht₂, heq, hc₂⟩
    · exact hcontra (by omega)
    · omega
    · omega
    · omega
    · exact hcontra (by omega)
    · omega
    · omega
    · omega
    · have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode hv₁ hv₂ ht₁ ht₂ heq
      rcases hdec with ⟨rfl, rfl, rfl⟩
      rcases hc₁ with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _, _⟩ <;>
      rcases hc₂ with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _, _⟩
      · exact hcontra (by omega)
      · omega
      · omega
      · omega
      · exact hcontra (by omega)
      · omega
      · omega
      · omega
      · exact hcontra (by omega)
  have hmain_nodup : mainList.Nodup := by
    refine PEqualNP.Outside.L_meta_497_aux.nodup_flatMap_of List.nodup_range ?_ ?_
    · intro i hi
      rw [List.mem_range] at hi
      refine PEqualNP.Outside.L_meta_497_aux.nodup_flatMap_of List.nodup_range
        (fun j hj => hblock_nodup i j hi (by rw [List.mem_range] at hj; omega)) ?_
      intro j₁ hj₁ j₂ hj₂ hne x hx₁ hx₂
      rw [List.mem_range] at hj₁ hj₂
      exact hblock_disj i i j₁ j₂ hi hi (by omega) (by omega) (Or.inr hne) x hx₁ hx₂
    · intro i₁ hi₁ i₂ hi₂ hne x hx₁ hx₂
      rw [List.mem_range] at hi₁ hi₂
      rw [List.mem_flatMap] at hx₁ hx₂
      obtain ⟨j₁, hj₁, hx₁⟩ := hx₁
      obtain ⟨j₂, hj₂, hx₂⟩ := hx₂
      rw [List.mem_range] at hj₁ hj₂
      exact hblock_disj i₁ i₂ j₁ j₂ hi₁ hi₂ (by omega) (by omega) (Or.inl hne) x hx₁ hx₂
  have htail_nodup : tailList.Nodup := by
    have hT12 : (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)))
        (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++
        inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)))
        (num (Sum.inr (φ.length, 0))) false).Nodup := by
      refine PEqualNP.Outside.L_meta_497_aux.nodup_append_of (hinner_nodup _ _ _) (hinner_nodup _ _ _) ?_
      intro x hx₁ hx₂
      rw [hmem_inner] at hx₁ hx₂
      obtain ⟨t₁, ht₁, _, rfl⟩ := hx₁
      obtain ⟨t₂, ht₂, _, heq⟩ := hx₂
      have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode (by omega) (by omega) ht₁ ht₂ heq
      omega
    have hT3 : ([num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)),
        num (Sum.inr (φ.length, 0))]).Nodup := by
      rw [List.nodup_cons]
      simp only [List.mem_singleton, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_self, and_true]
      omega
    refine PEqualNP.Outside.L_meta_497_aux.nodup_append_of hT12 hT3 ?_
    intro x hx₁ hx₂
    have hge : N ≤ x := by
      rw [List.mem_append] at hx₁
      rcases hx₁ with hx₁ | hx₁ <;>
        (rw [hmem_inner] at hx₁; obtain ⟨t, _, _, rfl⟩ := hx₁; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₂
    rcases hx₂ with rfl | rfl <;> omega
  have hmain_tail_disj : ∀ x ∈ mainList, x ∉ tailList := by
    intro x hx₁ hx₂
    rw [List.mem_flatMap] at hx₁
    obtain ⟨i, hi, hx₁⟩ := hx₁
    rw [List.mem_range] at hi
    rw [List.mem_flatMap] at hx₁
    obtain ⟨j, hj, hx₁⟩ := hx₁
    rw [List.mem_range] at hj
    have hk₁ := hblock_key i j hi (by omega) x hx₁
    simp only [tailList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx₂
    rcases hx₂ with (hx₂ | hx₂) | (rfl | rfl)
    · rw [hmem_inner] at hx₂
      obtain ⟨t₂, ht₂, _, heq⟩ := hx₂
      rcases hk₁ with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨u₁, v₁, t₁, hu₁, hv₁, ht₁, rfl, hc₁⟩
      · omega
      · omega
      · have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode hv₁ (by omega) ht₁ ht₂ heq
        rcases hdec with ⟨rfl, rfl, rfl⟩
        rcases hc₁ with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · rw [hmem_inner] at hx₂
      obtain ⟨t₂, ht₂, _, heq⟩ := hx₂
      rcases hk₁ with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨u₁, v₁, t₁, hu₁, hv₁, ht₁, rfl, hc₁⟩
      · omega
      · omega
      · have hdec := PEqualNP.Outside.L_meta_497_aux.sub_decode hv₁ (by omega) ht₁ ht₂ heq
        rcases hdec with ⟨rfl, rfl, rfl⟩
        rcases hc₁ with ⟨_, _, _, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · rcases hk₁ with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _, _, _, _, heqx, _⟩ <;> omega
    · rcases hk₁ with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _, _, _, _, heqx, _⟩ <;> omega
  constructor
  · rw [hTL_eq]
    exact PEqualNP.Outside.L_meta_497_aux.nodup_append_of hmain_nodup htail_nodup hmain_tail_disj
  · intro x
    rw [hTL_eq]
    constructor
    · intro hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [List.mem_flatMap] at hx
        obtain ⟨i, hi, hx⟩ := hx
        rw [List.mem_range] at hi
        rw [List.mem_flatMap] at hx
        obtain ⟨j, hj, hx⟩ := hx
        rw [List.mem_range] at hj
        have hj' : j ≤ (φ.getD i []).length := by omega
        have hoij := hoff_lt i j hi hj'
        simp only [block, List.mem_append] at hx
        rcases hx with (((hx | hx) | hx) | hx) | hx
        · rw [hmem_inner] at hx
          obtain ⟨t, ht, htb, rfl⟩ := hx
          have hu_lt := hnum_lit_lt i j hi hj'
          have hv_eq := hnum_occ i j hi hj'
          right
          refine ⟨⟨num (Sum.inl (lit i j)), by omega⟩, ⟨num (Sum.inr (i, j)), by omega⟩,
            by change num (Sum.inl (lit i j)) < num (Sum.inr (i, j)); omega, ?_,
            t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inl (lit i j), Sum.inr (i, j), ?_, rfl, rfl⟩
            change (PEqualNP.MetaComplexity.CoverPromise.clauseAt
              (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) i)[j]? = some (lit i j)
            rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_lt φ hi, hlit i j]
            exact PEqualNP.Outside.L_meta_497_aux.getElem?_clause_append_eq hj'
          · rw [hTH_lit i j hi hj']
            exact htb
        · rw [List.mem_flatMap] at hx
          obtain ⟨l, hl, hx⟩ := hx
          rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
          have hl' : l ≤ (φ.getD i []).length := by omega
          have hoil := hoff_lt i l hi hl'
          rw [hmem_inner] at hx
          obtain ⟨t, ht, htb, rfl⟩ := hx
          have hu_eq := hnum_occ i j hi hj'
          have hv_eq := hnum_occ i l hi hl'
          right
          refine ⟨⟨num (Sum.inr (i, j)), by omega⟩, ⟨num (Sum.inr (i, l)), by omega⟩,
            by change num (Sum.inr (i, j)) < num (Sum.inr (i, l)); omega, ?_,
            t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inr (i, j), Sum.inr (i, l), ?_, rfl, rfl⟩
            change i = i ∧ j ≠ l ∧
              j < (PEqualNP.MetaComplexity.CoverPromise.clauseAt
                (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) i).length ∧
              l < (PEqualNP.MetaComplexity.CoverPromise.clauseAt
                (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) i).length
            rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_lt φ hi]
            simp only [List.length_append, List.length_singleton]
            exact ⟨trivial, by omega, by omega, by omega⟩
          · rw [hTH_occ i j hi hj']
            simpa [decide_eq_true_eq] using htb
        · split_ifs at hx with hcond
          · rcases hcond with ⟨hlt, _⟩
            have hv := hlit_var i j hi hlt
            have hez := he_lt _ hv
            rw [hmem_inner] at hx
            obtain ⟨t, ht, htb, rfl⟩ := hx
            have hu_eq := hnum_var_false (lit i j).1 hv
            have hv_eq := hnum_var_true (lit i j).1 hv
            right
            refine ⟨⟨num (Sum.inl ((lit i j).1, false)), by omega⟩,
              ⟨num (Sum.inl ((lit i j).1, true)), by omega⟩,
              by change num (Sum.inl ((lit i j).1, false)) < num (Sum.inl ((lit i j).1, true)); omega,
              ?_, t, ht, rfl, ?_⟩
            · rw [hH]
              refine ⟨Sum.inl ((lit i j).1, false), Sum.inl ((lit i j).1, true), ?_, rfl, rfl⟩
              change (lit i j).1 = (lit i j).1 ∧ false ≠ true ∧
                (lit i j).1 ∈ PEqualNP.MetaComplexity.CoverPromise.vars
                  (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ)
              rw [PEqualNP.Outside.L_meta_497_aux.mem_vars_cvcFormula]
              exact ⟨rfl, by decide, Or.inl hv⟩
            · rw [hTH_var (lit i j).1 hv false]
              exact htb
          · simp at hx
        · split_ifs at hx with hne
          · simp only [List.mem_singleton] at hx
            subst hx
            left
            exact (hTH_occ i j hi hj').2 hne
          · simp at hx
        · split_ifs at hx with hcond
          · rcases hcond with ⟨hlt, _⟩
            have hv := hlit_var i j hi hlt
            simp only [List.mem_singleton] at hx
            subst hx
            left
            exact (hTH_var (lit i j).1 hv true).2 rfl
          · simp at hx
      · simp only [tailList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with (hx | hx) | (rfl | rfl)
        · rw [hmem_inner] at hx
          obtain ⟨t, ht, htb, rfl⟩ := hx
          right
          refine ⟨⟨num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)), by omega⟩,
            ⟨num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), by omega⟩,
            by change num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)) <
              num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)); omega,
            ?_, t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false),
              Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true), ?_, rfl, rfl⟩
            change PEqualNP.MetaComplexity.CoverPromise.fresh φ =
              PEqualNP.MetaComplexity.CoverPromise.fresh φ ∧ false ≠ true ∧
              PEqualNP.MetaComplexity.CoverPromise.fresh φ ∈
                PEqualNP.MetaComplexity.CoverPromise.vars
                  (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ)
            rw [PEqualNP.Outside.L_meta_497_aux.mem_vars_cvcFormula]
            exact ⟨rfl, by decide, Or.inr rfl⟩
          · rw [hTH_fresh false]
            exact htb
        · rw [hmem_inner] at hx
          obtain ⟨t, ht, htb, rfl⟩ := hx
          right
          refine ⟨⟨num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)), by omega⟩,
            ⟨num (Sum.inr (φ.length, 0)), by omega⟩,
            by change num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)) <
              num (Sum.inr (φ.length, 0)); omega,
            ?_, t, ht, rfl, ?_⟩
          · rw [hH]
            refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false),
              Sum.inr (φ.length, 0), ?_, rfl, rfl⟩
            change (PEqualNP.MetaComplexity.CoverPromise.clauseAt
              (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) φ.length)[0]? =
              some (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)
            rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_eq φ]
            rfl
          · rw [hTH_fresh false]
            exact htb
        · left
          exact (hTH_fresh true).2 rfl
        · left
          rw [hnum_last, hTH]
          exact Or.inr (Or.inr (Or.inr rfl))
    · intro hx
      rcases hx with hth | ⟨u, v, huv, hadj, t, ht, rfl, htTH⟩
      · rw [hTH] at hth
        rcases hth with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
        · obtain ⟨l, hflat, hl1⟩ := he_occ z hz
          obtain ⟨i, hi, j, hj, he_eq, hget⟩ := PEqualNP.Outside.L_meta_497_aux.flatMap_opt_eq φ (e z) l hflat
          have hlit_eq : lit i j = l := by
            have h1 := PEqualNP.Outside.L_meta_497_aux.getElem?_of_lt_clause
              (a := (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) hj
            rw [← hlit i j] at h1
            rw [hget] at h1
            exact Option.some.inj h1.symm
          have hcond : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 := by
            refine ⟨hj, ?_⟩
            rw [hlit_eq, hl1, hoff i]
            exact he_eq.symm
          rw [List.mem_append]
          left
          rw [List.mem_flatMap]
          refine ⟨i, List.mem_range.2 hi, ?_⟩
          rw [List.mem_flatMap]
          refine ⟨j, List.mem_range.2 (by omega), ?_⟩
          simp only [block, List.mem_append]
          right
          simp only [hcond, and_self, ↓reduceIte, List.mem_singleton, hlit_eq, hl1, hnum_var_true z hz]
        · rw [List.mem_append]
          right
          simp only [tailList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          right
          left
          rw [hnum_fresh_true]
        · rw [List.mem_append]
          left
          rw [List.mem_flatMap]
          refine ⟨i, List.mem_range.2 hi, ?_⟩
          rw [List.mem_flatMap]
          refine ⟨j, List.mem_range.2 (by omega), ?_⟩
          simp only [block, List.mem_append]
          left
          right
          simp [hne, hnum_occ i j hi hj]
        · rw [List.mem_append]
          right
          simp only [tailList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          right
          right
          rw [hnum_last]
      · obtain ⟨a, b, hab, ha, hb⟩ := (hH u v).1 hadj
        have huv' : num a < num b := by
          have : u.val < v.val := huv
          omega
        rcases a with ⟨za, ba⟩ | ⟨ia, ja⟩ <;> rcases b with ⟨zb, bb⟩ | ⟨ib, jb⟩
        · change za = zb ∧ ba ≠ bb ∧ za ∈ PEqualNP.MetaComplexity.CoverPromise.vars
            (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) at hab
          rcases hab with ⟨rfl, hbab, hzv⟩
          rw [PEqualNP.Outside.L_meta_497_aux.mem_vars_cvcFormula] at hzv
          rcases hzv with hzv | rfl
          · have hba : ba = false := by
              cases ba
              · rfl
              · cases bb
                · have hna := hnum_var_true za hzv
                  have hnb := hnum_var_false za hzv
                  omega
                · exact absurd rfl hbab
            have hbb : bb = true := by
              cases bb
              · exact absurd hba hbab
              · rfl
            subst hba
            subst hbb
            obtain ⟨l, hflat, hl1⟩ := he_occ za hzv
            obtain ⟨i, hi, j, hj, he_eq, hget⟩ :=
              PEqualNP.Outside.L_meta_497_aux.flatMap_opt_eq φ (e za) l hflat
            have hlit_eq : lit i j = l := by
              have h1 := PEqualNP.Outside.L_meta_497_aux.getElem?_of_lt_clause
                (a := (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) hj
              rw [← hlit i j] at h1
              rw [hget] at h1
              exact Option.some.inj h1.symm
            have hcond : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 := by
              refine ⟨hj, ?_⟩
              rw [hlit_eq, hl1, hoff i]
              exact he_eq.symm
            rw [List.mem_append]
            left
            rw [List.mem_flatMap]
            refine ⟨i, List.mem_range.2 hi, ?_⟩
            rw [List.mem_flatMap]
            refine ⟨j, List.mem_range.2 (by omega), ?_⟩
            simp only [block, List.mem_append]
            left
            left
            right
            simp only [hcond, and_self, ↓reduceIte]
            rw [hlit_eq, hl1, hmem_inner]
            refine ⟨t, ht, ?_, by rw [ha, hb]⟩
            rw [← ha, hTH_var za hzv false] at htTH
            exact htTH
          · have hba : ba = false := by
              cases ba
              · rfl
              · cases bb
                · omega
                · exact absurd rfl hbab
            have hbb : bb = true := by
              cases bb
              · exact absurd hba hbab
              · rfl
            subst hba
            subst hbb
            rw [List.mem_append]
            right
            simp only [tailList, List.mem_append]
            left
            left
            rw [hmem_inner]
            refine ⟨t, ht, ?_, by rw [ha, hb]⟩
            rw [← ha, hTH_fresh false] at htTH
            exact htTH
        · change (PEqualNP.MetaComplexity.CoverPromise.clauseAt
            (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) ib)[jb]? = some (za, ba) at hab
          by_cases hib : ib < φ.length
          · rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_lt φ hib] at hab
            have hjb : jb ≤ (φ.getD ib []).length := by
              have hlt := PEqualNP.Outside.L_meta_497_aux.lt_len_of_getElem?_eq_some hab
              simp only [List.length_append, List.length_singleton] at hlt
              omega
            have hlit_eq : lit ib jb = (za, ba) := by
              have h1 := PEqualNP.Outside.L_meta_497_aux.getElem?_clause_append_eq
                (c := φ.getD ib []) (a := (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) hjb
              rw [← hlit ib jb] at h1
              rw [hab] at h1
              exact Option.some.inj h1.symm
            rw [List.mem_append]
            left
            rw [List.mem_flatMap]
            refine ⟨ib, List.mem_range.2 hib, ?_⟩
            rw [List.mem_flatMap]
            refine ⟨jb, List.mem_range.2 (by omega), ?_⟩
            simp only [block, List.mem_append]
            left
            left
            left
            left
            rw [hmem_inner]
            refine ⟨t, ht, ?_, by rw [hlit_eq, ha, hb]⟩
            rw [← ha, ← hlit_eq, hTH_lit ib jb hib hjb] at htTH
            exact htTH
          · by_cases hib_eq : ib = φ.length
            · subst hib_eq
              rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_eq φ] at hab
              have hjb0 : jb = 0 := by
                have hlt := PEqualNP.Outside.L_meta_497_aux.lt_len_of_getElem?_eq_some hab
                simp at hlt
                omega
              subst hjb0
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hab
              have hpair : (za, ba) = (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false) := hab.symm
              rw [List.mem_append]
              right
              simp only [tailList, List.mem_append]
              left
              right
              rw [hmem_inner]
              refine ⟨t, ht, ?_, by rw [← hpair, ha, hb]⟩
              rw [← ha, hpair, hTH_fresh false] at htTH
              exact htTH
            · rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_gt φ (by omega)] at hab
              simp at hab
        · change (PEqualNP.MetaComplexity.CoverPromise.clauseAt
            (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) ia)[ja]? = some (zb, bb) at hab
          by_cases hia : ia < φ.length
          · rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_lt φ hia] at hab
            have hja : ja ≤ (φ.getD ia []).length := by
              have hlt := PEqualNP.Outside.L_meta_497_aux.lt_len_of_getElem?_eq_some hab
              simp only [List.length_append, List.length_singleton] at hlt
              omega
            have hlit_eq : lit ia ja = (zb, bb) := by
              have h1 := PEqualNP.Outside.L_meta_497_aux.getElem?_clause_append_eq
                (c := φ.getD ia []) (a := (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) hja
              rw [← hlit ia ja] at h1
              rw [hab] at h1
              exact Option.some.inj h1.symm
            have hna := hnum_occ ia ja hia hja
            have hnb := hnum_lit_lt ia ja hia hja
            rw [hlit_eq] at hnb
            omega
          · by_cases hia_eq : ia = φ.length
            · subst hia_eq
              rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_eq φ] at hab
              have hja0 : ja = 0 := by
                have hlt := PEqualNP.Outside.L_meta_497_aux.lt_len_of_getElem?_eq_some hab
                simp at hlt
                omega
              subst hja0
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hab
              have hpair : (zb, bb) = (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false) := hab.symm
              rw [hpair] at huv'
              omega
            · rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_gt φ (by omega)] at hab
              simp at hab
        · change ia = ib ∧ ja ≠ jb ∧
            ja < (PEqualNP.MetaComplexity.CoverPromise.clauseAt
              (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) ia).length ∧
            jb < (PEqualNP.MetaComplexity.CoverPromise.clauseAt
              (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) ia).length at hab
          rcases hab with ⟨rfl, hne, hja, hjb⟩
          by_cases hia : ia < φ.length
          · rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_lt φ hia] at hja hjb
            simp only [List.length_append, List.length_singleton] at hja hjb
            have hna := hnum_occ ia ja hia (by omega)
            have hnb := hnum_occ ia jb hia (by omega)
            have hjlt : ja < jb := by omega
            rw [List.mem_append]
            left
            rw [List.mem_flatMap]
            refine ⟨ia, List.mem_range.2 hia, ?_⟩
            rw [List.mem_flatMap]
            refine ⟨ja, List.mem_range.2 (by omega), ?_⟩
            simp only [block, List.mem_append]
            left
            left
            left
            right
            rw [List.mem_flatMap]
            refine ⟨jb, ?_, ?_⟩
            · rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
              exact ⟨by omega, hjlt⟩
            · rw [hmem_inner]
              refine ⟨t, ht, ?_, by rw [ha, hb]⟩
              rw [← ha, hTH_occ ia ja hia (by omega)] at htTH
              simpa [decide_eq_true_eq] using htTH
          · by_cases hia_eq : ia = φ.length
            · subst hia_eq
              rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_eq φ] at hja hjb
              simp at hja hjb
              omega
            · rw [PEqualNP.Outside.L_meta_497_aux.clauseAt_cvcFormula_gt φ (by omega)] at hja
              simp at hja
