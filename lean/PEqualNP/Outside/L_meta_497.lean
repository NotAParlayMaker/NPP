import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta497

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem divmod {K a a' t t' : ℕ} (ht : t < K) (ht' : t' < K) (h : K * a + t = K * a' + t') :
    a = a' ∧ t = t' := by
  have ha : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hlt)
      rw [Nat.mul_succ] at this
      omega
    · exact heq
    · have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hgt)
      rw [Nat.mul_succ] at this
      omega
  subst ha
  exact ⟨rfl, by omega⟩

theorem dec {N k u v t u' v' t' : ℕ} (ht : t < 2 * k) (ht' : t' < 2 * k) (hv : v < N)
    (hv' : v' < N) (h : N + 2 * k * (u * N + v) + t = N + 2 * k * (u' * N + v') + t') :
    u = u' ∧ v = v' ∧ t = t' := by
  obtain ⟨h1, h2⟩ := divmod ht ht'
    (by omega : 2 * k * (u * N + v) + t = 2 * k * (u' * N + v') + t')
  have h1' : N * u + v = N * u' + v' := by
    rw [Nat.mul_comm N u, Nat.mul_comm N u']
    exact h1
  obtain ⟨h3, h4⟩ := divmod hv hv' h1'
  exact ⟨h3, h4, h2⟩

/-- The offsets of the clauses in the list written clause by clause. -/
def offs (φ : CNF) (i : ℕ) : ℕ := ((φ.take i).map (fun c => c.length + 1)).sum

theorem offs_succ (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    offs φ (i + 1) = offs φ i + ((φ.getD i []).length + 1) := by
  rw [offs, offs, List.take_add_one, List.getElem?_eq_getElem hi]
  simp [List.getD, List.getElem?_eq_getElem hi]
  rw [List.take_add_one]
  simp [hi]

theorem offs_le_succ (φ : CNF) (i : ℕ) : offs φ i ≤ offs φ (i + 1) := by
  by_cases hi : i < φ.length
  · rw [offs_succ φ i hi]
    omega
  · have h1 : φ.length ≤ i := Nat.le_of_not_lt hi
    simp [offs, List.take_of_length_le h1, List.take_of_length_le (Nat.le_succ_of_le h1)]

theorem offs_mono (φ : CNF) {i i' : ℕ} (h : i ≤ i') : offs φ i ≤ offs φ i' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (offs_le_succ φ _)

theorem offs_lt (φ : CNF) {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
    offs φ i + j < offs φ φ.length := by
  have h1 := offs_succ φ i hi
  have h2 := offs_mono φ (show i + 1 ≤ φ.length by omega)
  omega

theorem offs_inj (φ : CNF) {i j i' j' : ℕ} (hi : i < φ.length) (hi' : i' < φ.length)
    (hj : j ≤ (φ.getD i []).length) (hj' : j' ≤ (φ.getD i' []).length)
    (h : offs φ i + j = offs φ i' + j') : i = i' ∧ j = j' := by
  have hii : i = i' := by
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · have h1 := offs_succ φ i hi
      have h2 := offs_mono φ (show i + 1 ≤ i' by omega)
      omega
    · exact heq
    · have h1 := offs_succ φ i' hi'
      have h2 := offs_mono φ (show i' + 1 ≤ i by omega)
      omega
  subst hii
  exact ⟨rfl, by omega⟩

theorem len_encodeClause (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  have h : ∀ c : Clause, c.length ≤ (c.flatMap encodeLiteral).length := by
    intro c
    induction c with
    | nil => simp
    | cons a c ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : 1 ≤ (encodeLiteral a).length := by simp [encodeLiteral]
      omega
  have := h c
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  omega

theorem offs_le_enc (φ : CNF) : offs φ φ.length ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [offs]
  | cons c φ ih =>
    have h1 := len_encodeClause c
    simp only [offs, List.take_length, encodeCNF, List.map_cons, List.sum_cons,
      List.flatMap_cons, List.length_append] at ih ⊢
    omega

theorem flat_some (φ : CNF) (p : ℕ) (l : Literal)
    (h : (φ.flatMap (fun c => c.map some ++ [none]))[p]? = some (some l)) :
    ∃ i, i < φ.length ∧ ∃ j, j < (φ.getD i []).length ∧ p = offs φ i + j ∧
      (φ.getD i [])[j]? = some l := by
  induction φ generalizing p with
  | nil => simp at h
  | cons c φ ih =>
    rw [List.flatMap_cons] at h
    by_cases hp : p < c.length
    · refine ⟨0, by simp, p, by simpa using hp, by simp [offs], ?_⟩
      rw [List.getElem?_append_left (by simp; omega)] at h
      rw [List.getElem?_append_left (by simpa using hp)] at h
      simpa using h
    · by_cases hp2 : p = c.length
      · subst hp2
        rw [List.getElem?_append_left (by simp)] at h
        simp at h
      · have hp3 : c.length + 1 ≤ p := by omega
        rw [List.getElem?_append_right (by simpa using hp3)] at h
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          at h
        obtain ⟨i, hi, j, hj, hpj, hl⟩ := ih (p - (c.length + 0 + 1)) h
        refine ⟨i + 1, by simpa using hi, j, by simpa using hj, ?_, by simpa using hl⟩
        have : offs (c :: φ) (i + 1) = c.length + 1 + offs φ i := by
          simp [offs]
        omega

theorem mem_vars (φ : CNF) (z : ℕ) : z ∈ vars φ ↔ ∃ c ∈ φ, ∃ l ∈ c, l.1 = z := by
  simp [vars]

theorem clauseAt_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    clauseAt (cvcFormula φ) i = φ.getD i [] ++ [(fresh φ, true)] := by
  simp [clauseAt, cvcFormula, List.getD, List.getElem?_append_left, hi]

theorem clauseAt_eq (φ : CNF) :
    clauseAt (cvcFormula φ) φ.length = [(fresh φ, false)] := by
  simp [clauseAt, cvcFormula, List.getD]

theorem clauseAt_gt (φ : CNF) {i : ℕ} (hi : φ.length < i) :
    clauseAt (cvcFormula φ) i = [] := by
  unfold clauseAt
  rw [List.getD_eq_default]
  simp [cvcFormula]
  omega

theorem nodup_flatMap_of_key {α β : Type} (l : List β) (g : β → List α) (hl : l.Nodup)
    (hg : ∀ b ∈ l, (g b).Nodup)
    (key : ∀ b ∈ l, ∀ b' ∈ l, ∀ x, x ∈ g b → x ∈ g b' → b = b') : (l.flatMap g).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hg, hl.pairwise_of_forall_ne ?_⟩
  intro a ha b hb hne x hx hx'
  exact hne (key a ha b hb x hx hx')

end PEqualNP.Outside.Meta497

namespace PEqualNP.Outside.Meta497

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem mem_vars_cvc (φ : CNF) (z : ℕ) :
    z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
  simp only [mem_vars, cvcFormula, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨c, (⟨c0, hc0, rfl⟩ | rfl), l, hl, rfl⟩
    · rcases List.mem_append.mp hl with h | h
      · exact Or.inl ⟨c0, hc0, l, h, rfl⟩
      · right
        rw [List.mem_singleton.mp h]
    · right
      rw [List.mem_singleton.mp hl]
  · rintro (⟨c, hc, l, hl, rfl⟩ | rfl)
    · exact ⟨c ++ [(fresh φ, true)], Or.inl ⟨c, hc, rfl⟩, l, List.mem_append_left _ hl, rfl⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), by simp, rfl⟩

theorem getD_mem (φ : CNF) {i : ℕ} (hi : i < φ.length) : φ.getD i [] ∈ φ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem getD_append_mem (C : Clause) (a d : Literal) {j : ℕ} (hj : j < C.length) :
    (C ++ [a]).getD j d ∈ C := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

theorem getD_append_get (C : Clause) (a d : Literal) {j : ℕ} (hj : j ≤ C.length) :
    (C ++ [a])[j]? = some ((C ++ [a]).getD j d) := by
  have hlen : j < (C ++ [a]).length := by
    simp
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  rfl

theorem getD_append_last (C : Clause) (a d : Literal) : (C ++ [a]).getD C.length d = a := by
  rw [List.getD_eq_getElem?_getD]
  simp

theorem par (t : ℕ) (b : Bool) : ((t % 2 == 1) == b) = true ↔ (t % 2 = 1 ↔ b = true) := by
  cases b <;> simp

theorem nodup_append_of {α : Type} {l₁ l₂ : List α} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (h : ∀ x, x ∈ l₁ → x ∈ l₂ → False) : (l₁ ++ l₂).Nodup :=
  List.Nodup.append h1 h2 (fun x hx hx' => h x hx hx')

/-- What a member of the cell with code `c` looks like. -/
def Q (E N k c x : ℕ) : Prop :=
  x = 2 * (E + 1) + c ∨ x = 2 * c + 1 ∨
    ∃ u v t, t < 2 * k ∧ v < N ∧ x = N + 2 * k * (u * N + v) + t ∧
      ((u ≤ 2 * E + 1 ∧ v = 2 * (E + 1) + c) ∨ (u = 2 * (E + 1) + c ∧ u < v) ∨
        (u = 2 * c ∧ v = 2 * c + 1))

theorem Q_inj {E N k c c' x : ℕ} (hN : N = 3 * (E + 1)) (hc : c < E) (hc' : c' < E)
    (h : Q E N k c x) (h' : Q E N k c' x) : c = c' := by
  rcases h with rfl | rfl | ⟨u, v, t, ht, hv, rfl, h⟩
  · rcases h' with h' | h' | ⟨u', v', t', ht', hv', h', hh⟩ <;> omega
  · rcases h' with h' | h' | ⟨u', v', t', ht', hv', h', hh⟩ <;> omega
  · rcases h' with h' | h' | ⟨u', v', t', ht', hv', h', hh⟩
    · omega
    · omega
    · obtain ⟨rfl, rfl, rfl⟩ := dec ht ht' hv hv' h'
      rcases h with h | h | h <;> rcases hh with hh | hh | hh <;> omega

theorem Q_tail {E N k c x : ℕ} (hN : N = 3 * (E + 1)) (hc : c < E) (h : Q E N k c x)
    (h' : (∃ t, t < 2 * k ∧ ¬ t % 2 = 1 ∧ x = N + 2 * k * (2 * E * N + (2 * E + 1)) + t) ∨
      (∃ t, t < 2 * k ∧ ¬ t % 2 = 1 ∧ x = N + 2 * k * (2 * E * N + (3 * E + 2)) + t) ∨
      x = 2 * E + 1 ∨ x = 3 * E + 2) : False := by
  rcases h with rfl | rfl | ⟨u, v, t, ht, hv, rfl, h⟩
  · rcases h' with ⟨t', ht', -, h'⟩ | ⟨t', ht', -, h'⟩ | h' | h' <;> omega
  · rcases h' with ⟨t', ht', -, h'⟩ | ⟨t', ht', -, h'⟩ | h' | h' <;> omega
  · rcases h' with ⟨t', ht', -, h'⟩ | ⟨t', ht', -, h'⟩ | h' | h'
    · obtain ⟨rfl, rfl, rfl⟩ := dec ht ht' hv (by omega) h'
      rcases h with h | h | h <;> omega
    · obtain ⟨rfl, rfl, rfl⟩ := dec ht ht' hv (by omega) h'
      rcases h with h | h | h <;> omega
    · omega
    · omega

theorem getD_append_of_get (C : Clause) (a d l : Literal) {j : ℕ} (h : C[j]? = some l) :
    (C ++ [a]).getD j d = l := by
  obtain ⟨hj, hl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, h]
  rfl

end PEqualNP.Outside.Meta497

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_497 : ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff he heinj hedes num hnumL hnumY hnumO hnumLast H hH f hf TH
    hTH lit hlit inner hinner TL hTL
  have hoffeq : off = PEqualNP.Outside.Meta497.offs φ := funext hoff
  subst hoffeq
  have hoffn : PEqualNP.Outside.Meta497.offs φ φ.length ≤ E := by
    rw [hE]
    exact PEqualNP.Outside.Meta497.offs_le_enc φ
  have hc : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      PEqualNP.Outside.Meta497.offs φ i + j < E := by
    intro i j hi hj
    have := PEqualNP.Outside.Meta497.offs_lt φ hi hj
    omega
  have hlitlt : ∀ i j, j < (φ.getD i []).length → lit i j ∈ φ.getD i [] := by
    intro i j hj
    rw [hlit]
    exact PEqualNP.Outside.Meta497.getD_append_mem _ _ _ hj
  have hlitvars : ∀ i j, i < φ.length → j < (φ.getD i []).length →
      (lit i j).1 ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ := by
    intro i j hi hj
    exact (PEqualNP.Outside.Meta497.mem_vars φ _).mpr
      ⟨_, PEqualNP.Outside.Meta497.getD_mem φ hi, _, hlitlt i j hj, rfl⟩
  have hlitlast : ∀ i, lit i (φ.getD i []).length =
      (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true) := by
    intro i
    rw [hlit]
    exact PEqualNP.Outside.Meta497.getD_append_last _ _ _
  have hlitget : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (PEqualNP.MetaComplexity.CoverPromise.clauseAt
        (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) i)[j]? = some (lit i j) := by
    intro i j hi hj
    rw [PEqualNP.Outside.Meta497.clauseAt_lt φ hi, hlit]
    exact PEqualNP.Outside.Meta497.getD_append_get _ _ _ hj
  have hTHlit : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool,
      (TH (2 * e z + (if b then 1 else 0)) ↔ b = true) := by
    intro z hz b
    have hez := he z hz
    rw [hTH]
    constructor
    · rintro (⟨z', hz', h⟩ | h | ⟨i, hi, j, hj, _, h⟩ | h)
      · cases b
        · simp at h
          omega
        · rfl
      · cases b <;> simp at h <;> omega
      · cases b <;> simp at h <;> omega
      · cases b <;> simp at h <;> omega
    · intro hb
      subst hb
      exact Or.inl ⟨z, hz, by simp⟩
  have hTHo : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (2 * (E + 1) + PEqualNP.Outside.Meta497.offs φ i + j) ↔ j ≠ f i) := by
    intro i j hi hj
    have hcij := hc i j hi hj
    rw [hTH]
    constructor
    · rintro (⟨z', hz', h⟩ | h | ⟨i', hi', j', hj', hne, h⟩ | h)
      · have := he z' hz'
        omega
      · omega
      · obtain ⟨rfl, rfl⟩ := PEqualNP.Outside.Meta497.offs_inj φ hi hi' hj hj' (by omega)
        exact hne
      · omega
    · intro hne
      exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hne, rfl⟩))
  have hTH2E : ¬ TH (2 * E) := by
    rw [hTH]
    rintro (⟨z', hz', h⟩ | h | ⟨i', hi', j', hj', hne, h⟩ | h)
    · have := he z' hz'
      omega
    · omega
    · omega
    · omega
  have hTH2E1 : TH (2 * E + 1) := (hTH _).mpr (Or.inr (Or.inl rfl))
  have hTHlast : TH (3 * E + 2) := (hTH _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hu1 : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inl (lit i j)) ≤ 2 * E + 1 ∧
        (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2 = true) := by
    intro i j hi hj
    by_cases hjl : j < (φ.getD i []).length
    · have hz := hlitvars i j hi hjl
      have h1 := hnumL _ hz (lit i j).2
      have h2 := hTHlit _ hz (lit i j).2
      have h3 := he _ hz
      rw [Prod.mk.eta] at h1
      rw [h1]
      refine ⟨?_, h2⟩
      split <;> omega
    · have hjeq : j = (φ.getD i []).length := by omega
      subst hjeq
      rw [hlitlast i, hnumY true]
      simpa using hTH2E1
  have hmi : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t, t < 2 * k ∧ (t % 2 = 1 ↔ b = true) ∧ x = N + 2 * k * (u * N + v) + t := by
    intro u v b x
    rw [hinner]
    simp only [List.mem_map, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨t, ⟨ht, hb⟩, rfl⟩
      exact ⟨t, ht, (PEqualNP.Outside.Meta497.par t b).mp hb, rfl⟩
    · rintro ⟨t, ht, hb, rfl⟩
      exact ⟨t, ⟨ht, (PEqualNP.Outside.Meta497.par t b).mpr hb⟩, rfl⟩
  have hinodup : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner]
    refine List.Nodup.map ?_ (List.Nodup.filter _ List.nodup_range)
    intro t t' h
    simp only at h
    omega
  obtain ⟨cell, hcelldef⟩ : ∃ cell : ℕ → ℕ → List ℕ, cell = fun i j => (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ PEqualNP.Outside.Meta497.offs φ i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ PEqualNP.Outside.Meta497.offs φ i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else [])) := ⟨_, rfl⟩
  obtain ⟨tail, htaildef⟩ : ∃ tail : List ℕ, tail = (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) := ⟨_, rfl⟩
  have hTL' : TL = (List.range φ.length).flatMap (fun i =>
      (List.range ((φ.getD i []).length + 1)).flatMap (fun j => cell i j)) ++ tail := by
    rw [hTL, hcelldef, htaildef]
  clear hTL
  have hzn : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      num (Sum.inl (z, false)) = 2 * e z ∧ num (Sum.inl (z, true)) = 2 * e z + 1 := by
    intro z hz
    exact ⟨by simpa using hnumL z hz false, by simpa using hnumL z hz true⟩
  have hcm : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → ∀ x, x ∈ cell i j ↔
      ((∃ t, t < 2 * k ∧ (t % 2 = 1 ↔ (lit i j).2 = true) ∧
          x = N + 2 * k * (num (Sum.inl (lit i j)) * N + (2 * (E + 1) + PEqualNP.Outside.Meta497.offs φ i + j)) + t) ∨
        (∃ l, (j < l ∧ l ≤ (φ.getD i []).length) ∧ ∃ t, t < 2 * k ∧ (t % 2 = 1 ↔ j ≠ f i) ∧
          x = N + 2 * k * ((2 * (E + 1) + PEqualNP.Outside.Meta497.offs φ i + j) * N +
            (2 * (E + 1) + PEqualNP.Outside.Meta497.offs φ i + l)) + t) ∨
        ((j < (φ.getD i []).length ∧ PEqualNP.Outside.Meta497.offs φ i + j = e (lit i j).1) ∧ ∃ t, t < 2 * k ∧ ¬ t % 2 = 1 ∧
          x = N + 2 * k * (2 * (PEqualNP.Outside.Meta497.offs φ i + j) * N + (2 * (PEqualNP.Outside.Meta497.offs φ i + j) + 1)) + t) ∨
        (j ≠ f i ∧ x = (2 * (E + 1) + PEqualNP.Outside.Meta497.offs φ i + j)) ∨
        ((j < (φ.getD i []).length ∧ PEqualNP.Outside.Meta497.offs φ i + j = e (lit i j).1) ∧ x = 2 * (PEqualNP.Outside.Meta497.offs φ i + j) + 1)) := by
    intro i j hi hj x
    rw [hcelldef]
    simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
      List.mem_ite_nil_right, List.mem_singleton, hmi, decide_eq_true_eq, hnumO i j hi hj,
      Bool.false_eq_true, iff_false]
    constructor
    · rintro ((((h | ⟨l, ⟨hl1, hl2⟩, t, ht, hp, rfl⟩) | ⟨hD, t, ht, hp, rfl⟩) | h) | ⟨hD, rfl⟩)
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨l, ⟨hl2, by omega⟩, t, ht, hp, ?_⟩)
        rw [hnumO i l hi (by omega)]
      · obtain ⟨h1, h2⟩ := hzn _ (hlitvars i j hi hD.1)
        refine Or.inr (Or.inr (Or.inl ⟨hD, t, ht, hp, ?_⟩))
        rw [h1, h2, ← hD.2]
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · obtain ⟨h1, h2⟩ := hzn _ (hlitvars i j hi hD.1)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, ?_⟩)))
        rw [h2, ← hD.2]
    · rintro (h | ⟨l, ⟨hl1, hl2⟩, t, ht, hp, rfl⟩ | ⟨hD, t, ht, hp, rfl⟩ | h | ⟨hD, rfl⟩)
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨l, ⟨by omega, hl1⟩, t, ht, hp, ?_⟩)))
        rw [hnumO i l hi hl2]
      · obtain ⟨h1, h2⟩ := hzn _ (hlitvars i j hi hD.1)
        refine Or.inl (Or.inl (Or.inr ⟨hD, t, ht, hp, ?_⟩))
        rw [h1, h2, ← hD.2]
      · exact Or.inl (Or.inr h)
      · obtain ⟨h1, h2⟩ := hzn _ (hlitvars i j hi hD.1)
        refine Or.inr ⟨hD, ?_⟩
        rw [h2, ← hD.2]
  have hQ : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → ∀ x, x ∈ cell i j →
      PEqualNP.Outside.Meta497.Q E N k (PEqualNP.Outside.Meta497.offs φ i + j) x := by
    intro i j hi hj x hx
    have hcij := hc i j hi hj
    rcases (hcm i j hi hj x).mp hx with ⟨t, ht, -, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, t, ht, -, rfl⟩ |
      ⟨hD, t, ht, -, rfl⟩ | ⟨-, rfl⟩ | ⟨hD, rfl⟩
    · exact Or.inr (Or.inr ⟨_, _, t, ht, by omega, rfl,
        Or.inl ⟨(hu1 i j hi hj).1, by omega⟩⟩)
    · have := hc i l hi hl2
      exact Or.inr (Or.inr ⟨_, _, t, ht, by omega, rfl, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩)
    · exact Or.inr (Or.inr ⟨_, _, t, ht, by omega, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl rfl)
  have hY0 : num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)) = 2 * E := by
    simpa using hnumY false
  have hY1 : num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) = 2 * E + 1 := by
    simpa using hnumY true
  have htm : ∀ x, x ∈ tail ↔
      ((∃ t, t < 2 * k ∧ ¬ t % 2 = 1 ∧ x = N + 2 * k * (2 * E * N + (2 * E + 1)) + t) ∨
      (∃ t, t < 2 * k ∧ ¬ t % 2 = 1 ∧ x = N + 2 * k * (2 * E * N + (3 * E + 2)) + t) ∨
      x = 2 * E + 1 ∨ x = 3 * E + 2) := by
    intro x
    rw [htaildef]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hmi, hY0, hY1,
      hnumLast, Bool.false_eq_true, iff_false]
    exact or_assoc
  have hcn : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → (cell i j).Nodup := by
    intro i j hi hj
    have hcij := hc i j hi hj
    have hU := (hu1 i j hi hj).1
    rw [hcelldef]
    beta_reduce
    refine PEqualNP.Outside.Meta497.nodup_append_of (PEqualNP.Outside.Meta497.nodup_append_of
      (PEqualNP.Outside.Meta497.nodup_append_of (PEqualNP.Outside.Meta497.nodup_append_of
        (hinodup _ _ _) ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_
    · apply PEqualNP.Outside.Meta497.nodup_flatMap_of_key _ _
        (List.Nodup.filter _ List.nodup_range) (fun _ _ => hinodup _ _ _)
      intro l hl l' hl' x hx hx'
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl hl'
      rw [hmi, hnumO i j hi hj, hnumO i l hi (by omega)] at hx
      rw [hmi, hnumO i j hi hj, hnumO i l' hi (by omega)] at hx'
      obtain ⟨t, ht, -, rfl⟩ := hx
      obtain ⟨t', ht', -, h⟩ := hx'
      have hl1 := hc i l hi (by omega)
      have hl2 := hc i l' hi (by omega)
      obtain ⟨-, h2, -⟩ := PEqualNP.Outside.Meta497.dec ht ht' (by omega) (by omega) h
      omega
    · intro x hx hx'
      simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
        List.mem_ite_nil_right, List.mem_singleton, hmi, decide_eq_true_eq, hnumO i j hi hj,
        Bool.false_eq_true, iff_false] at hx hx'
      obtain ⟨t, ht, -, rfl⟩ := hx
      obtain ⟨l, ⟨hl1, hl2⟩, t', ht', -, h⟩ := hx'
      rw [hnumO i l hi (by omega)] at h
      have := hc i l hi (by omega)
      obtain ⟨h1, -, -⟩ := PEqualNP.Outside.Meta497.dec ht ht' (by omega) (by omega) h
      omega
    · split
      · exact hinodup _ _ _
      · exact List.nodup_nil
    · intro x hx hx'
      simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
        List.mem_ite_nil_right, List.mem_singleton, hmi, decide_eq_true_eq, hnumO i j hi hj,
        Bool.false_eq_true, iff_false] at hx hx'
      obtain ⟨hD, t', ht', -, h'⟩ := hx'
      have hz := hlitvars i j hi hD.1
      obtain ⟨h1, h2⟩ := hzn _ hz
      have hez := he _ hz
      rw [h1, h2] at h'
      rcases hx with ⟨t, ht, -, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, t, ht, -, rfl⟩
      · obtain ⟨-, h3, -⟩ := PEqualNP.Outside.Meta497.dec ht ht' (by omega) (by omega) h'
        omega
      · rw [hnumO i l hi (by omega)] at h'
        have := hc i l hi (by omega)
        obtain ⟨h3, -, -⟩ := PEqualNP.Outside.Meta497.dec ht ht' (by omega) (by omega) h'
        omega
    · split <;> simp
    · intro x hx hx'
      simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
        List.mem_ite_nil_right, List.mem_singleton, hmi, decide_eq_true_eq, hnumO i j hi hj,
        Bool.false_eq_true, iff_false] at hx hx'
      obtain ⟨-, hxo⟩ := hx'
      rcases hx with (⟨t, ht, -, rfl⟩ | ⟨l, -, t, ht, -, rfl⟩) | ⟨-, t, ht, -, rfl⟩ <;> omega
    · split <;> simp
    · intro x hx hx'
      simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
        List.mem_ite_nil_right, List.mem_singleton, hmi, decide_eq_true_eq, hnumO i j hi hj,
        Bool.false_eq_true, iff_false] at hx hx'
      obtain ⟨hD, hxo⟩ := hx'
      have hz := hlitvars i j hi hD.1
      obtain ⟨h1, h2⟩ := hzn _ hz
      have hez := he _ hz
      rw [h2] at hxo
      rcases hx with ((⟨t, ht, -, rfl⟩ | ⟨l, -, t, ht, -, rfl⟩) | ⟨-, t, ht, -, rfl⟩) | ⟨-, rfl⟩ <;>
        omega
  have hnodup : TL.Nodup := by
    rw [hTL']
    refine PEqualNP.Outside.Meta497.nodup_append_of ?_ ?_ ?_
    · apply PEqualNP.Outside.Meta497.nodup_flatMap_of_key _ _ List.nodup_range
      · intro i hi
        rw [List.mem_range] at hi
        apply PEqualNP.Outside.Meta497.nodup_flatMap_of_key _ _ List.nodup_range
        · intro j hj
          rw [List.mem_range] at hj
          exact hcn i j hi (by omega)
        · intro j hj j' hj' x hx hx'
          rw [List.mem_range] at hj hj'
          have h1 := hQ i j hi (by omega) x hx
          have h2 := hQ i j' hi (by omega) x hx'
          have := PEqualNP.Outside.Meta497.Q_inj hN (hc i j hi (by omega))
            (hc i j' hi (by omega)) h1 h2
          omega
      · intro i hi i' hi' x hx hx'
        rw [List.mem_range] at hi hi'
        simp only [List.mem_flatMap, List.mem_range] at hx hx'
        obtain ⟨j, hj, hx⟩ := hx
        obtain ⟨j', hj', hx'⟩ := hx'
        have h1 := hQ i j hi (by omega) x hx
        have h2 := hQ i' j' hi' (by omega) x hx'
        have := PEqualNP.Outside.Meta497.Q_inj hN (hc i j hi (by omega))
          (hc i' j' hi' (by omega)) h1 h2
        exact (PEqualNP.Outside.Meta497.offs_inj φ hi hi' (by omega) (by omega) this).1
    · rw [htaildef]
      refine PEqualNP.Outside.Meta497.nodup_append_of (PEqualNP.Outside.Meta497.nodup_append_of
        (hinodup _ _ _) (hinodup _ _ _) ?_) ?_ ?_
      · intro x hx hx'
        rw [hmi, hY0, hY1] at hx
        rw [hmi, hY0, hnumLast] at hx'
        obtain ⟨t, ht, -, rfl⟩ := hx
        obtain ⟨t', ht', -, h⟩ := hx'
        obtain ⟨-, h2, -⟩ := PEqualNP.Outside.Meta497.dec ht ht' (by omega) (by omega) h
        omega
      · rw [hY1, hnumLast]
        simp
        omega
      · intro x hx hx'
        simp only [List.mem_append, hmi, hY0, hY1, hnumLast, List.mem_cons, List.not_mem_nil,
          or_false] at hx hx'
        rcases hx with ⟨t, ht, -, rfl⟩ | ⟨t, ht, -, rfl⟩ <;> omega
    · intro x hx hx'
      simp only [List.mem_flatMap, List.mem_range] at hx
      obtain ⟨i, hi, j, hj, hx⟩ := hx
      exact PEqualNP.Outside.Meta497.Q_tail hN (hc i j hi (by omega))
        (hQ i j hi (by omega) x hx) ((htm x).mp hx')
  refine ⟨hnodup, ?_⟩
  have hin : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length → ∀ x, x ∈ cell i j → x ∈ TL := by
    intro i j hi hj x hx
    rw [hTL']
    simp only [List.mem_append, List.mem_flatMap, List.mem_range]
    exact Or.inl ⟨i, hi, j, by omega, hx⟩
  have hint : ∀ x, x ∈ tail → x ∈ TL := by
    intro x hx
    rw [hTL']
    exact List.mem_append_right _ hx
  have hdes : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ i j, i < φ.length ∧ j < (φ.getD i []).length ∧
      PEqualNP.Outside.Meta497.offs φ i + j = e z ∧ (lit i j).1 = z := by
    intro z hz
    obtain ⟨l, hl, hlz⟩ := hedes z hz
    obtain ⟨i, hi, j, hj, hp, hget⟩ := PEqualNP.Outside.Meta497.flat_some φ _ l hl
    refine ⟨i, j, hi, hj, hp.symm, ?_⟩
    rw [hlit, PEqualNP.Outside.Meta497.getD_append_of_get _ _ _ l hget]
    exact hlz
  have hedge : ∀ (U V : PEqualNP.MetaComplexity.CoverPromise.Vertex), (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj U V → num U < num V → num V < N →
      ∀ t, t < 2 * k → (t % 2 = 1 ↔ TH (num U)) →
      ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t' < 2 * k,
        N + 2 * k * (num U * N + num V) + t = N + 2 * k * (u.val * N + v.val) + t' ∧
          (t' % 2 = 1 ↔ TH u.val) := by
    intro U V hUV hlt hVN t ht hp
    exact ⟨⟨num U, by omega⟩, ⟨num V, hVN⟩, hlt, (hH _ _).mpr ⟨U, V, hUV, rfl, rfl⟩,
      t, ht, rfl, hp⟩
  have hnT : ∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ¬ TH (2 * e z) := by
    intro z hz
    simpa using hTHlit z hz false
  have hadjA : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj (Sum.inl (lit i j)) (Sum.inr (i, j)) := by
    intro i j hi hj
    exact hlitget i j hi hj
  have hlenC : ∀ i, i < φ.length →
      (PEqualNP.MetaComplexity.CoverPromise.clauseAt (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) i).length = (φ.getD i []).length + 1 := by
    intro i hi
    rw [PEqualNP.Outside.Meta497.clauseAt_lt φ hi]
    simp
  intro x
  constructor
  · intro hx
    rw [hTL'] at hx
    simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hx
    rcases hx with ⟨i, hi, j, hj, hx⟩ | hx
    · have hj' : j ≤ (φ.getD i []).length := by omega
      have hcij := hc i j hi hj'
      have hnO := hnumO i j hi hj'
      rcases (hcm i j hi hj' x).mp hx with ⟨t, ht, hp, rfl⟩ | ⟨l, ⟨hl1, hl2⟩, t, ht, hp, rfl⟩ |
        ⟨hD, t, ht, hp, rfl⟩ | ⟨hne, rfl⟩ | ⟨hD, rfl⟩
      · right
        have hU := hu1 i j hi hj'
        have := hedge _ _ (hadjA i j hi hj') (by omega) (by omega) t ht (hp.trans hU.2.symm)
        rw [hnO] at this
        exact this
      · right
        have hnl := hnumO i l hi hl2
        have hcl := hc i l hi hl2
        have hadj : (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj (Sum.inr (i, j)) (Sum.inr (i, l)) := by
          refine ⟨rfl, by omega, ?_, ?_⟩
          · rw [hlenC i hi]
            omega
          · rw [hlenC i hi]
            omega
        have := hedge _ _ hadj (by omega) (by omega) t ht
          (by rw [hnO]; exact hp.trans (hTHo i j hi hj').symm)
        rw [hnO, hnl] at this
        exact this
      · right
        have hz := hlitvars i j hi hD.1
        obtain ⟨h1, h2⟩ := hzn _ hz
        have hez := he _ hz
        have hadj : (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj (Sum.inl ((lit i j).1, false))
            (Sum.inl ((lit i j).1, true)) :=
          ⟨rfl, by simp, (PEqualNP.Outside.Meta497.mem_vars_cvc φ _).mpr (Or.inl hz)⟩
        have := hedge _ _ hadj (by omega) (by omega) t ht
          (by rw [h1]; exact iff_of_false hp (hnT _ hz))
        rw [h1, h2, ← hD.2] at this
        exact this
      · exact Or.inl ((hTHo i j hi hj').mpr hne)
      · exact Or.inl ((hTH _).mpr (Or.inl ⟨_, hlitvars i j hi hD.1, by rw [hD.2]⟩))
    · rcases (htm x).mp hx with ⟨t, ht, hp, rfl⟩ | ⟨t, ht, hp, rfl⟩ | rfl | rfl
      · right
        have hadj : (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))
            (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) :=
          ⟨rfl, by simp, (PEqualNP.Outside.Meta497.mem_vars_cvc φ _).mpr (Or.inr rfl)⟩
        have := hedge _ _ hadj (by omega) (by omega) t ht
          (by rw [hY0]; exact iff_of_false hp hTH2E)
        rw [hY0, hY1] at this
        exact this
      · right
        have hadj : (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))
            (Sum.inr (φ.length, 0)) := by
          show (PEqualNP.MetaComplexity.CoverPromise.clauseAt (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) φ.length)[0]? = some (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)
          rw [PEqualNP.Outside.Meta497.clauseAt_eq]
          rfl
        have := hedge _ _ hadj (by omega) (by omega) t ht
          (by rw [hY0]; exact iff_of_false hp hTH2E)
        rw [hY0, hnumLast] at this
        exact this
      · exact Or.inl hTH2E1
      · exact Or.inl hTHlast
  · rintro (hTHx | ⟨u, v, huv, hadj, t, ht, rfl, hp⟩)
    · rcases (hTH x).mp hTHx with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
      · obtain ⟨i, j, hi, hj, hpos, hl1⟩ := hdes z hz
        refine hin i j hi (by omega) _ ((hcm i j hi (by omega) _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hj, by rw [hl1]; exact hpos⟩, by rw [hpos]⟩)))))
      · exact hint _ ((htm _).mpr (Or.inr (Or.inr (Or.inl rfl))))
      · exact hin i j hi hj _ ((hcm i j hi hj _).mpr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, rfl⟩)))))
      · exact hint _ ((htm _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    · obtain ⟨U, V, hUV, hU, hV⟩ := (hH u v).mp hadj
      have huv' : num U < num V := by
        rw [hU, hV]
        exact Fin.lt_def.mp huv
      rw [← hU] at hp
      rw [← hU, ← hV]
      have hUV' : PEqualNP.MetaComplexity.CoverPromise.satAdj (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) U V := hUV
      clear hU hV hadj huv hUV
      rcases U with a | ⟨i, j⟩ <;> rcases V with b | ⟨i', l⟩ <;> simp only [PEqualNP.MetaComplexity.CoverPromise.satAdj] at hUV'
      · obtain ⟨z, ba⟩ := a
        obtain ⟨z', bb⟩ := b
        obtain ⟨h1, h2, h3⟩ := hUV'
        obtain rfl : z = z' := h1
        by_cases hz : z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ
        · obtain ⟨hn0, hn1⟩ := hzn z hz
          rcases ba with _ | _ <;> rcases bb with _ | _
          · exact absurd rfl h2
          · obtain ⟨i, j, hi, hj, hpos, hl1⟩ := hdes z hz
            rw [hn0] at hp
            rw [hn0, hn1, ← hpos]
            exact hin i j hi (by omega) _ ((hcm i j hi (by omega) _).mpr
              (Or.inr (Or.inr (Or.inl ⟨⟨hj, by rw [hl1]; exact hpos⟩, t, ht,
                fun h => hnT z hz (hp.mp h), rfl⟩))))
          · rw [hn0, hn1] at huv'
            omega
          · exact absurd rfl h2
        · obtain rfl : z = PEqualNP.MetaComplexity.CoverPromise.fresh φ := by
            rcases (PEqualNP.Outside.Meta497.mem_vars_cvc φ z).mp h3 with h | h
            · exact absurd h hz
            · exact h
          rcases ba with _ | _ <;> rcases bb with _ | _
          · exact absurd rfl h2
          · rw [hY0] at hp
            rw [hY0, hY1]
            exact hint _ ((htm _).mpr (Or.inl ⟨t, ht, fun h => hTH2E (hp.mp h), rfl⟩))
          · rw [hY0, hY1] at huv'
            omega
          · exact absurd rfl h2
      · -- a literal and an occurrence
        by_cases hi : i' < φ.length
        · rw [PEqualNP.Outside.Meta497.clauseAt_lt φ hi] at hUV'
          obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hUV'
          have hl : l ≤ (φ.getD i' []).length := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen
            omega
          have hget := hlitget i' l hi hl
          rw [PEqualNP.Outside.Meta497.clauseAt_lt φ hi] at hget
          obtain rfl : a = lit i' l := Option.some.inj (hUV'.symm.trans hget)
          rw [hnumO i' l hi hl]
          exact hin i' l hi hl _ ((hcm i' l hi hl _).mpr
            (Or.inl ⟨t, ht, hp.trans (hu1 i' l hi hl).2, rfl⟩))
        · by_cases hi2 : i' = φ.length
          · subst hi2
            rw [PEqualNP.Outside.Meta497.clauseAt_eq] at hUV'
            rcases l with _ | l
            · obtain rfl : (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false) = a := by simpa using hUV'
              rw [hY0] at hp
              rw [hY0, hnumLast]
              exact hint _ ((htm _).mpr (Or.inr (Or.inl ⟨t, ht,
                fun h => hTH2E (hp.mp h), rfl⟩)))
            · simp at hUV'
          · rw [PEqualNP.Outside.Meta497.clauseAt_gt φ (by omega)] at hUV'
            simp at hUV'
      · -- an occurrence and a literal: the numbers are in the wrong order
        exfalso
        by_cases hi : i < φ.length
        · rw [PEqualNP.Outside.Meta497.clauseAt_lt φ hi] at hUV'
          obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hUV'
          have hl : j ≤ (φ.getD i []).length := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen
            omega
          have hget := hlitget i j hi hl
          rw [PEqualNP.Outside.Meta497.clauseAt_lt φ hi] at hget
          obtain rfl : b = lit i j := Option.some.inj (hUV'.symm.trans hget)
          rw [hnumO i j hi hl] at huv'
          have := (hu1 i j hi hl).1
          omega
        · by_cases hi2 : i = φ.length
          · subst hi2
            rw [PEqualNP.Outside.Meta497.clauseAt_eq] at hUV'
            rcases j with _ | j
            · obtain rfl : (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false) = b := by simpa using hUV'
              rw [hY0, hnumLast] at huv'
              omega
            · simp at hUV'
          · rw [PEqualNP.Outside.Meta497.clauseAt_gt φ (by omega)] at hUV'
            simp at hUV'
      · -- two occurrences of one clause
        obtain ⟨rfl, hne, hj, hl⟩ := hUV'
        by_cases hi : i < φ.length
        · rw [hlenC i hi] at hj hl
          have hj' : j ≤ (φ.getD i []).length := by omega
          have hl' : l ≤ (φ.getD i []).length := by omega
          rw [hnumO i j hi hj', hnumO i l hi hl'] at huv'
          rw [hnumO i j hi hj'] at hp
          rw [hnumO i j hi hj', hnumO i l hi hl']
          exact hin i j hi hj' _ ((hcm i j hi hj' _).mpr
            (Or.inr (Or.inl ⟨l, ⟨by omega, hl'⟩, t, ht, hp.trans (hTHo i j hi hj'), rfl⟩)))
        · exfalso
          by_cases hi2 : i = φ.length
          · subst hi2
            rw [PEqualNP.Outside.Meta497.clauseAt_eq] at hj hl
            simp at hj hl
            omega
          · rw [PEqualNP.Outside.Meta497.clauseAt_gt φ (by omega)] at hj
            simp at hj
