import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3577

-- Points are lattice coordinates. A line is specified by its slope and intercept.
abbrev Q : ℕ := 100000
abbrev Pt := Fin Q × Fin (2 * Q ^ 2)
abbrev Ln := Fin Q × Fin (Q ^ 2)
abbrev V := Sum Pt Ln

def incident (p : Pt) (l : Ln) : Prop :=
  p.2.val = l.1.val * p.1.val + l.2.val

def G : SimpleGraph V where
  Adj
    | .inl p, .inr l => incident p l
    | .inr l, .inl p => incident p l
    | .inl _, .inl _ => False
    | .inr _, .inr _ => False
  symm := ⟨by rintro (p|l) (q|m) h <;> exact h⟩
  loopless := ⟨by rintro (p|l) <;> exact id⟩

def side : V → Bool := Sum.elim (fun _ => false) (fun _ => true)

lemma side_adj (u v : V) (h : G.Adj u v) : side u ≠ side v := by
  rcases u with p|l <;> rcases v with q|m <;> first | exact h.elim | simp [side]

-- Two lines passing through two distinct points must coincide.
lemma incidence_unique (p q : Pt) (l m : Ln)
    (hpl : incident p l) (hpm : incident p m)
    (hql : incident q l) (hqm : incident q m) : p = q ∨ l = m := by
  unfold incident at hpl hpm hql hqm
  zify at hpl hpm hql hqm
  have h : ((l.1.val : ℤ) - m.1.val) * ((p.1.val : ℤ) - q.1.val) = 0 := by
    nlinarith only [hpl, hpm, hql, hqm]
  rcases mul_eq_zero.mp h with h|h
  · right
    have ha : l.1 = m.1 := by apply Fin.ext; omega
    apply Prod.ext ha
    apply Fin.ext
    rw [ha] at hpl
    omega
  · left
    have hx : p.1 = q.1 := by apply Fin.ext; omega
    apply Prod.ext hx
    apply Fin.ext
    rw [hx] at hpl
    omega

lemma no_four (u v w z : V) (huw : u ≠ w) (hvz : v ≠ z) :
    ¬ (G.Adj u v ∧ G.Adj v w ∧ G.Adj w z ∧ G.Adj z u) := by
  rintro ⟨huv, hvw, hwz, hzu⟩
  rcases u with u|u <;> rcases v with v|v <;> rcases w with w|w <;> rcases z with z|z <;>
    try first | exact huv.elim | exact hvw.elim | exact hwz.elim
  · rcases incidence_unique u w v z huv hzu hvw hwz with h|h
    · exact huw (congrArg Sum.inl h)
    · exact hvz (congrArg Sum.inr h)
  · rcases incidence_unique v z u w huv hvw hzu hwz with h|h
    · exact hvz (congrArg Sum.inl h)
    · exact huw (congrArg Sum.inr h)

def pointOn (x : Fin Q) (l : Ln) : Pt :=
  (x, ⟨l.1.val * x.val + l.2.val, by
    have hax : l.1.val * x.val ≤ Q * Q :=
      Nat.mul_le_mul (Nat.le_of_lt l.1.isLt) (Nat.le_of_lt x.isLt)
    rw [← pow_two] at hax
    have hb := l.2.isLt
    omega⟩)

def namedEdge (s : Fin Q × Ln) : Sym2 V :=
  s(Sum.inl (pointOn s.1 s.2), Sum.inr s.2)

open scoped Classical

-- Each line contributes a distinct edge for each permitted horizontal coordinate.
lemma edges_ge : Q ^ 4 ≤ G.edgeFinset.card := by
  let emb (s : Fin Q × Ln) : G.edgeSet := ⟨namedEdge s, (rfl : incident (pointOn s.1 s.2) s.2)⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    have he : namedEdge a = namedEdge b := congrArg Subtype.val hab
    rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩|⟨h1,_⟩
    · exact Prod.ext (congrArg (fun p : Pt => p.1) (Sum.inl.inj h1)) (Sum.inr.inj h2)
    · cases h1
  calc
    Q ^ 4 = Q * (Q * Q ^ 2) := by ring
    _ = Fintype.card (Fin Q × Ln) := by simp only [Fintype.card_prod, Fintype.card_fin, Ln]
    _ ≤ Fintype.card G.edgeSet := Fintype.card_le_of_injective emb hinj
    _ = _ := SimpleGraph.card_edgeSet

def modulus (i : Fin 12) : ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37][i.val]'(by simp)

lemma modulus_pos (i : Fin 12) : 0 < modulus i :=
  (by decide : ∀ j : Fin 12, 0 < modulus j) i

lemma modulus_le (i : Fin 12) : modulus i ≤ 37 :=
  (by decide : ∀ j : Fin 12, modulus j ≤ 37) i

-- Equal residues at the eight largest moduli force equality throughout the coordinate range.
lemma exists_mod_ne {u v : ℕ} (hu : u < 2 * 100000^2) (hv : v < 2 * 100000^2)
    (hne : u ≠ v) : ∃ i : Fin 12, u % modulus i ≠ v % modulus i := by
  by_contra! h
  have eqs (i : Fin 12) : Nat.ModEq (modulus i) u v := h i
  have same := Nat.mod_lcm
    (Nat.mod_lcm (Nat.mod_lcm (eqs 4) (eqs 5)) (Nat.mod_lcm (eqs 6) (eqs 7)))
    (Nat.mod_lcm (Nat.mod_lcm (eqs 8) (eqs 9)) (Nat.mod_lcm (eqs 10) (eqs 11)))
  change u % 35336848261 = v % 35336848261 at same
  have hbound : 2 * 100000 ^ 2 < 35336848261 := by decide
  exact hne (by simpa only [Nat.mod_eq_of_lt (hu.trans hbound),
    Nat.mod_eq_of_lt (hv.trans hbound)] using same)

abbrev Ix := Sum Bool (Fin 12 × Fin 37 × Fin 37)

-- A residue block contains one residue class of points and the lines that miss it modulo that modulus.
def blockProp : Ix → V → Prop
  | .inl false, .inl _ => True
  | .inl true, .inr _ => True
  | .inl _, _ => False
  | .inr (i, x, y), .inl p =>
    p.1.val % modulus i = x.val ∧ p.2.val % modulus i = y.val
  | .inr (i, x, y), .inr l =>
    y.val ≠ (l.1.val * x.val + l.2.val) % modulus i

lemma blocks_mem (a : V) : ∃ j, blockProp j a := by
  cases a with
  | inl p => exact ⟨.inl false, True.intro⟩
  | inr l => exact ⟨.inl true, True.intro⟩

lemma blocks_omit (a : V) : ∃ j, ¬ blockProp j a := by
  cases a with
  | inl p => exact ⟨.inl true, id⟩
  | inr l => exact ⟨.inl false, id⟩

lemma residue_eval (x d c m : ℕ) :
    (d * (x % m) + c) % m = (d * x + c) % m :=
  ((Nat.mod_modEq x m).mul_left d).add_right c

lemma block_cross_indep (j : Ix) (p : Pt) (l : Ln)
    (hp : blockProp j (.inl p)) (hl : blockProp j (.inr l)) : ¬ incident p l := by
  rcases j with b | ⟨i, x, y⟩
  · cases b <;> simp [blockProp] at hp hl
  · change p.1.val % modulus i = x.val ∧ p.2.val % modulus i = y.val at hp
    change y.val ≠ (l.1.val * x.val + l.2.val) % modulus i at hl
    intro h
    change p.2.val = l.1.val * p.1.val + l.2.val at h
    apply hl
    rw [← hp.1, residue_eval, ← hp.2, h]

lemma blocks_indep (j : Ix) (a : V) (ha : blockProp j a) (b : V) (hb : blockProp j b) :
    ¬ G.Adj a b := by
  cases a with
  | inl p =>
    cases b with
    | inl w => exact fun h => h
    | inr l => exact block_cross_indep j p l ha hb
  | inr l =>
    cases b with
    | inl p => exact block_cross_indep j p l hb ha
    | inr w => exact fun h => h

lemma blocks_cross_pair (p : Pt) (l : Ln) (h : ¬ incident p l) :
    ∃ j, blockProp j (.inl p) ∧ blockProp j (.inr l) := by
  have hd : l.1.val * p.1.val + l.2.val < 2 * 100000^2 := by
    have hmul := Nat.mul_le_mul (Nat.le_of_lt l.1.isLt) (Nat.le_of_lt p.1.isLt)
    change l.1.val * p.1.val ≤ 100000 * 100000 at hmul
    have hint := l.2.isLt
    change l.2.val < 100000 ^ 2 at hint
    omega
  obtain ⟨i, hi⟩ := exists_mod_ne p.2.isLt hd h
  let x : Fin 37 := ⟨p.1.val % modulus i,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (modulus_pos i)) (modulus_le i)⟩
  let y : Fin 37 := ⟨p.2.val % modulus i,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (modulus_pos i)) (modulus_le i)⟩
  refine ⟨.inr (i, x, y), ⟨rfl, rfl⟩, ?_⟩
  change p.2.val % modulus i ≠ (l.1.val * (p.1.val % modulus i) + l.2.val) % modulus i
  rwa [residue_eval]

lemma blocks_pair (a b : V) (_hne : a ≠ b) (h : ¬ G.Adj a b) :
    ∃ j, blockProp j a ∧ blockProp j b := by
  cases a with
  | inl p =>
    cases b with
    | inl w =>
      exact ⟨.inl false, True.intro, True.intro⟩
    | inr l => exact blocks_cross_pair p l h
  | inr l =>
    cases b with
    | inl p =>
      obtain ⟨j, hp, hl⟩ := blocks_cross_pair p l h
      exact ⟨j, hl, hp⟩
    | inr w =>
      exact ⟨.inl true, True.intro, True.intro⟩

-- Transfer arbitrary finite vertex and block types to the numbered types of the posted statement.
lemma transport_refutation {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (g : SimpleGraph A) [DecidableRel g.Adj] (s : A → Bool) (b : B → A → Prop)
    (hs : ∀ x y, g.Adj x y → s x ≠ s y)
    (hfour : ∀ x y z w, x ≠ z → y ≠ w → ¬ (g.Adj x y ∧ g.Adj y z ∧ g.Adj z w ∧ g.Adj w x))
    (hk : 2 ≤ Fintype.card B)
    (hind : ∀ j, ∀ x, b j x → ∀ y, b j y → ¬ g.Adj x y)
    (hmem : ∀ x, ∃ j, b j x) (homit : ∀ x, ∃ j, ¬ b j x)
    (hmiss : ∀ j, ∃ x y, x ≠ y ∧ ¬ b j x ∧ ¬ b j y)
    (hpair : ∀ x y, x ≠ y → ¬ g.Adj x y → ∃ j, b j x ∧ b j y)
    (hcost : Fintype.card B * Fintype.card A < g.edgeFinset.card) :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  intro claim
  let sets (j : B) := Finset.univ.filter (b j)
  have hsizes (j : B) : (sets j).card + 2 ≤ Fintype.card A := by
    obtain ⟨u, v, huv, hu, hv⟩ := hmiss j
    have hu' : u ∉ sets j := by simpa [sets] using hu
    have hv' : v ∉ insert u (sets j) := by simp [sets, Ne.symm huv, hv]
    have bound := Finset.card_le_univ (insert v (insert u (sets j)))
    rwa [Finset.card_insert_of_notMem hv', Finset.card_insert_of_notMem hu'] at bound
  let e := Fintype.equivFin A
  let f := Fintype.equivFin B
  let g' := g.comap e.symm
  let b' := fun j => (sets (f.symm j)).map e.toEmbedding
  have hm (j x) : x ∈ b' j ↔ b (f.symm j) (e.symm x) := by
    simp [b', sets]
  have hcard (j) : (b' j).card = (sets (f.symm j)).card := Finset.card_map _
  obtain ⟨T, _, hbound⟩ := claim (Fintype.card A) (Fintype.card B) g' (s ∘ e.symm) b'
    (fun x y => hs (e.symm x) (e.symm y))
    (fun x y z w hx hy => hfour _ _ _ _ (e.symm.injective.ne hx) (e.symm.injective.ne hy)) hk
    (fun j x hx y hy => hind _ _ ((hm j x).mp hx) _ ((hm j y).mp hy))
    (by
      intro x
      obtain ⟨j, hj⟩ := hmem (e.symm x)
      exact ⟨f j, (hm _ _).mpr (by simpa using hj)⟩)
    (by
      intro x
      obtain ⟨j, hj⟩ := homit (e.symm x)
      exact ⟨f j, fun h => hj (by simpa using (hm _ _).mp h)⟩)
    (by intro j; rw [hcard]; exact hsizes _)
    (by
      intro x y hxy hn
      obtain ⟨j, hx, hy⟩ := hpair _ _ (e.symm.injective.ne hxy) hn
      exact ⟨f j, (hm _ _).mpr (by simpa using hx), (hm _ _).mpr (by simpa using hy)⟩)
  have he : g'.edgeFinset.card = g.edgeFinset.card :=
    (SimpleGraph.Iso.comap e.symm g).card_edgeFinset_eq
  have hsum : (∑ j : Fin (Fintype.card B), (Fintype.card A - (b' j).card)) ≤
      Fintype.card B * Fintype.card A := by
    calc
      _ ≤ ∑ _j : Fin (Fintype.card B), Fintype.card A :=
        Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
      _ = _ := by simp
  omega

-- Two vertex-disjoint incidences force every independent block to omit at least two vertices.
lemma omissions (j : Ix) : ∃ u v, u ≠ v ∧ ¬ blockProp j u ∧ ¬ blockProp j v := by
  classical
  let p₀ : V := .inl (0, 0)
  let l₀ : V := .inr (0, 0)
  let p₁ : V := .inl (0, 1)
  let l₁ : V := .inr (0, 1)
  have miss (x y : V) (h : G.Adj x y) : ∃ z, (z = x ∨ z = y) ∧ ¬ blockProp j z := by
    by_cases hx : blockProp j x
    · exact ⟨y, Or.inr rfl, fun hy => blocks_indep j x hx y hy h⟩
    · exact ⟨x, Or.inl rfl, hx⟩
  obtain ⟨u, hu, hu'⟩ := miss p₀ l₀ rfl
  obtain ⟨v, hv, hv'⟩ := miss p₁ l₁ rfl
  have huv : u ≠ v := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> decide
  exact ⟨u, v, huv, hu', hv'⟩

lemma ix_card : Fintype.card Ix = 16430 := by
  simp [Ix, Fintype.card_sum, Fintype.card_prod]

lemma vertex_card : Fintype.card V = 3 * Q ^ 3 := by
  simp only [V, Pt, Ln, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

lemma cost_lt_edges : Fintype.card Ix * Fintype.card V < G.edgeFinset.card := by
  apply lt_of_lt_of_le _ edges_ge
  rw [ix_card, vertex_card]
  decide

end PEqualNP.Outside.L_meta_3577

open PEqualNP.Outside.L_meta_3577

theorem PEqualNP.Outside.L_meta_3577 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  apply transport_refutation G side blockProp side_adj no_four _ blocks_indep blocks_mem blocks_omit omissions blocks_pair cost_lt_edges
  rw [ix_card]
  decide
