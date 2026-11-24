import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4863

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def OK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Good {n : ℕ} (gs : List Gate) (k : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  k < n + gs.length ∧ ∀ x : Fin n → Bool, (gs.foldl stepWire (List.ofFn x)).getD k false = f x

lemma ok_nil : OK [] := by
  intro g hg
  simp at hg

lemma ok_gate {gs : List Gate} (h : OK gs) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (i j : ℕ) : OK (gs ++ [⟨op, [i, j]⟩]) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | hg
  · exact h g hg
  · subst hg
    exact ⟨hop, by simp⟩

lemma good_congr {n : ℕ} {gs : List Gate} {k : ℕ} {f g : (Fin n → Bool) → Bool}
    (h : Good gs k f) (e : ∀ x, f x = g x) : Good gs k g :=
  ⟨h.1, fun x => (h.2 x).trans (e x)⟩

lemma good_var {n : ℕ} (gs : List Gate) (v : Fin n) :
    Good (n := n) gs (v : ℕ) (fun x => x v) := by
  refine ⟨by omega, fun x => ?_⟩
  rw [foldl_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma good_append {n : ℕ} {gs : List Gate} {k : ℕ} {f : (Fin n → Bool) → Bool}
    (h : Good gs k f) (hs : List Gate) : Good (gs ++ hs) k f := by
  refine ⟨by simp; have := h.1; omega, fun x => ?_⟩
  rw [List.foldl_append, foldl_getD_lt _ _ _ (by rw [foldl_length]; simp; exact h.1)]
  exact h.2 x

lemma good_gate {n : ℕ} {gs : List Gate} {i j : ℕ} {f g : (Fin n → Bool) → Bool} (op : GateOp)
    (hi : Good gs i f) (hj : Good gs j g) :
    Good (gs ++ [⟨op, [i, j]⟩]) (n + gs.length) (fun x => op.eval [f x, g x]) := by
  refine ⟨by simp, fun x => ?_⟩
  have hl : (gs.foldl stepWire (List.ofFn x)).length = n + gs.length := by
    rw [foldl_length]; simp
  have h1 := hi.2 x
  have h2 := hj.2 x
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize gs.foldl stepWire (List.ofFn x) = w at hl h1 h2 ⊢
  rw [stepWire, List.getD_eq_getElem?_getD, ← hl, List.getElem?_append_right (le_refl _)]
  rw [List.getD_eq_getElem?_getD] at h1 h2
  simp [h1, h2]

def Inv {n : ℕ} (f : (Fin n → Bool) → Bool) (b : ℕ) : Prop :=
  (∀ x, f x = false) ∨ ∃ gs k, OK gs ∧ Good gs k f ∧ gs.length < b

lemma inv_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {b c : ℕ} (h : Inv f b) (hbc : b ≤ c) :
    Inv f c := by
  rcases h with h | ⟨gs, k, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨gs, k, h1, h2, by omega⟩

lemma inv_var {n : ℕ} {f : (Fin n → Bool) → Bool} {b : ℕ} (h : Inv f b) (a : Fin n) :
    Inv (fun x => x a || f x) (b + 1) := by
  rcases h with h | ⟨gs, k, h1, h2, h3⟩
  · right
    refine ⟨[], a, ok_nil, good_congr (good_var [] a) ?_, by simp⟩
    intro x
    simp [h x]
  · right
    refine ⟨gs ++ [⟨GateOp.or, [a, k]⟩], n + gs.length, ok_gate h1 _ (Or.inr rfl) _ _,
      good_congr (good_gate GateOp.or (good_var gs a) h2) ?_, by simp; omega⟩
    intro x
    simp [GateOp.eval]

lemma orSet {n : ℕ} (gs : List Gate) (hgs : OK gs) (T : Finset (Fin n)) (hT : T.Nonempty) :
    ∃ hs k, OK (gs ++ hs) ∧ hs.length + 1 = T.card ∧
      Good (gs ++ hs) k (fun x => decide (∃ v ∈ T, x v = true)) := by
  induction T using Finset.induction_on with
  | empty => exact absurd hT (by simp)
  | insert a S ha ih =>
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      refine ⟨[], a, by simpa using hgs, by simp, good_congr (good_var _ a) ?_⟩
      intro x
      simp
    · obtain ⟨hs, k, h1, h2, h3⟩ := ih hS
      refine ⟨hs ++ [⟨GateOp.or, [a, k]⟩], n + (gs ++ hs).length, ?_, ?_, ?_⟩
      · rw [← List.append_assoc]
        exact ok_gate h1 _ (Or.inr rfl) _ _
      · rw [Finset.card_insert_of_notMem ha]
        simp
        omega
      · rw [← List.append_assoc]
        refine good_congr (good_gate GateOp.or (good_var (gs ++ hs) a) h3) ?_
        intro x
        simp [GateOp.eval, Finset.exists_mem_insert]

lemma inv_star {n : ℕ} {f : (Fin n → Bool) → Bool} {b : ℕ} (h : Inv f b) (c : Fin n)
    (T : Finset (Fin n)) :
    Inv (fun x => decide (x c = true ∧ ∃ v ∈ T, x v = true) || f x) (b + (T.card + 1)) := by
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst hT
    have e : (fun x => decide (x c = true ∧ ∃ v ∈ (∅ : Finset (Fin n)), x v = true) || f x) = f := by
      funext x
      simp
    rw [e]
    exact inv_mono h (by omega)
  rcases h with h | ⟨gs, k, h1, h2, h3⟩
  · obtain ⟨hs, k', o1, l1, g1⟩ := orSet [] ok_nil T hT
    right
    refine ⟨([] ++ hs) ++ [⟨GateOp.and, [c, k']⟩], n + ([] ++ hs).length,
      ok_gate o1 _ (Or.inl rfl) _ _,
      good_congr (good_gate GateOp.and (good_var _ c) g1) ?_, ?_⟩
    · intro x
      simp [GateOp.eval, h x]
    · simp
      omega
  · obtain ⟨hs, k', o1, l1, g1⟩ := orSet gs h1 T hT
    have g2 := good_gate GateOp.and (good_var (gs ++ hs) c) g1
    have g4 := good_append (good_append h2 hs) [⟨GateOp.and, [c, k']⟩]
    have g5 := good_gate GateOp.or g2 g4
    right
    refine ⟨_, _, ok_gate (ok_gate o1 _ (Or.inl rfl) _ _) _ (Or.inr rfl) _ _, good_congr g5 ?_, ?_⟩
    · intro x
      simp [GateOp.eval]
    · simp
      omega

lemma invA {n : ℕ} (A : Finset (Fin n)) :
    Inv (fun x => decide (∃ a ∈ A, x a = true)) A.card := by
  induction A using Finset.induction_on with
  | empty =>
    left
    intro x
    simp
  | insert a S ha ih =>
    have h2 := inv_var ih a
    rw [Finset.card_insert_of_notMem ha]
    have e : (fun x : Fin n → Bool => x a || decide (∃ b ∈ S, x b = true)) =
        (fun x => decide (∃ b ∈ insert a S, x b = true)) := by
      funext x
      cases hxa : x a <;> simp [hxa, Finset.exists_mem_insert]
    rw [e] at h2
    exact h2

lemma invK {n : ℕ} (T : Fin n → Finset (Fin n)) (f0 : (Fin n → Bool) → Bool) (b0 : ℕ)
    (h0 : Inv f0 b0) (S : Finset (Fin n)) :
    Inv (fun x => decide (∃ c ∈ S, x c = true ∧ ∃ v ∈ T c, x v = true) || f0 x)
      (b0 + ∑ c ∈ S, ((T c).card + 1)) := by
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun x => decide (∃ c ∈ (∅ : Finset (Fin n)), x c = true ∧ ∃ v ∈ T c, x v = true)
        || f0 x) = f0 := by
      funext x
      simp
    rw [e]
    simpa using h0
  | insert a S ha ih =>
    have h2 := inv_star ih a (T a)
    rw [Finset.sum_insert ha]
    have e : (fun x => decide (x a = true ∧ ∃ v ∈ T a, x v = true) ||
        (decide (∃ c ∈ S, x c = true ∧ ∃ v ∈ T c, x v = true) || f0 x)) =
        (fun x => decide (∃ c ∈ insert a S, x c = true ∧ ∃ v ∈ T c, x v = true) || f0 x) := by
      funext x
      rw [← Bool.or_assoc]
      congr 1
      simp [Finset.exists_mem_insert]
    rw [e] at h2
    have hb : b0 + (∑ c ∈ S, ((T c).card + 1)) + ((T a).card + 1) =
        b0 + ((T a).card + 1 + ∑ c ∈ S, ((T c).card + 1)) := by ring
    rw [hb] at h2
    exact h2

lemma inv_circuit {n : ℕ} {f : (Fin n → Bool) → Bool} {b : ℕ} (h : Inv f b) :
    HasCircuitSize n f (b - 1) := by
  rcases h with h | ⟨gs, k, h1, h2, h3⟩
  · refine ⟨⟨[], n⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · simp [Circuit.size]
    · intro x
      simp [Circuit.eval, Circuit.wires, h x, List.getD_eq_getElem?_getD]
  · refine ⟨⟨gs, k⟩, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨ho, hl⟩ := h1 g hg
      refine ⟨?_, hl⟩
      rcases ho with ho | ho <;> simp [ho]
    · simp [Circuit.size]
      omega
    · intro x
      exact h2.2 x

def Tset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K' : Finset (Fin n)) (z : Fin n)
    (c : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => G.Adj c v ∧ v ≠ z ∧ (v ∈ K' → c < v))

lemma mem_Tset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K' : Finset (Fin n))
    (z c v : Fin n) : v ∈ Tset G K' z c ↔ G.Adj c v ∧ v ≠ z ∧ (v ∈ K' → c < v) := by
  simp [Tset]

lemma deg3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (h : (G.neighborSet v).ncard = 3) : G.degree v = 3 := by
  rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact h

lemma edges_ge5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (z : Fin n) (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (hA : ∀ u v, G.Adj u v → u ∉ A) (hzA : z ∉ A) : 5 ≤ G.edgeFinset.card := by
  have hz3 := deg3 G z (hdeg z hzA)
  obtain ⟨u, hzu⟩ := (G.degree_pos_iff_exists_adj z).mp (by omega : 0 < G.degree z)
  have huA : u ∉ A := hA u z (hzu.symm)
  have hu3 := deg3 G u (hdeg u huA)
  have hmem : s(u, z) ∈ G.incidenceFinset u := by
    rw [G.mem_incidenceFinset]
    exact (G.mk'_mem_incidenceSet_left_iff).mpr (hzu.symm)
  have hdisj : Disjoint (G.incidenceFinset z) ((G.incidenceFinset u).erase s(u, z)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_erase] at he2
    have hh : e ∈ G.incidenceSet z ∩ G.incidenceSet u :=
      ⟨G.mem_incidenceFinset.mp he1, G.mem_incidenceFinset.mp he2.2⟩
    rw [G.incidenceSet_inter_incidenceSet_of_adj hzu, Set.mem_singleton_iff] at hh
    exact he2.1 (hh.trans Sym2.eq_swap)
  have hsub : G.incidenceFinset z ∪ (G.incidenceFinset u).erase s(u, z) ⊆ G.edgeFinset :=
    Finset.union_subset (G.incidenceFinset_subset z)
      ((Finset.erase_subset _ _).trans (G.incidenceFinset_subset u))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hmem,
    G.card_incidenceFinset_eq_degree, G.card_incidenceFinset_eq_degree] at h1
  omega

lemma edges_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K' : Finset (Fin n))
    (z : Fin n) (hz3 : G.degree z = 3) (hK' : z ∉ K') :
    ∑ c ∈ K', (Tset G K' z c).card + 3 ≤ G.edgeFinset.card := by
  have hsub : G.incidenceFinset z ⊆ G.edgeFinset := G.incidenceFinset_subset z
  have hI : (G.incidenceFinset z).card = 3 := by
    rw [G.card_incidenceFinset_eq_degree]
    exact hz3
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hinj : (K'.sigma (Tset G K' z)).card ≤ (G.edgeFinset \ G.incidenceFinset z).card := by
    apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
    · rintro ⟨c, v⟩ hp
      rw [Finset.mem_coe, Finset.mem_sigma, mem_Tset] at hp
      obtain ⟨hc, hadj, hvz, -⟩ := hp
      have hcz : c ≠ z := fun h => hK' (h ▸ hc)
      rw [Finset.mem_coe, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, G.mem_incidenceFinset]
      refine ⟨hadj, ?_⟩
      intro h
      have h2 := h.2
      rw [Sym2.mem_iff] at h2
      rcases h2 with h' | h'
      · exact hcz h'.symm
      · exact hvz h'.symm
    · rintro ⟨c, v⟩ hp ⟨c', v'⟩ hp' he
      rw [Finset.mem_coe, Finset.mem_sigma, mem_Tset] at hp hp'
      simp only at he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exfalso
        exact lt_asymm (hp.2.2.2 hp'.1) (hp'.2.2.2 hp.1)
  rw [Finset.card_sigma] at hinj
  omega

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A K : Finset (Fin n))
    (z : Fin n) (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (hA : ∀ u v, G.Adj u v → u ∉ A) (hKA : K ⊆ Aᶜ)
    (hcov : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) (hz : z ∈ K) :
    ∃ s, s + 5 ≤ A.card + G.edgeFinset.card + K.card ∧
      HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x z false)) s := by
  have hzA : z ∉ A := by
    have := hKA hz
    simpa using this
  have hInv := invK (Tset G (K.erase z) z) _ _ (invA A) (K.erase z)
  have hfun : (fun x => NestedCover.graphFun G A (Function.update x z false)) =
      (fun x => decide (∃ c ∈ K.erase z, x c = true ∧ ∃ v ∈ Tset G (K.erase z) z c, x v = true)
        || decide (∃ a ∈ A, x a = true)) := by
    funext x
    have key : ∀ u, (Function.update x z false u = true) ↔ (u ≠ z ∧ x u = true) := by
      intro u
      by_cases h : u = z <;> simp [h]
    apply Bool.eq_iff_iff.mpr
    simp only [NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq, key]
    constructor
    · rintro (⟨a, ha, -, hx⟩ | ⟨u, v, huv, ⟨huz, hu⟩, ⟨hvz, hv⟩⟩)
      · exact Or.inr ⟨a, ha, hx⟩
      · left
        have cov : u ∈ K.erase z ∨ v ∈ K.erase z := by
          rcases hcov u v huv with h | h
          · exact Or.inl (Finset.mem_erase.mpr ⟨huz, h⟩)
          · exact Or.inr (Finset.mem_erase.mpr ⟨hvz, h⟩)
        by_cases hu' : u ∈ K.erase z <;> by_cases hv' : v ∈ K.erase z
        · rcases lt_or_gt_of_ne (G.ne_of_adj huv) with hlt | hlt
          · exact ⟨u, hu', hu, v, (mem_Tset _ _ _ _ _).mpr ⟨huv, hvz, fun _ => hlt⟩, hv⟩
          · exact ⟨v, hv', hv, u, (mem_Tset _ _ _ _ _).mpr ⟨huv.symm, huz, fun _ => hlt⟩, hu⟩
        · exact ⟨u, hu', hu, v, (mem_Tset _ _ _ _ _).mpr ⟨huv, hvz, fun h => absurd h hv'⟩, hv⟩
        · exact ⟨v, hv', hv, u, (mem_Tset _ _ _ _ _).mpr ⟨huv.symm, huz, fun h => absurd h hu'⟩, hu⟩
        · rcases cov with h | h
          · exact absurd h hu'
          · exact absurd h hv'
    · rintro (⟨c, hc, hxc, v, hv, hxv⟩ | ⟨a, ha, hx⟩)
      · right
        rw [mem_Tset] at hv
        exact ⟨c, v, hv.1, ⟨(Finset.mem_erase.mp hc).1, hxc⟩, ⟨hv.2.1, hxv⟩⟩
      · left
        exact ⟨a, ha, fun h => hzA (h ▸ ha), hx⟩
  have hm := edges_count G (K.erase z) z (deg3 G z (hdeg z hzA)) (by simp)
  have h5 := edges_ge5 G A z hdeg hA hzA
  have hK' : (K.erase z).card + 1 = K.card := Finset.card_erase_add_one hz
  refine ⟨A.card + ∑ c ∈ K.erase z, ((Tset G (K.erase z) z c).card + 1) - 1, ?_, ?_⟩
  · rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    omega
  · rw [hfun]
    exact inv_circuit hInv

end PEqualNP.Outside.L_meta_4863

theorem PEqualNP.Outside.L_meta_4863 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : Fin x1), (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → x5 ⊆ x4ᶜ → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x5 ∨ x11 ∈ x5) → x6 ∈ x5 → ∃ (x12 : ℕ), x12 + (5 : ℕ) ≤ x4.card + x2.edgeFinset.card + x5.card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x13 x6 Bool.false)) x12 := by
  intro n G _ A K z hdeg hA hKA hcov hz
  exact PEqualNP.Outside.L_meta_4863.main n G A K z hdeg hA hKA hcov hz
