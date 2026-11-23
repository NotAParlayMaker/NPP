import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_903_aux

private def hasEdge (es : List (Fin 8 × Fin 8)) (u v : Fin 8) : Bool :=
  es.any (fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u))

private def adjB (es : List (Fin 8 × Fin 8)) (u v : Fin 8) : Bool :=
  (u != v) && hasEdge es u v

private theorem hasEdge_symm (es : List (Fin 8 × Fin 8)) (u v : Fin 8) :
    hasEdge es u v = hasEdge es v u := by
  unfold hasEdge
  congr 1
  funext e
  cases (e.1 == u) <;> cases (e.2 == v) <;> cases (e.1 == v) <;> cases (e.2 == u) <;> rfl

private theorem adjB_symm (es : List (Fin 8 × Fin 8)) (u v : Fin 8) :
    adjB es u v = adjB es v u := by
  unfold adjB
  rw [hasEdge_symm]
  cases h : (u == v)
  · have h' : (v == u) = false := by
      simp only [beq_eq_false_iff_ne] at h ⊢; exact h.symm
    simp [bne, h, h']
  · have h' : (v == u) = true := by
      simp only [beq_iff_eq] at h ⊢; exact h.symm
    simp [bne, h, h']

private def graphOf (es : List (Fin 8 × Fin 8)) : SimpleGraph (Fin 8) where
  Adj u v := adjB es u v = true
  symm := ⟨fun u v h => by rw [adjB_symm]; exact h⟩
  loopless := ⟨fun u h => by simp [adjB] at h⟩

private theorem edgeFinset_card_eq (es : List (Fin 8 × Fin 8))
    [DecidableRel (graphOf es).Adj]
    (hcard : ((Finset.univ : Finset (Fin 8 × Fin 8)).filter
      (fun p => p.1 < p.2 ∧ adjB es p.1 p.2 = true)).card = 7) :
    (graphOf es).edgeFinset.card = 7 := by
  rw [← hcard]
  symm
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact SimpleGraph.mem_edgeFinset.mpr hp.2
  · intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have hlt1 : p1.1.val < p1.2.val := hp1.1
      have hlt2 : p2.1.val < p2.2.val := hp2.1
      rw [h1, h2] at hlt1
      omega
  · intro e he
    have he' : e ∈ (graphOf es).edgeSet := SimpleGraph.mem_edgeFinset.mp he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : (graphOf es).Adj u v := he'
      have hne : u ≠ v := hadj.ne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨(u, v), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, hadj⟩
      · refine ⟨(v, u), ?_, Sym2.eq_swap⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hgt, hadj.symm⟩

private theorem isAcyclic_of_parent (G : SimpleGraph (Fin 8))
    (par : Fin 8 → Fin 8) (dep : Fin 8 → ℕ)
    (hpar : ∀ u v : Fin 8, G.Adj u v →
      (u = par v ∧ dep u < dep v) ∨ (v = par u ∧ dep v < dep u)) :
    G.IsAcyclic := by
  intro v c hc
  have hne_supp : c.support.toFinset.Nonempty :=
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  obtain ⟨w, hw_mem, hw_max⟩ := Finset.exists_max_image c.support.toFinset dep hne_supp
  have hw_supp : w ∈ c.support := List.mem_toFinset.mp hw_mem
  let c' := c.rotate w hw_supp
  have hc' : c'.IsCycle := hc.rotate hw_supp
  have hle_w : ∀ u ∈ c'.support, dep u ≤ dep w := by
    intro u hu
    have hu' : u ∈ c.support := (SimpleGraph.Walk.mem_support_rotate_iff c w hw_supp).mp hu
    exact hw_max u (List.mem_toFinset.mpr hu')
  have hlen : 3 ≤ c'.length := hc'.three_le_length
  have hnodup : c'.edges.Nodup := hc'.edges_nodup
  have hed_len : c'.edges.length = c'.length := SimpleGraph.Walk.length_edges c'
  cases hcw : c' with
  | nil => exact absurd hcw hc'.ne_nil
  | cons hadj_a p1 =>
    rename_i a
    have ha_supp : a ∈ c'.support := by
      rw [hcw]; simp
    have hrev_ne : c'.reverse ≠ SimpleGraph.Walk.nil := by
      intro hnil
      have hlen0 : c'.reverse.length = 0 := by rw [hnil]; rfl
      rw [SimpleGraph.Walk.length_reverse] at hlen0
      omega
    cases hcr : c'.reverse with
    | nil => exact absurd hcr hrev_ne
    | cons hadj_b p2 =>
      rename_i b
      have hb_supp : b ∈ c'.support := by
        have hb' : b ∈ c'.reverse.support := by rw [hcr]; simp
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hb'
      have ha_dep : dep a ≤ dep w := hle_w a ha_supp
      have hb_dep : dep b ≤ dep w := hle_w b hb_supp
      have ha_par : a = par w := by
        rcases hpar w a hadj_a with ⟨_, hlt⟩ | ⟨heq, _⟩
        · omega
        · exact heq
      have hb_par : b = par w := by
        rcases hpar w b hadj_b with ⟨_, hlt⟩ | ⟨heq, _⟩
        · omega
        · exact heq
      have hab : a = b := ha_par.trans hb_par.symm
      have hed_eq : c'.edges = s(w, a) :: p1.edges := by
        rw [hcw]; rfl
      have hlast : c'.edges.getLast? = some s(w, b) := by
        have hrev_ed : c'.reverse.edges = s(w, b) :: p2.edges := by
          rw [hcr]; rfl
        have hhead_rev := congrArg List.head? hrev_ed
        rw [SimpleGraph.Walk.edges_reverse, List.head?_reverse] at hhead_rev
        simpa using hhead_rev
      rw [hed_eq] at hnodup hed_len hlast
      rcases hp1 : p1.edges with _ | ⟨e1, rest2⟩
      · rw [hp1] at hed_len; simp at hed_len; omega
      · rw [hp1] at hlast hnodup
        have hlast_mem : s(w, b) ∈ e1 :: rest2 := by
          rw [List.getLast?_cons_cons] at hlast
          exact List.mem_of_getLast? hlast
        rw [← hab] at hlast_mem
        exact (List.nodup_cons.mp hnodup).1 hlast_mem

private theorem cover_ge_matching :
    ∀ (M : List (Fin 8 × Fin 8)) (T : Finset (Fin 8)),
      (M.flatMap (fun e => [e.1, e.2])).Nodup →
      (∀ e ∈ M, e.1 ∈ T ∨ e.2 ∈ T) →
      M.length ≤ T.card := by
  intro M
  induction M with
  | nil => intros; exact Nat.zero_le _
  | cons e rest ih =>
    intro T hnodup hcov
    have hflat : (e :: rest).flatMap (fun p => [p.1, p.2]) =
        e.1 :: e.2 :: rest.flatMap (fun p => [p.1, p.2]) := rfl
    rw [hflat] at hnodup
    obtain ⟨h1_not, hnodup2⟩ := List.nodup_cons.mp hnodup
    obtain ⟨h2_not, hnodup_rest⟩ := List.nodup_cons.mp hnodup2
    have step : ∀ w : Fin 8, w ∈ T → w ∉ rest.flatMap (fun p => [p.1, p.2]) →
        (e :: rest).length ≤ T.card := by
      intro w hwT hw_not
      have hrest_cov : ∀ p ∈ rest, p.1 ∈ T.erase w ∨ p.2 ∈ T.erase w := by
        intro p hp
        have h1ne : p.1 ≠ w := by
          intro h; rw [← h] at hw_not
          exact hw_not (List.mem_flatMap.mpr ⟨p, hp, by simp⟩)
        have h2ne : p.2 ≠ w := by
          intro h; rw [← h] at hw_not
          exact hw_not (List.mem_flatMap.mpr ⟨p, hp, by simp⟩)
        rcases hcov p (List.mem_cons_of_mem e hp) with h1 | h2
        · exact Or.inl (Finset.mem_erase.mpr ⟨h1ne, h1⟩)
        · exact Or.inr (Finset.mem_erase.mpr ⟨h2ne, h2⟩)
      have hih := ih (T.erase w) hnodup_rest hrest_cov
      have hcard := Finset.card_erase_add_one hwT
      simp only [List.length_cons]
      omega
    rcases hcov e (List.mem_cons_self ..) with h1 | h2
    · exact step e.1 h1 (fun hm => h1_not (List.mem_cons_of_mem e.2 hm))
    · exact step e.2 h2 h2_not

private theorem eval_eq_seven (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 : Fin 8)
    [DecidableRel (graphOf [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)]).Adj]
    (hne : ∀ e ∈ ([(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] : List (Fin 8 × Fin 8)), e.1 ≠ e.2) :
    (fun x : Fin 8 → Bool =>
      (x a1 && x b1) || (x a2 && x b2) || (x a3 && x b3) || (x a4 && x b4) ||
      (x a5 && x b5) || (x a6 && x b6) || (x a7 && x b7)) =
    (fun x : Fin 8 → Bool =>
      decide (∃ i j : Fin 8,
        (graphOf [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)]).Adj i j ∧
        x i = true ∧ x j = true)) := by
  let es : List (Fin 8 × Fin 8) :=
    [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)]
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  have hor : (((x a1 && x b1) || (x a2 && x b2) || (x a3 && x b3) || (x a4 && x b4) ||
      (x a5 && x b5) || (x a6 && x b6) || (x a7 && x b7)) = true) ↔
      ∃ e ∈ es, x e.1 = true ∧ x e.2 = true := by
    simp only [es, Bool.or_eq_true, Bool.and_eq_true, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ((((((h | h) | h) | h) | h) | h) | h)
      · exact ⟨(a1, b1), Or.inl rfl, h⟩
      · exact ⟨(a2, b2), Or.inr (Or.inl rfl), h⟩
      · exact ⟨(a3, b3), Or.inr (Or.inr (Or.inl rfl)), h⟩
      · exact ⟨(a4, b4), Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
      · exact ⟨(a5, b5), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h⟩
      · exact ⟨(a6, b6), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), h⟩
      · exact ⟨(a7, b7), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), h⟩
    · rintro ⟨e, hmem, hx⟩
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hx)))
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  rw [hor]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    refine ⟨e.1, e.2, ?_, h1, h2⟩
    show adjB es e.1 e.2 = true
    unfold adjB hasEdge
    rw [Bool.and_eq_true, bne_iff_ne, List.any_eq_true]
    exact ⟨hne e he, ⟨e, he, by simp⟩⟩
  · rintro ⟨i, j, hadj, hi, hj⟩
    change adjB es i j = true at hadj
    unfold adjB hasEdge at hadj
    rw [Bool.and_eq_true, List.any_eq_true] at hadj
    obtain ⟨_, ⟨e, he, hcond⟩⟩ := hadj
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨e, he, hi, hj⟩
    · exact ⟨e, he, hj, hi⟩

private theorem hasCircuitSize_mono {n s1 s2 : ℕ} {f : (Fin n → Bool) → Bool}
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s1) (hle : s1 ≤ s2) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s2 := by
  obtain ⟨C, hF, hsz, hev⟩ := h
  exact ⟨C, hF, hsz.trans hle, hev⟩

theorem tree_exact (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 : Fin 8)
    (k val : ℕ)
    (par : Fin 8 → Fin 8) (dep : Fin 8 → ℕ)
    (T : Finset (Fin 8)) (M : List (Fin 8 × Fin 8))
    (hne : ∀ e ∈ ([(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] : List (Fin 8 × Fin 8)), e.1 ≠ e.2)
    (hcard : ((Finset.univ : Finset (Fin 8 × Fin 8)).filter
      (fun p => p.1 < p.2 ∧ adjB [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] p.1 p.2 = true)).card = 7)
    (hpar : ∀ u v : Fin 8, adjB [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] u v = true →
      (u = par v ∧ dep u < dep v) ∨ (v = par u ∧ dep v < dep u))
    (hnonempty : adjB [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] a1 b1 = true)
    (hTcov : ∀ u v : Fin 8, adjB [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] u v = true → u ∈ T ∨ v ∈ T)
    (hTcard : T.card = k)
    (hMlen : M.length = k)
    (hMadj : ∀ e ∈ M, adjB [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)] e.1 e.2 = true)
    (hMnodup : (M.flatMap (fun e => [e.1, e.2])).Nodup)
    (hval : 7 + k - 1 = val) :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x a1 && x b1) || (x a2 && x b2) || (x a3 && x b3) || (x a4 && x b4) ||
      (x a5 && x b5) || (x a6 && x b6) || (x a7 && x b7)) s ↔ val ≤ s := by
  let es : List (Fin 8 × Fin 8) :=
    [(a1, b1), (a2, b2), (a3, b3), (a4, b4), (a5, b5), (a6, b6), (a7, b7)]
  let G := graphOf es
  let _ : DecidableRel G.Adj := fun u v => show Decidable (adjB es u v = true) from inferInstance
  have heval := eval_eq_seven a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 hne
  have hE : G.edgeFinset.card = 7 := edgeFinset_card_eq es hcard
  have hAcyc : G.IsAcyclic := isAcyclic_of_parent G par dep hpar
  have hMin : ∀ U : Finset (Fin 8), (∀ i j : Fin 8, G.Adj i j → i ∈ U ∨ j ∈ U) → k ≤ U.card := by
    intro U hU
    rw [← hMlen]
    exact cover_ge_matching M U hMnodup (fun e he => hU e.1 e.2 (hMadj e he))
  intro s
  rw [heval]
  constructor
  · intro hs
    have hlow := PEqualNP.MetaComplexity.L104 8 k s G hAcyc ⟨a1, b1, hnonempty⟩ hMin hs
    rw [hE] at hlow
    omega
  · intro hle
    have hup := PEqualNP.MetaComplexity.L105 8 G T ⟨a1, b1, hnonempty⟩ hTcov
    rw [hE, hTcard, hval] at hup
    exact hasCircuitSize_mono hup hle

end PEqualNP.Outside.L_meta_903_aux

theorem PEqualNP.Outside.L_meta_903 : (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x1 : Fin 8 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6) || (x1 0 && x1 7)) s1 ↔ 7 ≤ s1) ∧ (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x2 : Fin 8 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 0 && x2 6) || (x2 1 && x2 7)) s2 ↔ 8 ≤ s2) ∧ (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x3 : Fin 8 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 1 && x3 6) || (x3 2 && x3 7)) s3 ↔ 8 ≤ s3) ∧ (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x4 : Fin 8 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 0 && x4 5) || (x4 1 && x4 6) || (x4 1 && x4 7)) s4 ↔ 8 ≤ s4) ∧ (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x5 : Fin 8 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 0 && x5 5) || (x5 1 && x5 6) || (x5 2 && x5 7)) s5 ↔ 9 ≤ s5) ∧ (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x6 : Fin 8 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 1 && x6 5) || (x6 2 && x6 6) || (x6 2 && x6 7)) s6 ↔ 8 ≤ s6) ∧ (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x7 : Fin 8 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 0 && x7 3) || (x7 0 && x7 4) || (x7 1 && x7 5) || (x7 1 && x7 6) || (x7 1 && x7 7)) s7 ↔ 8 ≤ s7) ∧ (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x8 : Fin 8 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 1 && x8 3) || (x8 1 && x8 4) || (x8 1 && x8 5) || (x8 2 && x8 6) || (x8 6 && x8 7)) s8 ↔ 9 ≤ s8) ∧ (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x9 : Fin 8 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 0 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6) || (x9 5 && x9 7)) s9 ↔ 9 ≤ s9) ∧ (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x10 : Fin 8 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 1 && x10 5) || (x10 1 && x10 6) || (x10 2 && x10 7)) s10 ↔ 9 ≤ s10) ∧ (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x11 : Fin 8 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 1 && x11 5) || (x11 1 && x11 6) || (x11 2 && x11 7)) s11 ↔ 9 ≤ s11) ∧ (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x12 : Fin 8 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 0 && x12 4) || (x12 1 && x12 5) || (x12 2 && x12 6) || (x12 3 && x12 7)) s12 ↔ 10 ≤ s12) ∧ (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x13 : Fin 8 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 1 && x13 5) || (x13 2 && x13 6) || (x13 6 && x13 7)) s13 ↔ 9 ≤ s13) ∧ (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x14 : Fin 8 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 3 && x14 5) || (x14 3 && x14 6) || (x14 4 && x14 7)) s14 ↔ 9 ≤ s14) ∧ (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x15 : Fin 8 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 1 && x15 4) || (x15 2 && x15 5) || (x15 5 && x15 6) || (x15 5 && x15 7)) s15 ↔ 9 ≤ s15) ∧ (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x16 : Fin 8 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 0 && x16 3) || (x16 1 && x16 4) || (x16 2 && x16 5) || (x16 4 && x16 6) || (x16 4 && x16 7)) s16 ↔ 9 ≤ s16) ∧ (∀ s17 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x17 : Fin 8 → Bool => (x17 0 && x17 1) || (x17 0 && x17 2) || (x17 0 && x17 3) || (x17 1 && x17 4) || (x17 2 && x17 5) || (x17 4 && x17 6) || (x17 5 && x17 7)) s17 ↔ 9 ≤ s17) ∧ (∀ s18 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x18 : Fin 8 → Bool => (x18 0 && x18 1) || (x18 0 && x18 2) || (x18 0 && x18 3) || (x18 1 && x18 4) || (x18 1 && x18 5) || (x18 2 && x18 6) || (x18 2 && x18 7)) s18 ↔ 9 ≤ s18) ∧ (∀ s19 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x19 : Fin 8 → Bool => (x19 0 && x19 1) || (x19 0 && x19 2) || (x19 0 && x19 3) || (x19 1 && x19 4) || (x19 1 && x19 5) || (x19 2 && x19 6) || (x19 3 && x19 7)) s19 ↔ 9 ≤ s19) ∧ (∀ s20 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x20 : Fin 8 → Bool => (x20 0 && x20 1) || (x20 0 && x20 2) || (x20 0 && x20 3) || (x20 1 && x20 4) || (x20 2 && x20 5) || (x20 3 && x20 6) || (x20 4 && x20 7)) s20 ↔ 10 ≤ s20) ∧ (∀ s21 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x21 : Fin 8 → Bool => (x21 0 && x21 1) || (x21 0 && x21 2) || (x21 1 && x21 3) || (x21 1 && x21 4) || (x21 2 && x21 5) || (x21 3 && x21 6) || (x21 5 && x21 7)) s21 ↔ 10 ≤ s21) ∧ (∀ s22 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x22 : Fin 8 → Bool => (x22 0 && x22 1) || (x22 0 && x22 2) || (x22 0 && x22 3) || (x22 1 && x22 4) || (x22 1 && x22 5) || (x22 2 && x22 6) || (x22 4 && x22 7)) s22 ↔ 10 ≤ s22) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 0 5 0 6 0 7 1 7
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (0 : Fin 8) | 6 => (0 : Fin 8) | 7 => (0 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | _ => 0)
      ({(0 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 0 5 0 6 1 7 2 8
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (0 : Fin 8) | 6 => (0 : Fin 8) | 7 => (1 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 1 3 1 4 1 5 1 6 2 7 2 8
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (1 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (1 : Fin 8) | 7 => (2 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(1 : Fin 8), (2 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 0 5 1 6 1 7 2 8
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (0 : Fin 8) | 6 => (1 : Fin 8) | 7 => (1 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (6 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 0 5 1 6 2 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (0 : Fin 8) | 6 => (1 : Fin 8) | 7 => (2 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (2 : Fin 8)}) ([((0 : Fin 8), (3 : Fin 8)), ((1 : Fin 8), (6 : Fin 8)), ((2 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 1 3 1 4 1 5 2 6 2 7 2 8
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (1 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (2 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(1 : Fin 8), (2 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (6 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 1 5 1 6 1 7 2 8
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (1 : Fin 8) | 6 => (1 : Fin 8) | 7 => (1 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (5 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 1 3 1 4 1 5 2 6 6 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (1 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (6 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (6 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (3 : Fin 8)), ((6 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 1 5 2 6 5 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (5 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 2 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (2 : Fin 8), (5 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (6 : Fin 8)), ((5 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 1 5 1 6 2 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (1 : Fin 8) | 7 => (2 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (2 : Fin 8)}) ([((0 : Fin 8), (3 : Fin 8)), ((1 : Fin 8), (4 : Fin 8)), ((2 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 1 5 1 6 2 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (1 : Fin 8) | 6 => (1 : Fin 8) | 7 => (2 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (2 : Fin 8)}) ([((0 : Fin 8), (3 : Fin 8)), ((1 : Fin 8), (5 : Fin 8)), ((2 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 0 4 1 5 2 6 3 7 4 10
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (0 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (3 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (2 : Fin 8), (3 : Fin 8)}) ([((0 : Fin 8), (4 : Fin 8)), ((1 : Fin 8), (5 : Fin 8)), ((2 : Fin 8), (6 : Fin 8)), ((3 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 1 5 2 6 6 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (6 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (6 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (4 : Fin 8)), ((6 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 1 3 2 4 3 5 3 6 4 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (1 : Fin 8) | 4 => (2 : Fin 8) | 5 => (3 : Fin 8) | 6 => (3 : Fin 8) | 7 => (4 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 3 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (3 : Fin 8), (4 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (4 : Fin 8)), ((3 : Fin 8), (5 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 1 3 1 4 2 5 5 6 5 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (1 : Fin 8) | 4 => (1 : Fin 8) | 5 => (2 : Fin 8) | 6 => (5 : Fin 8) | 7 => (5 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 3 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (5 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (3 : Fin 8)), ((5 : Fin 8), (6 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 2 5 4 6 4 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (2 : Fin 8) | 6 => (4 : Fin 8) | 7 => (4 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (2 : Fin 8), (4 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (5 : Fin 8)), ((4 : Fin 8), (6 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 2 5 4 6 5 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (2 : Fin 8) | 6 => (4 : Fin 8) | 7 => (5 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (4 : Fin 8), (5 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (5 : Fin 8)), ((4 : Fin 8), (6 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 1 5 2 6 2 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (2 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (2 : Fin 8)}) ([((0 : Fin 8), (3 : Fin 8)), ((1 : Fin 8), (4 : Fin 8)), ((2 : Fin 8), (6 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 1 5 2 6 3 7 3 9
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (3 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 2 | _ => 0)
      ({(1 : Fin 8), (2 : Fin 8), (3 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (6 : Fin 8)), ((3 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 2 5 3 6 4 7 4 10
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (2 : Fin 8) | 6 => (3 : Fin 8) | 7 => (4 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (2 : Fin 8), (3 : Fin 8), (4 : Fin 8)}) ([((0 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (5 : Fin 8)), ((3 : Fin 8), (6 : Fin 8)), ((4 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 1 3 1 4 2 5 3 6 5 7 4 10
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (1 : Fin 8) | 4 => (1 : Fin 8) | 5 => (2 : Fin 8) | 6 => (3 : Fin 8) | 7 => (5 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 3 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (3 : Fin 8), (5 : Fin 8)}) ([((0 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (4 : Fin 8)), ((3 : Fin 8), (6 : Fin 8)), ((5 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_903_aux.tree_exact 0 1 0 2 0 3 1 4 1 5 2 6 4 7 4 10
      (fun i : Fin 8 => match i.val with | 0 => (0 : Fin 8) | 1 => (0 : Fin 8) | 2 => (0 : Fin 8) | 3 => (0 : Fin 8) | 4 => (1 : Fin 8) | 5 => (1 : Fin 8) | 6 => (2 : Fin 8) | 7 => (4 : Fin 8) | _ => 0)
      (fun i : Fin 8 => match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 3 | _ => 0)
      ({(0 : Fin 8), (1 : Fin 8), (2 : Fin 8), (4 : Fin 8)}) ([((0 : Fin 8), (3 : Fin 8)), ((1 : Fin 8), (5 : Fin 8)), ((2 : Fin 8), (6 : Fin 8)), ((4 : Fin 8), (7 : Fin 8))])
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
