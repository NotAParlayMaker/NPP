import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5355

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

def V (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wf gs (List.ofFn x)).getD w false

theorem V_old {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n + gs.length) :
    V n (gs ++ hs) x w = V n gs x w :=
  wf_prefix gs hs _ w (by simpa using hw)

theorem V_new {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    V n (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map (V n gs x)) := by
  unfold V
  rw [wf_snoc]
  have h := wf_len gs (List.ofFn x)
  rw [List.length_ofFn] at h
  rw [← h]
  simp [List.getD_eq_getElem?_getD]

theorem V_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) : V n gs x i.val = x i := by
  unfold V
  rw [wf_keep gs _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem V_nil_out {n : ℕ} (x : Fin n → Bool) : V n [] x n = false := by
  unfold V; simp [wf, List.getD_eq_getElem?_getD]

def gA (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

theorem gA_old (gs hs : List Gate) (j : ℕ) (h : j < gs.length) : gA (gs ++ hs) j = gA gs j := by
  simp [gA, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gA_new (gs hs : List Gate) (j : ℕ) (h : gs.length ≤ j) :
    gA (gs ++ hs) j = gA hs (j - gs.length) := by
  simp [gA, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem gA_mem (hs : List Gate) (k : ℕ) (h : (gA hs k).op = GateOp.and) : gA hs k ∈ hs := by
  unfold gA at h ⊢
  rw [List.getD_eq_getElem?_getD] at h ⊢
  cases e : hs[k]? with
  | none => rw [e] at h; simp at h
  | some g => simp only [Option.getD_some]; exact List.mem_of_getElem? e

def orChain (n : ℕ) : List Gate → ℕ → List (Fin n) → List Gate × ℕ
  | gs, c, [] => (gs, c)
  | gs, c, w :: ws => orChain n (gs ++ [⟨GateOp.or, [c, w.val]⟩]) (n + gs.length) ws

theorem orChain_spec {n : ℕ} (ws : List (Fin n)) : ∀ (gs : List Gate) (c : ℕ), c < n + gs.length →
    ∃ hs, (orChain n gs c ws).1 = gs ++ hs ∧ hs.length = ws.length ∧
      (∀ g ∈ hs, g.op = GateOp.or ∧ g.inputs.length = 2) ∧
      (orChain n gs c ws).2 < n + (orChain n gs c ws).1.length ∧
      ∀ x, (V n (orChain n gs c ws).1 x (orChain n gs c ws).2 = true ↔
        (V n gs x c = true ∨ ∃ w ∈ ws, x w = true)) := by
  induction ws with
  | nil => intro gs c hc; exact ⟨[], by simp [orChain], rfl, by simp, by simpa [orChain] using hc,
      fun x => by simp [orChain]⟩
  | cons w ws ih =>
    intro gs c hc
    obtain ⟨hs, h1, h2, h3, h4, h5⟩ := ih (gs ++ [⟨GateOp.or, [c, w.val]⟩]) (n + gs.length)
      (by simp)
    refine ⟨⟨GateOp.or, [c, w.val]⟩ :: hs, ?_, ?_, ?_, ?_, ?_⟩
    · simp [orChain, h1]
    · simp [h2]
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · simp
      · exact h3 g hg
    · simpa [orChain] using h4
    · intro x
      simp only [orChain]
      rw [h5 x, V_new]
      simp [GateOp.eval, V_in, or_assoc]

section
variable {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → Fin n → Prop)

def Own (gs : List Gate) (P : List (Fin n)) : Prop :=
  ∀ j < gs.length, (gA gs j).op = GateOp.and → ∃ v ∈ P,
    (∀ x, V n gs x (n + j) = true ↔ x v = true ∧ ∃ w, A v w ∧ x w = true) ∧
    ∃ u w, G.Adj u w ∧ V n gs (pairInput u w) (n + j) = true ∧
      ∀ i < j, (gA gs i).op = GateOp.and → V n gs (pairInput u w) (n + i) = false

theorem Own_or (gs hs : List Gate) (P : List (Fin n)) (h : Own G A gs P)
    (hh : ∀ g ∈ hs, g.op = GateOp.or) : Own G A (gs ++ hs) P := by
  intro j hj hand
  by_cases hjl : j < gs.length
  · rw [gA_old _ _ _ hjl] at hand
    obtain ⟨v, hv, hsem, u, w, hadj, htrue, hfalse⟩ := h j hjl hand
    refine ⟨v, hv, fun x => ?_, u, w, hadj, ?_, fun i hi hia => ?_⟩
    · rw [V_old _ _ _ _ (by omega)]; exact hsem x
    · rw [V_old _ _ _ _ (by omega)]; exact htrue
    · rw [gA_old _ _ _ (by omega)] at hia
      rw [V_old _ _ _ _ (by omega)]; exact hfalse i hi hia
  · rw [gA_new _ _ _ (by omega)] at hand
    have := hh _ (gA_mem _ _ hand)
    rw [this] at hand; cases hand

theorem Own_mono (gs : List Gate) (P Q : List (Fin n)) (h : Own G A gs P) (hPQ : ∀ v ∈ P, v ∈ Q) :
    Own G A gs Q := by
  intro j hj hand
  obtain ⟨v, hv, rest⟩ := h j hj hand
  exact ⟨v, hPQ v hv, rest⟩

theorem pairInput_true (u w z : Fin n) : pairInput u w z = true ↔ z = u ∨ z = w := by
  simp [pairInput]

theorem Own_and (hAG : ∀ v w, A v w → G.Adj v w) (hAA : ∀ v w, A v w → A w v → False)
    (gs : List Gate) (P : List (Fin n)) (h : Own G A gs P) (v : Fin n) (hv : v ∉ P)
    (c : ℕ) (_hc : c < n + gs.length) (hcs : ∀ x, V n gs x c = true ↔ ∃ w, A v w ∧ x w = true)
    (w1 : Fin n) (hw1 : A v w1) :
    Own G A (gs ++ [⟨GateOp.and, [v.val, c]⟩]) (P ++ [v]) := by
  have hsem : ∀ x, V n (gs ++ [⟨GateOp.and, [v.val, c]⟩]) x (n + gs.length) = true ↔
      x v = true ∧ ∃ w, A v w ∧ x w = true := by
    intro x
    rw [V_new]
    simp only [List.map_cons, List.map_nil, GateOp.eval, V_in]
    rw [← hcs x]
    simp
  intro j hj hand
  by_cases hjl : j < gs.length
  · rw [gA_old _ _ _ hjl] at hand
    obtain ⟨v', hv', hsem', u, w, hadj, htrue, hfalse⟩ := h j hjl hand
    refine ⟨v', List.mem_append_left _ hv', fun x => ?_, u, w, hadj, ?_, fun i hi hia => ?_⟩
    · rw [V_old _ _ _ _ (by omega)]; exact hsem' x
    · rw [V_old _ _ _ _ (by omega)]; exact htrue
    · rw [gA_old _ _ _ (by omega)] at hia
      rw [V_old _ _ _ _ (by omega)]; exact hfalse i hi hia
  · have hje : j = gs.length := by simp at hj; omega
    subst hje
    refine ⟨v, by simp, hsem, v, w1, hAG _ _ hw1, ?_, fun i hi hia => ?_⟩
    · exact (hsem _).2 ⟨by simp [pairInput], w1, hw1, by simp [pairInput]⟩
    · rw [gA_old _ _ _ hi] at hia
      obtain ⟨v', hv', hsem', -⟩ := h i hi hia
      rw [V_old _ _ _ _ (by omega)]
      by_contra hne
      simp only [Bool.not_eq_false] at hne
      obtain ⟨h1, w, hw, h2⟩ := (hsem' _).1 hne
      rw [pairInput_true] at h1 h2
      have hvv : v' ≠ v := fun e => hv (e ▸ hv')
      rcases h1 with h1 | h1
      · exact hvv h1
      · subst h1
        rcases h2 with h2 | h2
        · subst h2; exact hAA _ _ hw1 hw
        · subst h2; exact (hAG _ _ hw).ne rfl
end

def blockStep (n : ℕ) (st : List Gate × Option ℕ) (v : Fin n) (l : List (Fin n)) :
    List Gate × Option ℕ :=
  match l with
  | [] => st
  | w1 :: ws =>
    match st.2 with
    | none => ((orChain n st.1 w1.val ws).1 ++ [⟨GateOp.and, [v.val, (orChain n st.1 w1.val ws).2]⟩],
        some (n + (orChain n st.1 w1.val ws).1.length))
    | some c => ((orChain n st.1 w1.val ws).1 ++ [⟨GateOp.and, [v.val, (orChain n st.1 w1.val ws).2]⟩] ++
        [⟨GateOp.or, [c, n + (orChain n st.1 w1.val ws).1.length]⟩],
        some (n + ((orChain n st.1 w1.val ws).1 ++
          [(⟨GateOp.and, [v.val, (orChain n st.1 w1.val ws).2]⟩ : Gate)]).length))

section
variable {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → Fin n → Prop) (N : Fin n → List (Fin n))

def Inv (P : List (Fin n)) (st : List Gate × Option ℕ) : Prop :=
  (∀ g ∈ st.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  Own G A st.1 P ∧
  (st.2 = none → st.1 = [] ∧ ∀ v ∈ P, ∀ w, ¬ A v w) ∧
  (∀ c, st.2 = some c → c < n + st.1.length ∧
     (∀ x, V n st.1 x c = true ↔ ∃ v ∈ P, x v = true ∧ ∃ w, A v w ∧ x w = true) ∧
     st.1.length + 1 ≤ (P.map fun v => (N v).length).sum + P.length)

theorem and_sem (gs : List Gate) (v : Fin n) (c : ℕ) (p : (Fin n → Bool) → Prop)
    (hcs : ∀ x : Fin n → Bool, V n gs x c = true ↔ p x) (x : Fin n → Bool) :
    V n (gs ++ [⟨GateOp.and, [v.val, c]⟩]) x (n + gs.length) = true ↔ x v = true ∧ p x := by
  rw [V_new]
  simp only [List.map_cons, List.map_nil, GateOp.eval, V_in]
  rw [← hcs x]
  simp

theorem Inv_step (hAG : ∀ v w, A v w → G.Adj v w) (hAA : ∀ v w, A v w → A w v → False)
    (hN : ∀ v w, w ∈ N v ↔ A v w) (P : List (Fin n)) (st : List Gate × Option ℕ)
    (h : Inv G A N P st) (v : Fin n) (hv : v ∉ P) :
    Inv G A N (P ++ [v]) (blockStep n st v (N v)) := by
  obtain ⟨st1, st2⟩ := st
  obtain ⟨hm, ho, hnone, hsome⟩ := h
  simp only at hm ho hnone hsome
  cases hNv : N v with
  | nil =>
    have hnoA : ∀ w, ¬ A v w := fun w hw => by
      have := (hN v w).2 hw; rw [hNv] at this; simp at this
    simp only [blockStep]
    refine ⟨hm, Own_mono G A _ P _ ho (fun v' h => List.mem_append_left _ h), ?_, ?_⟩
    · intro h2
      obtain ⟨h1, h3⟩ := hnone h2
      refine ⟨h1, fun v' hv' => ?_⟩
      rcases List.mem_append.1 hv' with hv' | hv'
      · exact h3 v' hv'
      · rw [List.mem_singleton] at hv'; subst hv'; exact hnoA
    · intro c hc
      obtain ⟨a, b, d⟩ := hsome c hc
      refine ⟨a, fun x => ?_, ?_⟩
      · rw [b x]
        constructor
        · rintro ⟨v', hv', r⟩; exact ⟨v', by simp [hv'], r⟩
        · rintro ⟨v', hv', h1, w, hw, h2⟩
          rcases List.mem_append.1 hv' with hv' | hv'
          · exact ⟨v', hv', h1, w, hw, h2⟩
          · rw [List.mem_singleton] at hv'; subst hv'; exact absurd hw (hnoA w)
      · simp [hNv]; omega
  | cons w1 ws =>
    have hw1 : A v w1 := (hN v w1).1 (by rw [hNv]; simp)
    obtain ⟨hs, e1, e2, e3, e4, e5⟩ := orChain_spec ws st1 w1.val (by omega)
    have hcs : ∀ x, V n (orChain n st1 w1.val ws).1 x (orChain n st1 w1.val ws).2 = true ↔
        ∃ w, A v w ∧ x w = true := by
      intro x
      rw [e5, V_in]
      constructor
      · rintro (h | ⟨w, hw, h⟩)
        · exact ⟨w1, hw1, h⟩
        · exact ⟨w, (hN v w).1 (by rw [hNv]; simp [hw]), h⟩
      · rintro ⟨w, hw, h⟩
        have := (hN v w).2 hw
        rw [hNv] at this
        rcases List.mem_cons.1 this with rfl | hw'
        · exact Or.inl h
        · exact Or.inr ⟨w, hw', h⟩
    have hown1 : Own G A (orChain n st1 w1.val ws).1 P := by
      rw [e1]; exact Own_or G A st1 hs P ho (fun g hg => (e3 g hg).1)
    have hown2 := Own_and G A hAG hAA _ P hown1 v hv _ e4 hcs w1 hw1
    have hsem2 := and_sem (orChain n st1 w1.val ws).1 v (orChain n st1 w1.val ws).2 (fun x => ∃ w, A v w ∧ x w = true) hcs
    have hm2 : ∀ g ∈ (orChain n st1 w1.val ws).1 ++
        [(⟨GateOp.and, [v.val, (orChain n st1 w1.val ws).2]⟩ : Gate)],
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rw [e1] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | rfl
      · exact hm g hg
      · exact ⟨Or.inr (e3 g hg).1, (e3 g hg).2.le⟩
      · simp
    cases st2 with
    | none =>
      obtain ⟨rfl, hP⟩ := hnone rfl
      simp only [blockStep]
      refine ⟨hm2, hown2, by simp, ?_⟩
      intro c hc
      cases hc
      refine ⟨by simp, fun x => ?_, ?_⟩
      · rw [hsem2 x]
        constructor
        · intro h; exact ⟨v, by simp, h⟩
        · rintro ⟨v', hv', h1, w, hw, h2⟩
          rcases List.mem_append.1 hv' with hv' | hv'
          · exact absurd hw (hP v' hv' w)
          · rw [List.mem_singleton] at hv'; subst hv'; exact ⟨h1, w, hw, h2⟩
      · simp [e1, e2, hNv]; omega
    | some c =>
      obtain ⟨hc1, hc2, hc3⟩ := hsome c rfl
      simp only [blockStep]
      refine ⟨?_, Own_or G A _ _ _ hown2 (by simp), by simp, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hm2 g hg
        · rw [List.mem_singleton] at hg; subst hg; simp
      intro c' hc'
      cases hc'
      refine ⟨by simp, fun x => ?_, ?_⟩
      · rw [V_new]
        have hold : V n ((orChain n st1 w1.val ws).1 ++
            [(⟨GateOp.and, [v.val, (orChain n st1 w1.val ws).2]⟩ : Gate)]) x c = V n st1 x c := by
          rw [e1, List.append_assoc]; exact V_old _ _ _ _ hc1
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
          Bool.or_false, id, Bool.or_eq_true, hold, hc2 x, hsem2 x]
        constructor
        · rintro (⟨v', hv', r⟩ | h)
          · exact ⟨v', by simp [hv'], r⟩
          · exact ⟨v, by simp, h⟩
        · rintro ⟨v', hv', r⟩
          rcases List.mem_append.1 hv' with hv' | hv'
          · exact Or.inl ⟨v', hv', r⟩
          · rw [List.mem_singleton] at hv'; subst hv'; exact Or.inr r
      · simp [e1, e2, hNv]; omega

theorem Inv_fold (hAG : ∀ v w, A v w → G.Adj v w) (hAA : ∀ v w, A v w → A w v → False)
    (hN : ∀ v w, w ∈ N v ↔ A v w) (L : List (Fin n)) : ∀ (P : List (Fin n))
    (st : List Gate × Option ℕ), (P ++ L).Nodup → Inv G A N P st →
    Inv G A N (P ++ L) (L.foldl (fun st v => blockStep n st v (N v)) st) := by
  induction L with
  | nil => intro P st _ h; simpa using h
  | cons v L ih =>
    intro P st hnd h
    have hv : v ∉ P := by
      intro hvP
      exact (List.nodup_append.1 hnd).2.2 v hvP v (by simp) rfl
    have := ih (P ++ [v]) _ (by simpa using hnd) (Inv_step G A N hAG hAA hN P st h v hv)
    simpa using this

end

theorem cover_iff {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hT : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T) (x : Fin n → Bool) :
    (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ↔
      ∃ v ∈ T, x v = true ∧ ∃ w, (v ∈ T ∧ G.Adj v w ∧ (w ∈ T → v < w)) ∧ x w = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hne : u ≠ v := huv.ne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rcases hT u v huv with huT | hvT
      · exact ⟨u, huT, hu, v, ⟨huT, huv, fun _ => hlt⟩, hv⟩
      · by_cases huT : u ∈ T
        · exact ⟨u, huT, hu, v, ⟨huT, huv, fun _ => hlt⟩, hv⟩
        · exact ⟨v, hvT, hv, u, ⟨hvT, huv.symm, fun h => absurd h huT⟩, hu⟩
    · rcases hT u v huv with huT | hvT
      · by_cases hvT : v ∈ T
        · exact ⟨v, hvT, hv, u, ⟨hvT, huv.symm, fun _ => hlt⟩, hu⟩
        · exact ⟨u, huT, hu, v, ⟨huT, huv, fun h => absurd h hvT⟩, hv⟩
      · exact ⟨v, hvT, hv, u, ⟨hvT, huv.symm, fun _ => hlt⟩, hu⟩
  · rintro ⟨v, -, hv, w, ⟨-, hvw, -⟩, hw⟩
    exact ⟨v, w, hvw, hv, hw⟩

theorem count_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (A : Fin n → Fin n → Prop) [DecidableRel A] (hAG : ∀ v w, A v w → G.Adj v w)
    (hAA : ∀ v w, A v w → A w v → False) :
    ∑ v ∈ T, (Finset.univ.filter (A v)).card ≤ G.edgeSet.ncard := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset, ← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simpa using hAG _ _ hp.2
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq he
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    simp only [Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (hAA _ _ hp.2 hq.2).elim

end PEqualNP.Outside.L_meta_5355

open PEqualNP.Outside.L_meta_5355 in
theorem PEqualNP.Outside.L_meta_5355 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x6.size ≤ x2.edgeSet.ncard + x4.card - (1 : ℕ) ∧ ∀ x7 < x6.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G _ T hT
  classical
  let A : Fin n → Fin n → Prop := fun v w => v ∈ T ∧ G.Adj v w ∧ (w ∈ T → v < w)
  have hAG : ∀ v w, A v w → G.Adj v w := fun v w h => h.2.1
  have hAA : ∀ v w, A v w → A w v → False := fun v w h1 h2 =>
    absurd (h1.2.2 h2.1) (not_lt.2 (h2.2.2 h1.1).le)
  let N : Fin n → List (Fin n) := fun v => (Finset.univ.filter (A v)).toList
  have hN : ∀ v w, w ∈ N v ↔ A v w := fun v w => by simp [N]
  have h0 : Inv G A N [] ([], none) := by
    refine ⟨by simp, fun j hj => by simp at hj, fun _ => ⟨rfl, by simp⟩, fun c hc => by cases hc⟩
  obtain ⟨hm, ho, hnone, hsome⟩ := Inv_fold G A N hAG hAA hN T.toList [] ([], none)
    (by simpa using T.nodup_toList) h0
  simp only [List.nil_append] at hm ho hnone hsome
  set st := T.toList.foldl (fun st v => blockStep n st v (N v)) ([], none) with hst
  have hS : (T.toList.map fun v => (N v).length).sum ≤ G.edgeSet.ncard := by
    rw [Finset.sum_map_toList]
    simpa [N] using count_le G T A hAG hAA
  refine ⟨⟨st.1, st.2.getD n⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, (hm g hg).2⟩
    rcases (hm g hg).1 with h | h <;> simp [h]
  · funext x
    show V n st.1 x (st.2.getD n) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
    rw [Bool.eq_iff_iff]
    have hg : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
    rw [hg, cover_iff G T hT x]
    cases h2 : st.2 with
    | none =>
      obtain ⟨h1, hP⟩ := hnone h2
      simp only [Option.getD_none, h1, V_nil_out]
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro v hv _ w hw _
      exact hP v (by simpa using hv) w hw
    | some c =>
      obtain ⟨-, hc2, -⟩ := hsome c h2
      simp only [Option.getD_some, hc2 x, Finset.mem_toList]
      exact Iff.rfl
  · show st.1.length ≤ _
    cases h2 : st.2 with
    | none => rw [(hnone h2).1]; simp
    | some c =>
      obtain ⟨-, -, hc3⟩ := hsome c h2
      rw [Finset.length_toList] at hc3
      omega
  · intro j hj hand
    obtain ⟨v, -, -, u, w, hadj, htrue, hfalse⟩ := ho j hj hand
    exact ⟨u, w, hadj, hj, hand, htrue, fun i hi _ hia => hfalse i hi hia⟩
