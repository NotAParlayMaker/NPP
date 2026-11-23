import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1406

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val (gates : List Gate) (x : List Bool) (j : ℕ) : Bool := (gates.foldl stepW x).getD j false

def Below (a b : List Bool) : Prop := a.length = b.length ∧ ∀ c, a.getD c false = true → b.getD c false = true

lemma wires_val (gates : List Gate) (o : ℕ) (x : List Bool) (j : ℕ) :
    (Circuit.wires ⟨gates, o⟩ x).getD j false = val gates x j := rfl

lemma eval_val (gates : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gates, o⟩ x = val gates x o := rfl

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma getD_beyond (w : List Bool) (c : ℕ) (hc : w.length ≤ c) : w.getD c false = false := by
  rw [List.getD_eq_default _ _ hc]

lemma prefix_getD (gs : List Gate) (w : List Bool) (c : ℕ) (hc : c < w.length) :
    (gs.foldl stepW w).getD c false = w.getD c false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    simp only [stepW]
    rw [List.getD_append _ _ _ _ hc]

lemma val_input (gates : List Gate) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    val gates x j = x.getD j false := prefix_getD gates x j hj

lemma val_ge (gates : List Gate) (x : List Bool) (j : ℕ) (hj : x.length + gates.length ≤ j) :
    val gates x j = false := by
  unfold val
  apply getD_beyond
  rw [fold_length]
  exact hj

lemma fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < gs.length) :
    (gs.foldl stepW w).getD (w.length + i) false =
      gs[i].op.eval (gs[i].inputs.map fun c =>
        if c < w.length + i then (gs.foldl stepW w).getD c false else false) := by
  induction gs generalizing w i with
  | nil => simp at hi
  | cons g gs ih =>
    rcases i with _ | i
    · simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [prefix_getD gs (stepW w g) w.length (by simp [stepW])]
      simp only [stepW]
      rw [List.getD_append_right _ _ _ _ (le_refl _)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro c _
      by_cases hc : c < w.length
      · rw [if_pos hc, prefix_getD gs _ c (by simp; omega)]
        rw [List.getD_append _ _ _ _ hc]
      · rw [if_neg hc]
        exact getD_beyond w c (by omega)
    · simp only [List.foldl_cons, List.getElem_cons_succ]
      have hl : (stepW w g).length = w.length + 1 := by simp [stepW]
      have := ih (stepW w g) i (by simp at hi; omega)
      rw [hl] at this
      have e : w.length + (i + 1) = w.length + 1 + i := by omega
      rw [e, this]

lemma val_gate (gates : List Gate) (x : List Bool) (i : ℕ) (hi : i < gates.length) :
    val gates x (x.length + i) = gates[i].op.eval (gates[i].inputs.map fun c =>
      if c < x.length + i then val gates x c else false) := fold_get gates x i hi

lemma eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f1 f2 : ℕ → Bool)
    (h : ∀ c, f1 c = true → f2 c = true) :
    g.op.eval (g.inputs.map f1) = true → g.op.eval (g.inputs.map f2) = true := by
  rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
  · simp only [List.all_eq_true, List.mem_map, id]
    intro H b ⟨c, hc, hb⟩
    rw [← hb]
    exact h c (H (f1 c) ⟨c, hc, rfl⟩)
  · simp only [List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨c, hc, rfl⟩, hb⟩
    exact ⟨f2 c, ⟨c, hc, rfl⟩, h c hb⟩

lemma below_step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : Below a b) : Below (stepW a g) (stepW b g) := by
  refine ⟨by simp [stepW, h.1], ?_⟩
  intro c hc
  simp only [stepW] at hc ⊢
  by_cases hlt : c < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hc
    rw [List.getD_append _ _ _ _ (h.1 ▸ hlt)]
    exact h.2 c hc
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hc
    rw [List.getD_append_right _ _ _ _ (by rw [← h.1]; omega)]
    rw [← h.1]
    rcases Nat.lt_or_ge (c - a.length) 1 with h1 | h1
    · have e : c - a.length = 0 := by omega
      rw [e] at hc ⊢
      simp only [List.getD_cons_zero] at hc ⊢
      exact eval_mono g hg _ _ h.2 hc
    · rw [getD_beyond _ _ (by simp; omega)] at hc
      exact absurd hc (by simp)

lemma below_fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : Below a b) : Below (gs.foldl stepW a) (gs.foldl stepW b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ _
      (below_step g (hg g (List.mem_cons_self ..)) a b h)

lemma val_mono (gates : List Gate) (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : Below x y) (j : ℕ) : val gates x j = true → val gates y j = true :=
  (below_fold gates hg x y h).2 j


def ind {n : ℕ} (S : Finset (Fin n)) : List Bool := List.ofFn fun v => decide (v ∈ S)

def seen (gates : List Gate) (n : ℕ) (S : Finset (Fin n)) (i c : ℕ) : Bool :=
  if c < n + i then val gates (ind S) c else false

def Lset (gates : List Gate) (n i c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => seen gates n {a} i c = true

def pick (gates : List Gate) (n i : ℕ) (g : Gate) : Finset (Fin n) :=
  match g.op, g.inputs with
  | GateOp.and, [c1, c2] =>
    if (Lset gates n i c1).card ≤ 1 then Lset gates n i c1 else Lset gates n i c2
  | _, _ => ∅

lemma ind_length {n : ℕ} (S : Finset (Fin n)) : (ind S).length = n := List.length_ofFn

lemma ind_getD {n : ℕ} (S : Finset (Fin n)) (c : ℕ) (h : c < n) :
    (ind S).getD c false = decide (⟨c, h⟩ ∈ S) := by
  simp [ind, List.getD_eq_getElem?_getD, h]

lemma ind_below {n : ℕ} {S S' : Finset (Fin n)} (h : S ⊆ S') : Below (ind S) (ind S') := by
  refine ⟨by simp [ind_length], fun c hc => ?_⟩
  by_cases hcn : c < n
  · rw [ind_getD _ _ hcn] at hc ⊢
    simp only [decide_eq_true_eq] at hc ⊢
    exact h hc
  · rw [List.getD_eq_default _ _ (by rw [ind_length]; omega)] at hc
    exact absurd hc (by simp)

lemma mem_Lset {gates : List Gate} {n i c : ℕ} {a : Fin n} :
    a ∈ Lset gates n i c ↔ seen gates n {a} i c = true := by
  simp [Lset]

lemma any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.map (fun c => f c || g c)).any id = ((l.map f).any id || (l.map g).any id) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id, ih]
    cases f a <;> cases g a <;> simp


lemma gate_eq {n : ℕ} {gates : List Gate} (k : Fin gates.length) (S : Finset (Fin n)) :
    val gates (ind S) (n + k) = (gates.get k).op.eval ((gates.get k).inputs.map (seen gates n S k)) := by
  have h := val_gate gates (ind S) k k.isLt
  rw [ind_length] at h
  rw [h]
  rfl

lemma no_edge_single {n : ℕ} {G : SimpleGraph (Fin n)} (a : Fin n) : ¬ ∃ u v : Fin n, G.Adj u v ∧ u ∈ ({a} : Finset (Fin n)) ∧ v ∈ ({a} : Finset (Fin n)) := by
  rintro ⟨u, v, h, hu, hv⟩
  simp only [Finset.mem_singleton] at hu hv
  subst hu hv
  exact G.irrefl h

end PEqualNP.Outside.L_meta_1406

open PEqualNP.Outside.L_meta_1406 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1406 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∀ I : Finset (Fin gates.length), (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → i ∈ I) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ I.card := by
  classical
  intro n G _ hC4 gates out hops hf hbelow I hI
  have hmon : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hops g hg).1
  have hout : ∀ S : Finset (Fin n), val gates (ind S) out =
      decide (∃ u v : Fin n, G.Adj u v ∧ u ∈ S ∧ v ∈ S) := by
    intro S
    rw [← eval_val gates out]
    show Circuit.eval ⟨gates, out⟩ (List.ofFn fun v => decide (v ∈ S)) = _
    simpa using hf (fun v => decide (v ∈ S))
  have hbel : ∀ (k : Fin gates.length) (S : Finset (Fin n)), (gates.get k).op = GateOp.and →
      val gates (ind S) (n + k) = true → ∃ u v : Fin n, G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
    intro k S h1 h2
    have := hbelow k (fun v => decide (v ∈ S)) h1 (by rw [wires_val]; exact h2)
    simpa using this
  have hsingle_off : ∀ (k : Fin gates.length) (a : Fin n), (gates.get k).op = GateOp.and →
      val gates (ind {a}) (n + k) = false := by
    intro k a h1
    by_contra h2
    exact no_edge_single a (hbel k {a} h1 (by simpa using h2))
  -- the two child sets of an AND gate span a complete bipartite subgraph
  have hbic : ∀ (k : Fin gates.length) (c1 c2 : ℕ) (a b : Fin n), (gates.get k).op = GateOp.and →
      (gates.get k).inputs = [c1, c2] → a ∈ Lset gates n k c1 → b ∈ Lset gates n k c2 → G.Adj a b := by
    intro k c1 c2 a b hop hin ha hb
    rw [mem_Lset] at ha hb
    unfold seen at ha hb
    split_ifs at ha hb with h1 h2
    have ha' := val_mono gates hmon _ _ (ind_below (show ({a} : Finset (Fin n)) ⊆ {a, b} by simp)) c1 ha
    have hb' := val_mono gates hmon _ _ (ind_below (show ({b} : Finset (Fin n)) ⊆ {a, b} by simp)) c2 hb
    have hg : val gates (ind {a, b}) (n + k) = true := by
      rw [gate_eq, hop, hin]
      simp [GateOp.eval, seen, h1, h2, ha', hb']
    obtain ⟨p, q, hpq, hp, hq⟩ := hbel k {a, b} hop hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd hpq G.irrefl
    · exact hpq
    · exact hpq.symm
    · exact absurd hpq G.irrefl
  -- no 4-cycle: one side of every such bipartite subgraph has at most one vertex
  have hstar : ∀ (k : Fin gates.length) (c1 c2 : ℕ), (gates.get k).op = GateOp.and →
      (gates.get k).inputs = [c1, c2] →
      (Lset gates n k c1).card ≤ 1 ∨ (Lset gates n k c2).card ≤ 1 := by
    intro k c1 c2 hop hin
    by_contra h
    simp only [not_or, not_le] at h
    obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.1 h.2
    exact hC4 a b a' b' haa hbb ⟨hbic k c1 c2 a b hop hin ha hb, (hbic k c1 c2 a' b hop hin ha' hb).symm,
      hbic k c1 c2 a' b' hop hin ha' hb', (hbic k c1 c2 a b' hop hin ha hb').symm⟩
  -- every edge is split across the two children of some AND gate
  have hkey : ∀ u v : Fin n, G.Adj u v → ∃ (k : Fin gates.length) (c1 c2 : ℕ),
      (gates.get k).op = GateOp.and ∧ (gates.get k).inputs = [c1, c2] ∧
      ((u ∈ Lset gates n k c1 ∧ v ∈ Lset gates n k c2) ∨
        (v ∈ Lset gates n k c1 ∧ u ∈ Lset gates n k c2)) := by
    intro u v huv
    by_contra H
    have hsplit : ∀ j, val gates (ind {u, v}) j = (val gates (ind {u}) j || val gates (ind {v}) j) := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
      by_cases hjn : j < n
      · rw [val_input _ _ _ (by rw [ind_length]; exact hjn), val_input _ _ _ (by rw [ind_length]; exact hjn),
          val_input _ _ _ (by rw [ind_length]; exact hjn), ind_getD _ _ hjn, ind_getD _ _ hjn, ind_getD _ _ hjn]
        simp [Finset.mem_insert, Bool.decide_or]
      by_cases hjN : n + gates.length ≤ j
      · rw [val_ge _ _ _ (by rw [ind_length]; exact hjN), val_ge _ _ _ (by rw [ind_length]; exact hjN),
          val_ge _ _ _ (by rw [ind_length]; exact hjN)]
        rfl
      obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
      have hi : i < gates.length := by omega
      let k : Fin gates.length := ⟨i, hi⟩
      have hs : seen gates n {u, v} i = fun c => (seen gates n {u} i c || seen gates n {v} i c) := by
        funext c
        unfold seen
        split_ifs with hc
        · exact ih c hc
        · rfl
      have hk := gate_eq k {u, v}
      have hku := gate_eq k {u}
      have hkv := gate_eq k {v}
      change val gates (ind {u, v}) (n + k) = (val gates (ind {u}) (n + k) || val gates (ind {v}) (n + k))
      rcases hmon _ (List.get_mem gates k) with hop | hop
      · rw [hsingle_off k u hop, hsingle_off k v hop]
        have hu0 := hsingle_off k u hop
        have hv0 := hsingle_off k v hop
        rw [hku] at hu0
        rw [hkv] at hv0
        rw [hk, hs]
        have hlen := (hops _ (List.get_mem gates k)).2
        generalize hl : (gates.get k).inputs = l at hu0 hv0 hlen ⊢
        rw [hop] at hu0 hv0 ⊢
        match l, hlen with
        | [], _ => simp [GateOp.eval] at hu0
        | [c], _ =>
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true] at hu0 hv0 ⊢
          change seen gates n {u} i c = false at hu0
          change seen gates n {v} i c = false at hv0
          rw [hu0, hv0]
        | [c1, c2], _ =>
          have hc := fun h => H ⟨k, c1, c2, hop, hl, h⟩
          simp only [mem_Lset] at hc
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true] at hu0 hv0 ⊢
          revert hc hu0 hv0
          cases seen gates n {u} i c1 <;> cases seen gates n {v} i c1 <;>
            cases seen gates n {u} i c2 <;> cases seen gates n {v} i c2 <;> simp
        | _ :: _ :: _ :: _, h => simp at h
      · rw [hk, hku, hkv, hs, hop]
        exact any_or _ _ _
    have h1 := hout {u, v}
    have h2 := hout {u}
    have h3 := hout {v}
    rw [hsplit out] at h1
    have e1 : (∃ a b : Fin n, G.Adj a b ∧ a ∈ ({u, v} : Finset (Fin n)) ∧ b ∈ ({u, v} : Finset (Fin n))) :=
      ⟨u, v, huv, by simp, by simp⟩
    have e2 := no_edge_single (G := G) u
    have e3 := no_edge_single (G := G) v
    simp only [e1, e2, e3, decide_true, decide_false] at h1 h2 h3
    rw [h2, h3] at h1
    exact absurd h1 (by decide)
  -- the cover: one vertex for every AND gate
  refine ⟨I.biUnion fun k => pick gates n k (gates.get k), ?_, ?_⟩
  · intro u v huv
    obtain ⟨k, c1, c2, hop, hin, hc⟩ := hkey u v huv
    have hkI := hI k hop
    simp only [Finset.mem_biUnion]
    have hp : pick gates n k (gates.get k) =
        if (Lset gates n k c1).card ≤ 1 then Lset gates n k c1 else Lset gates n k c2 := by
      unfold pick; rw [hop, hin]
    rcases hc with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · by_cases hcard : (Lset gates n k c1).card ≤ 1
      · exact Or.inl ⟨k, hkI, by rw [hp, if_pos hcard]; exact hu⟩
      · exact Or.inr ⟨k, hkI, by rw [hp, if_neg hcard]; exact hv⟩
    · by_cases hcard : (Lset gates n k c1).card ≤ 1
      · exact Or.inr ⟨k, hkI, by rw [hp, if_pos hcard]; exact hv⟩
      · exact Or.inl ⟨k, hkI, by rw [hp, if_neg hcard]; exact hu⟩
  · have hpick : ∀ k : Fin gates.length, (pick gates n k (gates.get k)).card ≤ 1 := by
      intro k
      unfold pick
      split
      · rename_i c1 c2 hop hin
        split_ifs with hcard
        · exact hcard
        · rcases hstar k c1 c2 hop hin with h | h
          · exact absurd h hcard
          · exact h
      · simp
    calc (I.biUnion fun k => pick gates n k (gates.get k)).card
        ≤ ∑ k ∈ I, (pick gates n k (gates.get k)).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ I, 1 := Finset.sum_le_sum fun k _ => hpick k
      _ = I.card := by simp
