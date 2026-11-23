import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1406_aux

open PEqualNP.CircuitLowerBounds

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepWire w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : k < (stepWire w g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire w g) hlt]
    simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

def wval {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) : Bool :=
  (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD k false

private lemma wires_eq_foldl {n : ℕ} (gates : List Gate) (x : Fin n → Bool) :
    Circuit.wires ⟨gates, 0⟩ (List.ofFn x) = gates.foldl stepWire (List.ofFn x) := rfl

private lemma wval_length {n : ℕ} (gates : List Gate) (x : Fin n → Bool) :
    (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).length = n + gates.length := by
  rw [wires_eq_foldl, foldl_step_length, List.length_ofFn]

private lemma wval_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    wval gates x k = x ⟨k, hk⟩ := by
  unfold wval
  rw [wires_eq_foldl, foldl_step_getD_lt gates (List.ofFn x) k (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

private lemma wval_ge {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ)
    (hk : n + gates.length ≤ k) :
    wval gates x k = false := by
  unfold wval
  have hlen : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).length ≤ k := by
    rw [wval_length]
    exact hk
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

lemma wval_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (i : Fin gates.length) :
    wval gates x (n + i.1) =
      (gates.get i).op.eval
        ((gates.get i).inputs.map fun r => if r < n + i.1 then wval gates x r else false) := by
  unfold wval
  rw [wires_eq_foldl]
  have hsplit : gates = gates.take i.1 ++ gates.get i :: gates.drop (i.1 + 1) := by
    have hdrop : gates.drop i.1 = gates.get i :: gates.drop (i.1 + 1) := by
      rw [List.get_eq_getElem]
      exact List.drop_eq_getElem_cons i.2
    rw [← hdrop, List.take_append_drop]
  have hfold : gates.foldl stepWire (List.ofFn x) =
      (gates.take i.1 ++ gates.get i :: gates.drop (i.1 + 1)).foldl stepWire (List.ofFn x) :=
    congrArg (fun l => l.foldl stepWire (List.ofFn x)) hsplit
  conv_lhs => rw [hfold, List.foldl_append, List.foldl_cons]
  set pre := (gates.take i.1).foldl stepWire (List.ofFn x)
  have hpre_len : pre.length = n + i.1 := by
    simp only [pre, foldl_step_length, List.length_ofFn, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt i.2)]
  have hlt_step : n + i.1 < (stepWire pre (gates.get i)).length := by
    simp only [stepWire, List.length_append, List.length_singleton, hpre_len]
    omega
  rw [foldl_step_getD_lt _ _ _ hlt_step]
  have hget : (stepWire pre (gates.get i)).getD (n + i.1) false =
      (gates.get i).op.eval ((gates.get i).inputs.map fun r => pre.getD r false) := by
    simp only [stepWire, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hsub : n + i.1 - pre.length = 0 := by omega
    rw [hsub]
    simp
  rw [hget]
  congr 1
  refine List.map_congr_left fun r _ => ?_
  by_cases hr : r < n + i.1
  · simp only [hr, ite_true]
    conv_rhs => rw [hfold, List.foldl_append]
    rw [foldl_step_getD_lt _ pre r (by omega)]
  · simp only [hr, ite_false]
    have hge : pre.length ≤ r := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]

private lemma wval_mono {n : ℕ} (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ k : ℕ, wval gates x k = true → wval gates y k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hx
    by_cases hkn : k < n
    · rw [wval_input gates x k hkn] at hx
      rw [wval_input gates y k hkn]
      exact hxy ⟨k, hkn⟩ hx
    · by_cases hklen : k < n + gates.length
      · let i : Fin gates.length := ⟨k - n, by omega⟩
        have hki : n + i.1 = k := by simp [i]; omega
        rw [← hki] at hx ⊢
        rw [wval_gate] at hx ⊢
        have hmem : gates.get i ∈ gates := List.get_mem gates i
        rcases hmono (gates.get i) hmem with hand | hor
        · rw [hand] at hx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hx ⊢
          intro r hr
          have hxr := hx r hr
          split_ifs at hxr ⊢ with hri
          exact ih r (by omega) hxr
        · rw [hor] at hx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
          rcases hx with ⟨_, ⟨r, hr, hxr⟩, rfl⟩
          refine ⟨true, ⟨r, hr, ?_⟩, rfl⟩
          split_ifs at hxr ⊢ with hri
          exact ih r (by omega) hxr
      · rw [wval_ge gates x k (by omega)] at hx
        exact False.elim (Bool.false_ne_true hx)

def oneHot {n : ℕ} (v : Fin n) : Fin n → Bool :=
  fun z => decide (z = v)

def twoHot {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun z => decide (z = u ∨ z = v)

lemma first_and_fires {n : ℕ} (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : Fin n) :
    ∀ k : ℕ,
      (∀ j : Fin gates.length, n + j.1 ≤ k → (gates.get j).op = GateOp.and →
        wval gates (twoHot u v) (n + j.1) = false) →
      wval gates (twoHot u v) k = true →
      wval gates (oneHot u) k = true ∨ wval gates (oneHot v) k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hno hx
    by_cases hkn : k < n
    · rw [wval_input gates (twoHot u v) k hkn] at hx
      simp only [twoHot, decide_eq_true_eq] at hx
      rw [wval_input gates (oneHot u) k hkn, wval_input gates (oneHot v) k hkn]
      rcases hx with hu | hv
      · left; simp [oneHot, hu]
      · right; simp [oneHot, hv]
    · by_cases hklen : k < n + gates.length
      · let i : Fin gates.length := ⟨k - n, by omega⟩
        have hki : n + i.1 = k := by simp [i]; omega
        have hmem : gates.get i ∈ gates := List.get_mem gates i
        rcases hmono (gates.get i) hmem with hand | hor
        · have hf := hno i (by omega) hand
          rw [hki] at hf
          rw [hf] at hx
          exact False.elim (Bool.false_ne_true hx)
        · rw [← hki] at hx ⊢
          rw [wval_gate] at hx
          rw [hor] at hx
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx
          rcases hx with ⟨_, ⟨r, hr, hxr⟩, rfl⟩
          split_ifs at hxr with hri
          have hrec := ih r (by omega) (fun j hj hand => hno j (by omega) hand) hxr
          rcases hrec with hu | hv
          · left
            rw [wval_gate, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨r, hr, by simp [hri, hu]⟩, rfl⟩
          · right
            rw [wval_gate, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨true, ⟨r, hr, by simp [hri, hv]⟩, rfl⟩
      · rw [wval_ge gates (twoHot u v) k (by omega)] at hx
        exact False.elim (Bool.false_ne_true hx)

def supp (n : ℕ) (gates : List Gate) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => wval gates (oneHot v) k = true

lemma mem_supp (n : ℕ) (gates : List Gate) (k : ℕ) (v : Fin n) :
    v ∈ supp n gates k ↔ wval gates (oneHot v) k = true := by
  simp [supp]

lemma adj_of_clean_twoHot {n : ℕ} (G : SimpleGraph (Fin n))
    (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hclean : ∀ (i : Fin gates.length) (x : Fin n → Bool),
      (gates.get i).op = GateOp.and →
      wval gates x (n + i.1) = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)
    (i : Fin gates.length) (hand : (gates.get i).op = GateOp.and)
    (a b : ℕ) (hinp : (gates.get i).inputs = [a, b])
    (ha : a < n + i.1) (hb : b < n + i.1)
    (p q : Fin n) (hp : p ∈ supp n gates a) (hq : q ∈ supp n gates b) :
    G.Adj p q := by
  have hpa : wval gates (twoHot p q) a = true := by
    refine wval_mono gates hmono (oneHot p) (twoHot p q) ?_ a ((mem_supp n gates a p).mp hp)
    intro z hz
    simp only [oneHot, decide_eq_true_eq] at hz
    simp [twoHot, hz]
  have hqb : wval gates (twoHot p q) b = true := by
    refine wval_mono gates hmono (oneHot q) (twoHot p q) ?_ b ((mem_supp n gates b q).mp hq)
    intro z hz
    simp only [oneHot, decide_eq_true_eq] at hz
    simp [twoHot, hz]
  have hfire : wval gates (twoHot p q) (n + i.1) = true := by
    rw [wval_gate, hand, hinp]
    simp [GateOp.eval, ha, hb, hpa, hqb]
  obtain ⟨x, y, hxy, hx, hy⟩ := hclean i (twoHot p q) hand hfire
  simp only [twoHot, decide_eq_true_eq] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact False.elim (G.irrefl hxy)
  · exact hxy
  · exact G.adj_symm hxy
  · exact False.elim (G.irrefl hxy)

lemma card_le_one_or {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hbic : ∀ p ∈ A, ∀ q ∈ B, G.Adj p q) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨q1, hq1, q2, hq2, hqne⟩ := Finset.one_lt_card.mp h.2
  exact hC4 p1 q1 p2 q2 hpne hqne
    ⟨hbic p1 hp1 q1 hq1, G.adj_symm (hbic p2 hp2 q1 hq1),
     hbic p2 hp2 q2 hq2, G.adj_symm (hbic p1 hp1 q2 hq2)⟩

noncomputable def pickVertex (n : ℕ) (gates : List Gate) (i : Fin gates.length) :
    Option (Fin n) := by
  classical
  exact
    match (gates.get i).inputs with
    | [a, b] =>
      if h1 : (supp n gates a).card = 1 then
        some (Finset.card_eq_one.mp h1).choose
      else if h2 : (supp n gates b).card = 1 then
        some (Finset.card_eq_one.mp h2).choose
      else
        none
    | _ => none

lemma pickVertex_card_le (n : ℕ) (gates : List Gate) (i : Fin gates.length) :
    (pickVertex n gates i).toFinset.card ≤ 1 := by
  cases h : pickVertex n gates i <;> simp

lemma pickVertex_covers (n : ℕ) (gates : List Gate) (i : Fin gates.length)
    (a b : ℕ) (hinp : (gates.get i).inputs = [a, b])
    (u v : Fin n) (hu : u ∈ supp n gates a ∨ v ∈ supp n gates a)
    (hv : u ∈ supp n gates b ∨ v ∈ supp n gates b)
    (hcard : (supp n gates a).card ≤ 1 ∨ (supp n gates b).card ≤ 1) :
    u ∈ (pickVertex n gates i).toFinset ∨ v ∈ (pickVertex n gates i).toFinset := by
  have ha_pos : 0 < (supp n gates a).card := Finset.card_pos.mpr (by
    rcases hu with h | h
    · exact ⟨u, h⟩
    · exact ⟨v, h⟩)
  have hb_pos : 0 < (supp n gates b).card := Finset.card_pos.mpr (by
    rcases hv with h | h
    · exact ⟨u, h⟩
    · exact ⟨v, h⟩)
  unfold pickVertex
  simp only [hinp]
  by_cases h1 : (supp n gates a).card = 1
  · simp only [h1, ↓reduceDIte, Option.toFinset_some, Finset.mem_singleton]
    have hspec := (Finset.card_eq_one.mp h1).choose_spec
    rw [hspec, Finset.mem_singleton, Finset.mem_singleton] at hu
    exact hu
  · have h2 : (supp n gates b).card = 1 := by omega
    simp only [h1, ↓reduceDIte, h2, Option.toFinset_some, Finset.mem_singleton]
    have hspec := (Finset.card_eq_one.mp h2).choose_spec
    rw [hspec, Finset.mem_singleton, Finset.mem_singleton] at hv
    exact hv

end PEqualNP.Outside.L_meta_1406_aux

theorem PEqualNP.Outside.L_meta_1406 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∀ I : Finset (Fin gates.length), (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → i ∈ I) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ I.card := by
  classical
  intro n G _ hC4 gates out hgates heval hclean I hI
  have hmono : ∀ g ∈ gates,
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun g hg => (hgates g hg).1
  have hclean' : ∀ (i : Fin gates.length) (x : Fin n → Bool),
      (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      PEqualNP.Outside.L_meta_1406_aux.wval gates x (n + i.1) = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true :=
    fun i x hand h => hclean i x hand h
  let T : Finset (Fin n) :=
    I.biUnion fun i => (PEqualNP.Outside.L_meta_1406_aux.pickVertex n gates i).toFinset
  refine ⟨T, ?_, ?_⟩
  · intro u v huv
    have hout_true : PEqualNP.Outside.L_meta_1406_aux.wval gates
        (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) out = true := by
      have h := heval (PEqualNP.Outside.L_meta_1406_aux.twoHot u v)
      change PEqualNP.Outside.L_meta_1406_aux.wval gates
        (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) out = _ at h
      rw [h, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [PEqualNP.Outside.L_meta_1406_aux.twoHot],
        by simp [PEqualNP.Outside.L_meta_1406_aux.twoHot]⟩
    have hone_false (z : Fin n) : PEqualNP.Outside.L_meta_1406_aux.wval gates
        (PEqualNP.Outside.L_meta_1406_aux.oneHot z) out = false := by
      have h := heval (PEqualNP.Outside.L_meta_1406_aux.oneHot z)
      change PEqualNP.Outside.L_meta_1406_aux.wval gates
        (PEqualNP.Outside.L_meta_1406_aux.oneHot z) out = _ at h
      rw [h, decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [PEqualNP.Outside.L_meta_1406_aux.oneHot, decide_eq_true_eq] at ha hb
      rw [ha, hb] at hab
      exact G.irrefl hab
    have hex_and : ∃ m : ℕ, ∃ hm : m < gates.length,
        (gates.get ⟨m, hm⟩).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.Outside.L_meta_1406_aux.wval gates
          (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) (n + m) = true := by
      by_contra hnone
      have hno : ∀ j : Fin gates.length, n + j.1 ≤ out →
          (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.Outside.L_meta_1406_aux.wval gates
            (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) (n + j.1) = false := by
        intro j _ hand
        cases hval : PEqualNP.Outside.L_meta_1406_aux.wval gates
            (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) (n + j.1) with
        | false => rfl
        | true => exact False.elim (hnone ⟨j.1, j.2, hand, hval⟩)
      rcases PEqualNP.Outside.L_meta_1406_aux.first_and_fires gates hmono u v out hno hout_true with hu | hv
      · rw [hone_false u] at hu; exact Bool.false_ne_true hu
      · rw [hone_false v] at hv; exact Bool.false_ne_true hv
    let m := Nat.find hex_and
    obtain ⟨hm, hand, hfire⟩ := Nat.find_spec hex_and
    let i : Fin gates.length := ⟨m, hm⟩
    change (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and at hand
    change PEqualNP.Outside.L_meta_1406_aux.wval gates
      (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) (n + i.1) = true at hfire
    have hleast : ∀ j : Fin gates.length, j.1 < i.1 →
        (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.Outside.L_meta_1406_aux.wval gates
          (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) (n + j.1) = false := by
      intro j hj handj
      cases hval : PEqualNP.Outside.L_meta_1406_aux.wval gates
          (PEqualNP.Outside.L_meta_1406_aux.twoHot u v) (n + j.1) with
      | false => rfl
      | true => exact False.elim (Nat.find_min hex_and hj ⟨j.2, handj, hval⟩)
    have hclean_one (z : Fin n) : PEqualNP.Outside.L_meta_1406_aux.wval gates
        (PEqualNP.Outside.L_meta_1406_aux.oneHot z) (n + i.1) = false := by
      cases hval : PEqualNP.Outside.L_meta_1406_aux.wval gates
          (PEqualNP.Outside.L_meta_1406_aux.oneHot z) (n + i.1) with
      | false => rfl
      | true =>
        obtain ⟨a, b, hab, ha, hb⟩ := hclean' i (PEqualNP.Outside.L_meta_1406_aux.oneHot z) hand hval
        simp only [PEqualNP.Outside.L_meta_1406_aux.oneHot, decide_eq_true_eq] at ha hb
        rw [ha, hb] at hab
        exact False.elim (G.irrefl hab)
    have hlen : (gates.get i).inputs.length ≤ 2 := (hgates (gates.get i) (List.get_mem gates i)).2
    cases hinp : (gates.get i).inputs with
    | nil =>
      have htrue : PEqualNP.Outside.L_meta_1406_aux.wval gates
          (PEqualNP.Outside.L_meta_1406_aux.oneHot u) (n + i.1) = true := by
        rw [PEqualNP.Outside.L_meta_1406_aux.wval_gate, hand, hinp]
        rfl
      rw [hclean_one u] at htrue
      exact False.elim (Bool.false_ne_true htrue)
    | cons a rest =>
      cases rest with
      | nil =>
        rw [PEqualNP.Outside.L_meta_1406_aux.wval_gate, hand, hinp] at hfire
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true] at hfire
        split_ifs at hfire with ha
        have hrec := PEqualNP.Outside.L_meta_1406_aux.first_and_fires gates hmono u v a
          (fun j hj handj => hleast j (by omega) handj) hfire
        rcases hrec with hu | hv
        · have htrue : PEqualNP.Outside.L_meta_1406_aux.wval gates
              (PEqualNP.Outside.L_meta_1406_aux.oneHot u) (n + i.1) = true := by
            rw [PEqualNP.Outside.L_meta_1406_aux.wval_gate, hand, hinp]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ha, hu]
          rw [hclean_one u] at htrue
          exact False.elim (Bool.false_ne_true htrue)
        · have htrue : PEqualNP.Outside.L_meta_1406_aux.wval gates
              (PEqualNP.Outside.L_meta_1406_aux.oneHot v) (n + i.1) = true := by
            rw [PEqualNP.Outside.L_meta_1406_aux.wval_gate, hand, hinp]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ha, hv]
          rw [hclean_one v] at htrue
          exact False.elim (Bool.false_ne_true htrue)
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          rw [PEqualNP.Outside.L_meta_1406_aux.wval_gate, hand, hinp] at hfire
          simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hfire
          rcases hfire with ⟨hfa, hfb⟩
          split_ifs at hfa with ha
          split_ifs at hfb with hb
          have hu : u ∈ PEqualNP.Outside.L_meta_1406_aux.supp n gates a ∨
              v ∈ PEqualNP.Outside.L_meta_1406_aux.supp n gates a := by
            have hrec := PEqualNP.Outside.L_meta_1406_aux.first_and_fires gates hmono u v a
              (fun j hj handj => hleast j (by omega) handj) hfa
            simpa [PEqualNP.Outside.L_meta_1406_aux.mem_supp] using hrec
          have hv : u ∈ PEqualNP.Outside.L_meta_1406_aux.supp n gates b ∨
              v ∈ PEqualNP.Outside.L_meta_1406_aux.supp n gates b := by
            have hrec := PEqualNP.Outside.L_meta_1406_aux.first_and_fires gates hmono u v b
              (fun j hj handj => hleast j (by omega) handj) hfb
            simpa [PEqualNP.Outside.L_meta_1406_aux.mem_supp] using hrec
          have hcard := PEqualNP.Outside.L_meta_1406_aux.card_le_one_or G hC4
            (PEqualNP.Outside.L_meta_1406_aux.supp n gates a)
            (PEqualNP.Outside.L_meta_1406_aux.supp n gates b)
            (fun p hp q hq => PEqualNP.Outside.L_meta_1406_aux.adj_of_clean_twoHot G gates
              hmono hclean' i hand a b hinp ha hb p q hp hq)
          have hcov := PEqualNP.Outside.L_meta_1406_aux.pickVertex_covers n gates i a b hinp
            u v hu hv hcard
          have hiI : i ∈ I := hI i hand
          rcases hcov with hcu | hcv
          · left; exact Finset.mem_biUnion.mpr ⟨i, hiI, hcu⟩
          · right; exact Finset.mem_biUnion.mpr ⟨i, hiI, hcv⟩
        | cons _ _ =>
          rw [hinp] at hlen
          simp at hlen
  · calc
      T.card ≤ ∑ i ∈ I, (PEqualNP.Outside.L_meta_1406_aux.pickVertex n gates i).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I, 1 := Finset.sum_le_sum fun i _ =>
        PEqualNP.Outside.L_meta_1406_aux.pickVertex_card_le n gates i
      _ = I.card := by simp
