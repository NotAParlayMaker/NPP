import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wf]
  | cons g gs ih =>
    rw [wf_cons, ih]
    simp
    omega

lemma getD_snoc_lt (l : List Bool) (x : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma wf_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wf_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ hi

lemma wf_getD_gate (gs : List Gate) (w : List Bool) (i : ℕ) (g : Gate)
    (hi : w.length ≤ i) (hg : gs[i - w.length]? = some g) :
    (wf gs w).getD i false = g.op.eval (g.inputs.map fun c =>
      if c < i then (wf gs w).getD c false else false) := by
  induction gs generalizing w with
  | nil => simp at hg
  | cons g' gs ih =>
    rw [wf_cons]
    rcases Nat.eq_or_lt_of_le hi with h | h
    · subst h
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      rw [wf_getD_lt _ _ _ (by simp)]
      have e1 : (w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)]).getD w.length false
          = g'.op.eval (g'.inputs.map fun i => w.getD i false) := by
        simp [List.getD]
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro c _
      split_ifs with hc
      · rw [wf_getD_lt _ _ _ (by simp; omega), getD_snoc_lt _ _ _ hc]
      · exact List.getD_eq_default _ _ (by omega)
    · have e2 : i - w.length = (i - (w.length + 1)) + 1 := by omega
      rw [e2, List.getElem?_cons_succ] at hg
      exact ih _ (by simp; omega) (by simpa using hg)

def V (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma V_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    V C n x w = x ⟨w, h⟩ := by
  unfold V
  rw [show C.wires (List.ofFn x) = wf C.gates (List.ofFn x) from rfl,
    wf_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD, h]

lemma V_ge (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (h : n + C.size ≤ w) :
    V C n x w = false := by
  unfold V
  apply List.getD_eq_default
  rw [show C.wires (List.ofFn x) = wf C.gates (List.ofFn x) from rfl, wf_length]
  simpa [Circuit.size] using h

lemma V_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (g : Gate) (h : n ≤ w)
    (hg : C.gates[w - n]? = some g) :
    V C n x w = g.op.eval (g.inputs.map fun c => if c < w then V C n x c else false) := by
  unfold V
  rw [show C.wires (List.ofFn x) = wf C.gates (List.ofFn x) from rfl]
  exact wf_getD_gate _ _ _ _ (by simpa using h) (by simpa using hg)

def opAt (C : Circuit) (n w : ℕ) : GateOp := ((C.gates[w - n]?).map Gate.op).getD GateOp.or

def insAt (C : Circuit) (n w : ℕ) : List ℕ := ((C.gates[w - n]?).map Gate.inputs).getD []

def gen (C : Circuit) (n : ℕ) (P b : ℕ → Bool) (w : ℕ) : Bool :=
  if P w then (opAt C n w).eval ((insAt C n w).map fun c =>
    if _h : c < w then gen C n P b c else false) else b w
termination_by w

lemma gen_eq (C : Circuit) (n : ℕ) (P b : ℕ → Bool) (w : ℕ) :
    gen C n P b w = if P w then (opAt C n w).eval ((insAt C n w).map fun c =>
      if c < w then gen C n P b c else false) else b w := by
  rw [gen]
  simp only [dite_eq_ite]

def Rel (C : Circuit) (n : ℕ) (P : ℕ → Bool) (g c : ℕ) : Prop :=
  P g = true ∧ c ∈ insAt C n g ∧ c < g

def Reach (C : Circuit) (n : ℕ) (P : ℕ → Bool) (w c : ℕ) : Prop :=
  Relation.ReflTransGen (Rel C n P) w c

lemma reach_le {C : Circuit} {n : ℕ} {P : ℕ → Bool} {w c : ℕ} (h : Reach C n P w c) :
    c ≤ w := by
  induction h with
  | refl => exact le_refl _
  | tail _ hr ih => exact le_trans (le_of_lt hr.2.2) ih

lemma opAt_ao (C : Circuit) (n w : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    opAt C n w = GateOp.and ∨ opAt C n w = GateOp.or := by
  unfold opAt
  cases h : C.gates[w - n]? with
  | none => right; rfl
  | some g => exact (hg g (List.mem_of_getElem? h)).1

lemma insAt_len (C : Circuit) (n w : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (insAt C n w).length ≤ 2 := by
  unfold insAt
  cases h : C.gates[w - n]? with
  | none => simp
  | some g => simp [(hg g (List.mem_of_getElem? h)).2]

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (L : List ℕ)
    (f1 f2 : ℕ → Bool) (h : ∀ c ∈ L, f1 c = true → f2 c = true)
    (h1 : op.eval (L.map f1) = true) : op.eval (L.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h1 ⊢
    rintro _ ⟨c, hc, rfl⟩
    exact h c hc (h1 _ ⟨c, hc, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h1 ⊢
    obtain ⟨_, ⟨c, hc, rfl⟩, h1⟩ := h1
    exact ⟨_, ⟨c, hc, rfl⟩, h c hc h1⟩

lemma gen_mono (C : Circuit) (n : ℕ) (P b1 b2 : ℕ → Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, (∀ c, Reach C n P w c → P c = false → b1 c = true → b2 c = true) →
      gen C n P b1 w = true → gen C n P b2 w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hb h1
    rw [gen_eq] at h1 ⊢
    cases hP : P w with
    | false =>
      simp only [hP, Bool.false_eq_true, ite_false] at h1 ⊢
      exact hb w Relation.ReflTransGen.refl hP h1
    | true =>
      simp only [hP, ite_true] at h1 ⊢
      apply eval_mono _ (opAt_ao C n w hg) _ _ _ _ h1
      intro c hc hc1
      split_ifs at hc1 ⊢ with hcw
      apply ih c hcw _ hc1
      intro d hd
      exact hb d (Relation.ReflTransGen.head ⟨hP, hc, hcw⟩ hd)

lemma gen_V (C : Circuit) (n : ℕ) (P : ℕ → Bool) (x : Fin n → Bool)
    (hP : ∀ w, P w = true → n ≤ w) : ∀ w, gen C n P (V C n x) w = V C n x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [gen_eq]
    cases hPw : P w with
    | false => simp
    | true =>
      simp only [ite_true]
      have hn := hP w hPw
      cases hgw : C.gates[w - n]? with
      | none =>
        have hge : n + C.size ≤ w := by
          rw [List.getElem?_eq_none_iff] at hgw
          simp only [Circuit.size]
          omega
        rw [V_ge C n x w hge]
        simp [opAt, insAt, hgw, GateOp.eval]
      | some g =>
        rw [V_gate C n x w g hn hgw]
        simp only [opAt, insAt, hgw, Option.map_some, Option.getD_some]
        congr 1
        apply List.map_congr_left
        intro c _
        split_ifs with hcw
        · exact ih c hcw
        · rfl

lemma V_mono (C : Circuit) (n : ℕ) (x y : Fin n → Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hxy : ∀ a, x a = true → y a = true) (w : ℕ) (h : V C n x w = true) :
    V C n y w = true := by
  have hP : ∀ w, (fun w => decide (n ≤ w)) w = true → n ≤ w := fun w h => by simpa using h
  rw [← gen_V C n _ y hP]
  rw [← gen_V C n _ x hP] at h
  refine gen_mono C n _ _ _ hg w ?_ h
  intro c _ hc h1
  have hcn : c < n := by simpa using hc
  rw [V_input C n x c hcn] at h1
  rw [V_input C n y c hcn]
  exact hxy _ h1

def T (C : Circuit) (n w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n => V C n (fun b : Fin n => decide (b = a)) w = true)

lemma mem_T (C : Circuit) (n w : ℕ) (a : Fin n) :
    a ∈ T C n w ↔ V C n (fun b : Fin n => decide (b = a)) w = true := by
  simp [T]

lemma T_input (C : Circuit) (n w : ℕ) (h : w < n) : (T C n w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [mem_T, V_input C n _ w h] at ha hb
  simp at ha hb
  rw [← ha, ← hb]

lemma T_ge (C : Circuit) (n w : ℕ) (h : n + C.size ≤ w) : T C n w = ∅ := by
  ext a
  simp [mem_T, V_ge C n _ w h]

def priv (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) : Bool :=
  decide (n ≤ w ∧ w < n + C.size ∧ T C n w ⊆ S ∧ 2 ≤ (T C n w).card)

def PS (C : Circuit) (n : ℕ) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter (fun w => priv C n S w = true)

lemma count (C : Circuit) (n : ℕ) (P : ℕ → Bool) (r : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    [DecidablePred (Reach C n P r)] :
    (((Finset.range (r + 1)).filter (Reach C n P r)).filter (fun w => P w = false)).card ≤
    (((Finset.range (r + 1)).filter (Reach C n P r)).filter (fun w => P w = true)).card + 1 := by
  set R := (Finset.range (r + 1)).filter (Reach C n P r) with hR
  set Vs := R.filter (fun w => P w = true) with hVs
  set Es := R.filter (fun w => P w = false) with hEs
  have hsum : Vs.card + Es.card = R.card := by
    have := Finset.card_filter_add_card_filter_not (s := R) (fun w => P w = true)
    simpa [hVs, hEs] using this
  have hrR : r ∈ R := by
    simp only [hR, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self r, Relation.ReflTransGen.refl⟩
  have hsub : R.erase r ⊆ Vs.biUnion (fun g => (insAt C n g).toFinset) := by
    intro c hc
    rw [Finset.mem_erase] at hc
    obtain ⟨hcr, hcR⟩ := hc
    simp only [hR, Finset.mem_filter, Finset.mem_range] at hcR
    rcases Relation.ReflTransGen.cases_tail hcR.2 with h | ⟨g, hg1, hg2⟩
    · exact absurd h hcr
    · rw [Finset.mem_biUnion]
      refine ⟨g, ?_, ?_⟩
      · simp only [hVs, hR, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨Nat.lt_succ_of_le (reach_le hg1), hg1⟩, hg2.1⟩
      · simpa using hg2.2.1
  have hcard : (Vs.biUnion (fun g => (insAt C n g).toFinset)).card ≤ 2 * Vs.card := by
    calc _ ≤ ∑ g ∈ Vs, ((insAt C n g).toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ Vs, 2 := Finset.sum_le_sum
          (fun g _ => le_trans (List.toFinset_card_le _) (insAt_len C n g hg))
      _ = 2 * Vs.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hrR] at h1
  omega


lemma per_output (n k : ℕ) (C : Circuit) (S : Finset (Fin n)) (r c : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h2 : 2 ≤ (T C n r).card) (hS : T C n r ⊆ S)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → V C n x r = false)
    (hck : c ≤ k) (hcA : c + 1 ≤ (T C n r).card) :
    c ≤ (PS C n S).card := by
  classical
  set P := priv C n S with hPdef
  have hPiff : ∀ w, P w = true ↔
      (n ≤ w ∧ w < n + C.size ∧ T C n w ⊆ S ∧ 2 ≤ (T C n w).card) := by
    intro w
    simp only [hPdef, priv, decide_eq_true_eq]
  have hPn : ∀ w, P w = true → n ≤ w := fun w hw => ((hPiff w).mp hw).1
  have hr : P r = true := by
    have hn : n ≤ r := by
      by_contra hlt
      rw [not_le] at hlt
      have := T_input C n r hlt
      omega
    have hlt : r < n + C.size := by
      by_contra hge
      rw [not_lt] at hge
      rw [T_ge C n r hge] at h2
      simp at h2
    exact (hPiff r).mpr ⟨hn, hlt, hS, h2⟩
  have hcount := count C n P r hg
  set R := (Finset.range (r + 1)).filter (Reach C n P r) with hR
  set Vs := R.filter (fun w => P w = true) with hVs
  set Es := R.filter (fun w => P w = false) with hEs
  have hVsub : Vs ⊆ PS C n S := by
    intro w hw
    simp only [hVs, Finset.mem_filter] at hw
    have h3 := (hPiff w).mp hw.2
    simp only [PS, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨h3.1, h3.2.1⟩, hw.2⟩
  have hVcard := Finset.card_le_card hVsub
  have hEsmem : ∀ w, Reach C n P r w → P w = false → w ∈ Es := by
    intro w hw hPw
    simp only [hEs, hR, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.lt_succ_of_le (reach_le hw), hw⟩, hPw⟩
  set E : ℕ → Bool := fun w => decide (¬ T C n w ⊆ S) with hE
  cases hL : gen C n P E r with
  | true =>
    have : Nonempty (Fin n) := by
      obtain ⟨a, _⟩ := Finset.card_pos.mp (by omega : 0 < (T C n r).card)
      exact ⟨a⟩
    set Es1 := Es.filter (fun w => E w = true) with hEs1
    have hex : ∀ w ∈ Es1, ∃ a, a ∈ T C n w ∧ a ∉ S := by
      intro w hw
      simp only [hEs1, Finset.mem_filter, hE, decide_eq_true_eq] at hw
      obtain ⟨a, ha1, ha2⟩ := Finset.not_subset.mp hw.2
      exact ⟨a, ha1, ha2⟩
    choose! pick hpick using hex
    set X := Es1.image pick with hX
    set x : Fin n → Bool := fun a => decide (a ∈ X) with hx
    have hXcard : X.card ≤ Es.card :=
      le_trans Finset.card_image_le (Finset.card_le_card (Finset.filter_subset _ _))
    have hsupp : (Finset.univ.filter (fun q : Fin n => x q = true)) = X := by
      ext q
      simp [hx]
    have hdisj : ∀ q ∈ S, x q = false := by
      intro q hq
      simp only [hx, decide_eq_false_iff_not, hX, Finset.mem_image]
      rintro ⟨w, hw, rfl⟩
      exact (hpick w hw).2 hq
    have hVx : V C n x r = true := by
      rw [← gen_V C n P x hPn r]
      refine gen_mono C n P E (V C n x) hg r ?_ hL
      intro w hw hPw hEw
      have hw1 : w ∈ Es1 := by
        simp only [hEs1, Finset.mem_filter]
        exact ⟨hEsmem w hw hPw, hEw⟩
      have hp := hpick w hw1
      rw [mem_T] at hp
      apply V_mono C n _ x hg _ w hp.1
      intro a ha
      simp only [decide_eq_true_eq] at ha
      subst ha
      simp only [hx, decide_eq_true_eq, hX, Finset.mem_image]
      exact ⟨w, hw1, rfl⟩
    have hk : k < X.card := by
      by_contra hle
      rw [not_lt] at hle
      have := hprom x (by rw [hsupp]; exact hle) hdisj
      rw [hVx] at this
      exact Bool.noConfusion this
    omega
  | false =>
    have hex : ∀ a ∈ T C n r, ∃ w, w ∈ Es ∧ E w = false ∧
        V C n (fun b : Fin n => decide (b = a)) w = true := by
      intro a ha
      by_contra hcon
      rw [mem_T, ← gen_V C n P _ hPn r] at ha
      have hm := gen_mono C n P _ E hg r ?_ ha
      · rw [hL] at hm
        exact Bool.noConfusion hm
      · intro w hw hPw hVw
        by_contra hEw
        have hEw1 : E w = false := by simpa using hEw
        exact hcon ⟨w, hEsmem w hw hPw, hEw1, hVw⟩
    choose! f hf using hex
    have hinj : Set.InjOn f (T C n r) := by
      intro a ha b hb hab
      obtain ⟨hfa1, hfa2, hfa3⟩ := hf a ha
      obtain ⟨_, _, hfb3⟩ := hf b hb
      rw [← hab] at hfb3
      have hPw : P (f a) = false := (Finset.mem_filter.mp hfa1).2
      have hTS : T C n (f a) ⊆ S := by
        simpa [hE] using hfa2
      have hle : (T C n (f a)).card ≤ 1 := by
        by_contra hgt
        rw [not_le] at hgt
        have hn : n ≤ f a := by
          by_contra hlt
          rw [not_le] at hlt
          have := T_input C n (f a) hlt
          omega
        have hlt : f a < n + C.size := by
          by_contra hge
          rw [not_lt] at hge
          rw [T_ge C n (f a) hge] at hgt
          simp at hgt
        have hP1 := (hPiff (f a)).mpr ⟨hn, hlt, hTS, hgt⟩
        rw [hPw] at hP1
        exact Bool.noConfusion hP1
      exact Finset.card_le_one.mp hle a ((mem_T _ _ _ _).mpr hfa3) b ((mem_T _ _ _ _).mpr hfb3)
    have hcardA := Finset.card_le_card_of_injOn f (fun a ha => (hf a ha).1) hinj
    omega

lemma PS_disj (C : Circuit) (n : ℕ) (S1 S2 : Finset (Fin n)) (h : (S1 ∩ S2).card ≤ 1) :
    Disjoint (PS C n S1) (PS C n S2) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [PS, priv, Finset.mem_filter, decide_eq_true_eq] at h1 h2
  obtain ⟨_, _, _, h1S, h1c⟩ := h1
  obtain ⟨_, _, _, h2S, _⟩ := h2
  have := Finset.card_le_card (Finset.subset_inter h1S h2S)
  omega

lemma assemble (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (c : Fin m → ℕ) (hSS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (h2 : ∀ i, 2 ≤ (T C n (o i)).card)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hAS : ∀ (i : Fin m) (p : Fin n),
      V C n (fun q : Fin n => decide (q = p)) (o i) = true → p ∈ S i)
    (hprom : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → V C n x (o i) = false)
    (hck : ∀ i, c i ≤ k) (hcA : ∀ i, c i + 1 ≤ (T C n (o i)).card) :
    ∑ i : Fin m, c i ≤ C.size := by
  classical
  have key : ∀ i, c i ≤ (PS C n (S i)).card := fun i =>
    per_output n k C (S i) (o i) (c i) hg (h2 i)
      (fun p hp => hAS i p ((mem_T _ _ _ _).mp hp)) (hprom i) (hck i) (hcA i)
  calc ∑ i : Fin m, c i ≤ ∑ i : Fin m, (PS C n (S i)).card :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = (Finset.univ.biUnion (fun i => PS C n (S i))).card := by
        rw [Finset.card_biUnion]
        intro i _ j _ hij
        exact PS_disj C n (S i) (S j) (hSS i j hij)
    _ ≤ (Finset.Ico n (n + C.size)).card := by
        apply Finset.card_le_card
        intro w hw
        simp only [Finset.mem_biUnion] at hw
        obtain ⟨i, _, hi⟩ := hw
        exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hSS h2 hg hAS hprom hck hcA
  exact PEqualNP.Outside.L_meta_782.assemble n m k S C o c hSS h2 hg hAS hprom hck hcA
