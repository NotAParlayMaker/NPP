import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4915

open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost PEqualNP.SharedBlockCost

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  exact foldl_getD_gate C.gates x j hj

def V (C : Circuit) {N : ℕ} (x : Fin N → Bool) (u : ℕ) : Bool := val C (List.ofFn x) u

def gi (C : Circuit) (k : ℕ) : List ℕ := ((C.gates[k]?).map Gate.inputs).getD []

def in0 (C : Circuit) (k : ℕ) : ℕ := (gi C k).getD 0 0

def in1 (C : Circuit) (k : ℕ) : ℕ := (gi C k).getD 1 0

def oh (N v : ℕ) : Fin N → Bool := fun z => decide (z.val = v)

def S (C : Circuit) (N w : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun v => V C (oh N v) w = true)

def mnF (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.min' h else 0

def mn (C : Circuit) (N w : ℕ) : ℕ := mnF (S C N w)

def kap (C : Circuit) (N k : ℕ) : ℕ := max (mn C N (in0 C k)) (mn C N (in1 C k))

lemma V_input (C : Circuit) {N : ℕ} (x : Fin N → Bool) {u : ℕ} (hu : u < N) :
    V C x u = x ⟨u, hu⟩ := by
  unfold V
  rw [val_input (n := N) (by simp) hu]
  simp [List.getD_eq_getElem?_getD, hu]

lemma op_or {o : GateOp} (h : isOrOp o = true) : o = GateOp.or := by
  cases o <;> simp_all [isOrOp]

lemma gate_two {N : ℕ} {C : Circuit} (hOr : IsOrCircuit N C) {k : ℕ}
    (hk : k < C.gates.length) :
    (C.gates[k]).inputs = [in0 C k, in1 C k] ∧ in0 C k < N + k ∧ in1 C k < N + k ∧
      (C.gates[k]).op = GateOp.or := by
  obtain ⟨hop, hl, hr⟩ := hOr k hk
  have e : gi C k = (C.gates[k]).inputs := by
    simp [gi, List.getElem?_eq_getElem hk]
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have ha := hr a (by simp [hab])
  have hb := hr b (by simp [hab])
  refine ⟨?_, ?_, ?_, op_or hop⟩
  · simp [in0, in1, e, hab]
  · simpa [in0, e, hab] using ha
  · simpa [in1, e, hab] using hb

lemma V_or {N : ℕ} {C : Circuit} (hOr : IsOrCircuit N C) {k : ℕ}
    (hk : k < C.gates.length) (x : Fin N → Bool) :
    V C x (N + k) = (V C x (in0 C k) || V C x (in1 C k)) := by
  obtain ⟨h2, ha, hb, hop⟩ := gate_two hOr hk
  unfold V
  rw [val_gate (n := N) (by simp) hk, h2, hop]
  simp [GateOp.eval, ha, hb]

lemma memS {C : Circuit} {N w v : ℕ} : v ∈ S C N w ↔ v < N ∧ V C (oh N v) w = true := by
  simp [S]

lemma S_or {N : ℕ} {C : Circuit} (hOr : IsOrCircuit N C) {k : ℕ}
    (hk : k < C.gates.length) (v : ℕ) :
    v ∈ S C N (N + k) ↔ v ∈ S C N (in0 C k) ∨ v ∈ S C N (in1 C k) := by
  simp only [memS, V_or hOr hk, Bool.or_eq_true]
  tauto

lemma mn_mem {C : Circuit} {N w : ℕ} (h : (S C N w).Nonempty) : mn C N w ∈ S C N w := by
  unfold mn mnF; rw [dite_eq_left_of_eq_true (eq_true h)]; exact Finset.min'_mem _ _

lemma mn_le {C : Circuit} {N w v : ℕ} (h : v ∈ S C N w) : mn C N w ≤ v := by
  unfold mn mnF; rw [dite_eq_left_of_eq_true (eq_true ⟨v, h⟩)]; exact Finset.min'_le _ _ h

lemma S_input {C : Circuit} {N w : ℕ} (hw : w < N) (v : ℕ) : v ∈ S C N w ↔ v = w := by
  rw [memS, V_input C _ hw]
  simp [oh]
  omega

lemma kill {N : ℕ} {C : Circuit} (hOr : IsOrCircuit N C) :
    ∀ w, w < N + C.gates.length → ∀ v ∈ S C N w, v ≠ mn C N w →
      ∃ g < C.gates.length, S C N (N + g) ⊆ S C N w ∧ kap C N g = v ∧
        v ∈ S C N (N + g) ∧ v ≠ mn C N (N + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwl v hv hne
  by_cases hw : w < N
  · exfalso
    have h1 := (S_input hw _).1 hv
    have h2 := (S_input hw _).1 (mn_mem ⟨v, hv⟩)
    exact hne (h1.trans h2.symm)
  obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
  have hk : k < C.gates.length := by omega
  obtain ⟨_, ha, hb, _⟩ := gate_two hOr hk
  have subA : S C N (in0 C k) ⊆ S C N (N + k) :=
    fun z hz => (S_or hOr hk _).2 (Or.inl hz)
  have subB : S C N (in1 C k) ⊆ S C N (N + k) :=
    fun z hz => (S_or hOr hk _).2 (Or.inr hz)
  by_cases c1 : v ∈ S C N (in0 C k) ∧ v ≠ mn C N (in0 C k)
  · obtain ⟨g, hg, hsub, hk2, hvs, hne2⟩ := ih _ ha (by omega) v c1.1 c1.2
    exact ⟨g, hg, hsub.trans subA, hk2, hvs, hne2⟩
  by_cases c2 : v ∈ S C N (in1 C k) ∧ v ≠ mn C N (in1 C k)
  · obtain ⟨g, hg, hsub, hk2, hvs, hne2⟩ := ih _ hb (by omega) v c2.1 c2.2
    exact ⟨g, hg, hsub.trans subB, hk2, hvs, hne2⟩
  refine ⟨k, hk, subset_refl _, ?_, hv, hne⟩
  have hm := mn_mem (C := C) (N := N) (w := N + k) ⟨v, hv⟩
  have hmw := mn_le (C := C) (N := N) (w := N + k) hv
  unfold kap
  rcases (S_or hOr hk _).1 hv with h | h
  · have e : v = mn C N (in0 C k) := by
      by_contra h'; exact c1 ⟨h, h'⟩
    have l1 := mn_le (subA (mn_mem ⟨v, h⟩))
    rcases (S_or hOr hk _).1 hm with h3 | h3
    · have := mn_le h3; omega
    · have := mn_le h3
      have := mn_le (subB (mn_mem ⟨_, h3⟩))
      omega
  · have e : v = mn C N (in1 C k) := by
      by_contra h'; exact c2 ⟨h, h'⟩
    have l1 := mn_le (subB (mn_mem ⟨v, h⟩))
    rcases (S_or hOr hk _).1 hm with h3 | h3
    · have := mn_le h3
      have := mn_le (subA (mn_mem ⟨_, h3⟩))
      omega
    · have := mn_le h3; omega

lemma S_eq {N : ℕ} {C : Circuit} {w : ℕ} {s : Finset (Fin N)} (hc : ComputesOr N C w s) :
    S C N w = s.image Fin.val := by
  ext v
  rw [memS, Finset.mem_image]
  have key : ∀ x : Fin N → Bool, V C x w = true ↔ ∃ i ∈ s, x i = true := fun x => hc.2 x
  constructor
  · rintro ⟨hv, h⟩
    obtain ⟨i, hi, hx⟩ := (key _).1 h
    exact ⟨i, hi, by simpa [oh] using hx⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, (key _).2 ⟨i, hi, by simp [oh]⟩⟩

open Classical in
noncomputable def Edg {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

lemma mem_Edg {n : ℕ} {G : SimpleGraph (Fin n)} {e : Fin n × Fin n} :
    e ∈ Edg G ↔ e.1 < e.2 ∧ G.Adj e.1 e.2 := by
  simp [Edg]

def ord {n : ℕ} (a b : Fin n) : Fin n × Fin n := if a < b then (a, b) else (b, a)

lemma ord_mem {n : ℕ} {G : SimpleGraph (Fin n)} {a b : Fin n} (h : G.Adj a b) :
    ord a b ∈ Edg G := by
  have hne := G.ne_of_adj h
  rw [mem_Edg]
  unfold ord
  split_ifs with h1
  · exact ⟨h1, h⟩
  · refine ⟨?_, h.symm⟩
    simp only [Fin.lt_def, Fin.ext_iff] at h1 hne ⊢
    omega

lemma ord_inj {n : ℕ} {a b b' : Fin n} (h : ord a b = ord a b') : b = b' := by
  unfold ord at h
  split_ifs at h <;> simp only [Prod.ext_iff, Fin.ext_iff, Fin.lt_def] at * <;> omega

lemma ord_inj' {n : ℕ} {a a' b : Fin n} (h : ord a b = ord a' b) : a = a' := by
  unfold ord at h
  split_ifs at h <;> simp only [Prod.ext_iff, Fin.ext_iff, Fin.lt_def] at * <;> omega

lemma ord_cases {n : ℕ} (u v : Fin n) :
    ((ord u v).1 = u ∧ (ord u v).2 = v) ∨ ((ord u v).1 = v ∧ (ord u v).2 = u) := by
  unfold ord; split_ifs <;> simp

open Classical in
noncomputable def P {n : ℕ} (F : Finset (Block n)) (e : Fin n × Fin n) : Block n :=
  if h : ∃ p ∈ F, BlockCovers p e.1 e.2 then h.choose else (∅, ∅)

lemma P_spec {n : ℕ} {G : SimpleGraph (Fin n)} {F : Finset (Block n)} (hF : IsBlockCover G F)
    {e : Fin n × Fin n} (he : e ∈ Edg G) : P F e ∈ F ∧ BlockCovers (P F e) e.1 e.2 := by
  have h : ∃ p ∈ F, BlockCovers p e.1 e.2 := hF.2 _ _ (mem_Edg.1 he).2
  unfold P
  rw [dif_pos h]
  exact h.choose_spec

open Classical in
noncomputable def aE {n : ℕ} (p : Block n) (e : Fin n × Fin n) : Fin n :=
  if e.1 ∈ p.1 then e.1 else e.2

open Classical in
noncomputable def bE {n : ℕ} (p : Block n) (e : Fin n × Fin n) : Fin n :=
  if e.1 ∈ p.1 then e.2 else e.1

lemma ab_cases {n : ℕ} (p : Block n) (e : Fin n × Fin n) :
    (aE p e = e.1 ∧ bE p e = e.2) ∨ (aE p e = e.2 ∧ bE p e = e.1) := by
  unfold aE bE; split_ifs <;> simp

lemma ab_spec {n : ℕ} {G : SimpleGraph (Fin n)} {p : Block n} (hb : IsBlock G p)
    {e : Fin n × Fin n} (hc : BlockCovers p e.1 e.2) : aE p e ∈ p.1 ∧ bE p e ∈ p.2 := by
  unfold aE bE
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have : e.1 ∉ p.1 := Finset.disjoint_right.1 hb.1 h2
    simp [this, h1, h2]

lemma ab_ord {n : ℕ} (p : Block n) {e : Fin n × Fin n} (he : e.1 < e.2) :
    ord (aE p e) (bE p e) = e := by
  have he' : e.1.val < e.2.val := he
  unfold aE bE ord
  by_cases h1 : e.1 ∈ p.1
  · simp only [if_pos h1, if_pos he]
  · simp only [if_neg h1]
    have h3 : ¬ e.2 < e.1 := by simp only [Fin.lt_def]; omega
    rw [if_neg h3]

noncomputable def Rep {n : ℕ} (F : Finset (Block n)) (e : Fin n × Fin n) : Prop :=
  (aE (P F e) e).val = mnF ((P F e).1.image Fin.val) ∧
    (bE (P F e) e).val = mnF ((P F e).2.image Fin.val)

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (e : Fin n × Fin n) (g : ℕ) : Prop :=
  g < C.gates.length ∧ ∃ c : Fin n, ((c = e.1 ∧ kap C n g = e.2.val) ∨
    (c = e.2 ∧ kap C n g = e.1.val)) ∧ kap C n g ∈ S C n (n + g) ∧
    kap C n g ≠ mn C n (n + g) ∧ ∀ z ∈ S C n (n + g), ∃ hz : z < n, G.Adj c ⟨z, hz⟩

lemma side1 {n : ℕ} {F : Finset (Block n)} {p : Block n} (hp : p ∈ F) : p.1 ∈ sides F := by
  unfold sides
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)

lemma side2 {n : ℕ} {F : Finset (Block n)} {p : Block n} (hp : p ∈ F) : p.2 ∈ sides F := by
  unfold sides
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)

lemma good_ex {n : ℕ} {G : SimpleGraph (Fin n)} {F : Finset (Block n)} {C : Circuit}
    (hF : IsBlockCover G F) (hC : IsOrCircuitFor n C (sides F)) {e : Fin n × Fin n}
    (he : e ∈ Edg G) (hr : ¬ Rep F e) : ∃ g, Good G C e g := by
  obtain ⟨hpF, hcov⟩ := P_spec hF he
  have hb := hF.1 _ hpF
  obtain ⟨ha, hbm⟩ := ab_spec hb hcov
  unfold Rep at hr
  by_cases h1 : (aE (P F e) e).val = mnF ((P F e).1.image Fin.val)
  · have h2 : (bE (P F e) e).val ≠ mnF ((P F e).2.image Fin.val) := fun h => hr ⟨h1, h⟩
    obtain ⟨w, hw, hco⟩ := hC.2 _ (side2 hpF)
    have hS := S_eq hco
    obtain ⟨g, hg, hsub, hk, hvs, hne⟩ := kill hC.1 w hw (bE (P F e) e).val
      (by rw [hS]; exact Finset.mem_image_of_mem _ hbm) (by unfold mn; rw [hS]; exact h2)
    refine ⟨g, hg, aE (P F e) e, ?_, by rw [hk]; exact hvs, by rw [hk]; exact hne, ?_⟩
    · rcases ab_cases (P F e) e with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · left; rw [hk, x1, x2]; exact ⟨rfl, rfl⟩
      · right; rw [hk, x1, x2]; exact ⟨rfl, rfl⟩
    · intro z hz
      have hz2 := hsub hz
      rw [hS, Finset.mem_image] at hz2
      obtain ⟨b, hb2, rfl⟩ := hz2
      exact ⟨b.isLt, hb.2.2.2 _ ha _ hb2⟩
  · obtain ⟨w, hw, hco⟩ := hC.2 _ (side1 hpF)
    have hS := S_eq hco
    obtain ⟨g, hg, hsub, hk, hvs, hne⟩ := kill hC.1 w hw (aE (P F e) e).val
      (by rw [hS]; exact Finset.mem_image_of_mem _ ha) (by unfold mn; rw [hS]; exact h1)
    refine ⟨g, hg, bE (P F e) e, ?_, by rw [hk]; exact hvs, by rw [hk]; exact hne, ?_⟩
    · rcases ab_cases (P F e) e with ⟨x1, x2⟩ | ⟨x1, x2⟩
      · right; rw [hk, x1, x2]; exact ⟨rfl, rfl⟩
      · left; rw [hk, x1, x2]; exact ⟨rfl, rfl⟩
    · intro z hz
      have hz2 := hsub hz
      rw [hS, Finset.mem_image] at hz2
      obtain ⟨a, ha2, rfl⟩ := hz2
      exact ⟨a.isLt, (hb.2.2.2 _ ha2 _ hbm).symm⟩

lemma twoN {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) {a a' b b' : Fin n} (ha : a ≠ a') (hb : b ≠ b')
    (h1 : G.Adj a b) (h2 : G.Adj a' b) (h3 : G.Adj a b') (h4 : G.Adj a' b') : False := by
  have c := hG a a' ha
  have hs : ({b, b'} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj a' w) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [*]
  have c2 := Finset.card_le_card hs
  rw [Finset.card_pair hb] at c2
  omega

lemma good_inj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hG : PEqualNP.TopForm.NoFourCycle G) {e e' : Fin n × Fin n} (he : e ∈ Edg G)
    (he' : e' ∈ Edg G) {g : ℕ} (g1 : Good G C e g) (g2 : Good G C e' g) : e = e' := by
  obtain ⟨_, c, o1, hv, hne, hadj⟩ := g1
  obtain ⟨_, c', o2, _, _, hadj'⟩ := g2
  have hm := mn_mem (C := C) (N := n) (w := n + g) ⟨_, hv⟩
  obtain ⟨hv1, a1⟩ := hadj _ hv
  obtain ⟨hm1, a2⟩ := hadj _ hm
  obtain ⟨_, a3⟩ := hadj' _ hv
  obtain ⟨_, a4⟩ := hadj' _ hm
  have hcc : c = c' := by
    by_contra hcc
    exact twoN hG hcc (by simp only [ne_eq, Fin.ext_iff]; exact hne) a1 a3 a2 a4
  subst hcc
  have l1 : e.1.val < e.2.val := (mem_Edg.1 he).1
  have l2 : e'.1.val < e'.2.val := (mem_Edg.1 he').1
  rcases o1 with ⟨x1, y1⟩ | ⟨x1, y1⟩ <;> rcases o2 with ⟨x2, y2⟩ | ⟨x2, y2⟩ <;>
    rw [x1] at x2 <;> simp only [Fin.ext_iff] at x2 <;> ext <;> omega

lemma rep_inj {n : ℕ} {G : SimpleGraph (Fin n)} {F : Finset (Block n)}
    {e e' : Fin n × Fin n} (he : e ∈ Edg G) (he' : e' ∈ Edg G) (r1 : Rep F e) (r2 : Rep F e')
    (hP : P F e = P F e') : e = e' := by
  unfold Rep at r1 r2
  rw [← hP] at r2
  have x1 : aE (P F e) e = aE (P F e) e' := Fin.ext (r1.1.trans r2.1.symm)
  have x2 : bE (P F e) e = bE (P F e) e' := Fin.ext (r1.2.trans r2.2.symm)
  rw [← ab_ord (P F e) (mem_Edg.1 he).1, ← ab_ord (P F e) (mem_Edg.1 he').1, x1, x2]

open Classical in
noncomputable def phi {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n)) (C : Circuit)
    (e : Fin n × Fin n) : Block n ⊕ ℕ :=
  if Rep F e then Sum.inl (P F e)
  else Sum.inr (if h : ∃ g, Good G C e g then h.choose else 0)

lemma card_E {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {F : Finset (Block n)}
    {C : Circuit} (hG : PEqualNP.TopForm.NoFourCycle G) (hF : IsBlockCover G F)
    (hC : IsOrCircuitFor n C (sides F)) : (Edg G).card ≤ F.card + C.gates.length := by
  classical
  have gs : ∀ e ∈ Edg G, ¬ Rep F e →
      Good G C e (if h : ∃ g, Good G C e g then h.choose else 0) := by
    intro e he hr
    have h := good_ex hF hC he hr
    rw [dif_pos h]
    exact h.choose_spec
  have c := Finset.card_le_card_of_injOn (phi G F C) (s := Edg G)
    (t := F.disjSum (Finset.range C.gates.length)) (by
      intro e he
      have he' : e ∈ Edg G := he
      unfold phi
      rw [Finset.mem_coe]
      by_cases hr : Rep F e
      · rw [if_pos hr]; simp [(P_spec hF he').1]
      · rw [if_neg hr]; simp [(gs e he' hr).1]) (by
      intro e he e' he' hee
      have h1 : e ∈ Edg G := he
      have h2 : e' ∈ Edg G := he'
      unfold phi at hee
      by_cases r1 : Rep F e <;> by_cases r2 : Rep F e' <;> simp only [r1, r2, if_true,
        if_false, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hee
      · exact rep_inj h1 h2 r1 r2 hee
      · have g1 := gs e h1 r1
        rw [hee] at g1
        exact good_inj hG h1 h2 g1 (gs e' h2 r2))
  rw [Finset.card_disjSum, Finset.card_range] at c
  exact c

open Classical in
noncomputable def rho {n : ℕ} (F : Finset (Block n)) (p : Block n) : Block n :=
  (p.1.filter (fun a => ∃ b ∈ p.2, P F (ord a b) = p),
    p.2.filter (fun b => ∃ a ∈ p.1, P F (ord a b) = p))

open Classical in
noncomputable def Ep {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n)) (p : Block n) :
    Finset (Fin n × Fin n) := (Edg G).filter (fun e => P F e = p)

open Classical in
noncomputable def Fp {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Block n)) :
    Finset (Block n) := (F.filter (fun p => (Ep G F p).Nonempty)).image (rho F)

lemma ends_rho {n : ℕ} {G : SimpleGraph (Fin n)} {F : Finset (Block n)} (hF : IsBlockCover G F)
    {e : Fin n × Fin n} (he : e ∈ Edg G) :
    aE (P F e) e ∈ (rho F (P F e)).1 ∧ bE (P F e) e ∈ (rho F (P F e)).2 := by
  obtain ⟨hpF, hcov⟩ := P_spec hF he
  obtain ⟨ha, hb⟩ := ab_spec (hF.1 _ hpF) hcov
  have ho := ab_ord (P F e) (mem_Edg.1 he).1
  unfold rho
  simp only [Finset.mem_filter]
  exact ⟨⟨ha, _, hb, by rw [ho]⟩, ⟨hb, _, ha, by rw [ho]⟩⟩

lemma cover_Fp {n : ℕ} {G : SimpleGraph (Fin n)} {F : Finset (Block n)} (hF : IsBlockCover G F) :
    IsBlockCover G (Fp G F) := by
  classical
  constructor
  · intro q hq
    unfold Fp at hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [Finset.mem_filter] at hp
    obtain ⟨hpF, ⟨e, he⟩⟩ := hp
    unfold Ep at he
    rw [Finset.mem_filter] at he
    obtain ⟨he, hPe⟩ := he
    have hb := hF.1 _ hpF
    have hr := ends_rho hF he
    rw [hPe] at hr
    refine ⟨?_, ⟨_, hr.1⟩, ⟨_, hr.2⟩, ?_⟩
    · unfold rho
      exact Finset.disjoint_filter_filter hb.1
    · intro a ha b hb2
      unfold rho at ha hb2
      exact hb.2.2.2 a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb2).1
  · intro u v huv
    have he := ord_mem huv
    have hpF := (P_spec hF he).1
    refine ⟨rho F (P F (ord u v)), ?_, ?_⟩
    · unfold Fp
      apply Finset.mem_image_of_mem
      rw [Finset.mem_filter]
      refine ⟨hpF, ord u v, ?_⟩
      unfold Ep
      rw [Finset.mem_filter]
      exact ⟨he, rfl⟩
    · have hr := ends_rho hF he
      unfold BlockCovers
      rcases ab_cases (P F (ord u v)) (ord u v) with ⟨x1, x2⟩ | ⟨x1, x2⟩ <;>
        rcases ord_cases u v with ⟨y1, y2⟩ | ⟨y1, y2⟩ <;>
        rw [x1, x2] at hr <;> rw [y1, y2] at hr <;> tauto

lemma cost_rho {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {F : Finset (Block n)}
    (hG : PEqualNP.TopForm.NoFourCycle G) (hF : IsBlockCover G F) {p : Block n} (hp : p ∈ F) :
    blockCost (rho F p) ≤ (Ep G F p).card := by
  classical
  have hb := hF.1 _ hp
  unfold blockCost
  have star : p.1.card ≤ 1 ∨ p.2.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨b, hb1, b', hb', hbb⟩ := Finset.one_lt_card.1 h.2
    exact twoN hG haa hbb (hb.2.2.2 _ ha _ hb1) (hb.2.2.2 _ ha' _ hb1) (hb.2.2.2 _ ha _ hb')
      (hb.2.2.2 _ ha' _ hb')
  rcases star with h | h
  · obtain ⟨c, hc⟩ := hb.2.1
    have r1 : (rho F p).1.card ≤ 1 := by
      unfold rho
      exact (Finset.card_filter_le _ _).trans h
    have r2 : (rho F p).2.card ≤ (Ep G F p).card := by
      apply Finset.card_le_card_of_injOn (fun b => ord c b)
      · intro b hb2
        unfold rho at hb2
        rw [Finset.mem_coe, Finset.mem_filter] at hb2
        obtain ⟨hb3, a, ha, hP⟩ := hb2
        have e : a = c := Finset.card_le_one.1 h a ha c hc
        subst e
        unfold Ep
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨ord_mem (hb.2.2.2 _ ha _ hb3), hP⟩
      · intro b _ b' _ hbb
        exact ord_inj hbb
    omega
  · obtain ⟨c, hc⟩ := hb.2.2.1
    have r1 : (rho F p).2.card ≤ 1 := by
      unfold rho
      exact (Finset.card_filter_le _ _).trans h
    have r2 : (rho F p).1.card ≤ (Ep G F p).card := by
      apply Finset.card_le_card_of_injOn (fun a => ord a c)
      · intro a ha2
        unfold rho at ha2
        rw [Finset.mem_coe, Finset.mem_filter] at ha2
        obtain ⟨ha3, b, hb2, hP⟩ := ha2
        have e : b = c := Finset.card_le_one.1 h b hb2 c hc
        subst e
        unfold Ep
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨ord_mem (hb.2.2.2 _ ha3 _ hb2), hP⟩
      · intro a _ a' _ haa
        exact ord_inj' haa
    omega

lemma sum_Fp {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {F : Finset (Block n)}
    (hG : PEqualNP.TopForm.NoFourCycle G) (hF : IsBlockCover G F) :
    (∑ q ∈ Fp G F, blockCost q) ≤ (Edg G).card ∧ (Fp G F).card ≤ F.card := by
  classical
  constructor
  · unfold Fp
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)).trans ?_
    refine (Finset.sum_le_sum (fun p hp => cost_rho hG hF (Finset.mem_filter.1 hp).1)).trans ?_
    refine (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans ?_
    rw [Finset.card_eq_sum_card_fiberwise (f := P F) (t := F)
      (fun e he => (P_spec hF he).1)]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro p _
    unfold Ep
    congr 1
  · unfold Fp
    exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

end PEqualNP.Outside.L_meta_4915

theorem PEqualNP.Outside.L_meta_4915 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4 := by
  intro n G _ c hG hS
  obtain ⟨F, hF, k, ⟨C, hC, hlen⟩, hk⟩ := hS
  have e1 := PEqualNP.Outside.L_meta_4915.card_E hG hF hC
  obtain ⟨e2, e3⟩ := PEqualNP.Outside.L_meta_4915.sum_Fp hG hF
  refine ⟨PEqualNP.Outside.L_meta_4915.Fp G F, PEqualNP.Outside.L_meta_4915.cover_Fp hF, ?_⟩
  unfold PEqualNP.BicliqueBlockCost.familyCost
  omega
