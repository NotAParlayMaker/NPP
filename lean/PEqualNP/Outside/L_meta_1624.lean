import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1624

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma val_ofFn' {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩

lemma op_cases {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C) {r : ℕ}
    (hr : r < C.gates.length) :
    ((gateAt C r).op = GateOp.and ∨ (gateAt C r).op = GateOp.or) ∧
      (gateAt C r).inputs.length ≤ 2 := by
  have hg := hM _ (gateAt_mem hr)
  refine ⟨?_, hg.2⟩
  rcases hg.1 with h | h
  · exact Or.inl h
  · exact Or.inr h

-- wires of an AND/OR list are monotone in the input
lemma val_mono {n : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [val_ofFn' C y w h1]
      rw [val_ofFn' C x w h1] at hw
      exact hxy _ hw
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨r, rfl⟩ : ∃ r, w = n + r := ⟨w - n, by omega⟩
        have hr : r < C.gates.length := by omega
        rcases (op_cases hM hr).1 with hop | hop
        · rw [val_and (by simp) hr hop] at hw ⊢
          intro i hi
          exact ⟨(hw i hi).1, ih i (hw i hi).1 (hw i hi).2⟩
        · rw [val_or (by simp) hr hop] at hw ⊢
          obtain ⟨i, hi, hlt, hv⟩ := hw
          exact ⟨i, hi, hlt, ih i hlt hv⟩
      · rw [val_ge (n := n) (by simp) (by omega)] at hw
        cases hw

lemma two_of_le2 (l : List ℕ) (h : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ c ∈ l, c = a ∨ c = b := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp at ha hb; omega
  · intro c hc; simp at ha hb hc; omega
  · simp at h

-- the singleton part of a wire: the points p at which the wire is true on the input e_p
def part (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val C (List.ofFn (fun i : Fin n => decide (i = p))) w = true)

lemma mem_part {n : ℕ} {C : Circuit} {w : ℕ} {p : Fin n} :
    p ∈ part n C w ↔ val C (List.ofFn (fun i : Fin n => decide (i = p))) w = true := by
  simp [part]

-- the gates below K that are false at z and have at least two points in their singleton part
def goodSet {n : ℕ} (C : Circuit) (z : Fin n → Bool) (K : ℕ) : Finset ℕ :=
  (Finset.range K).filter (fun k => val C (List.ofFn z) (n + k) = false ∧
    2 ≤ (part n C (n + k)).card)

lemma mem_goodSet {n : ℕ} {C : Circuit} {z : Fin n → Bool} {K k : ℕ} :
    k ∈ goodSet C z K ↔ k < K ∧ val C (List.ofFn z) (n + k) = false ∧
      2 ≤ (part n C (n + k)).card := by
  simp [goodSet]

lemma goodSet_mono {n : ℕ} (C : Circuit) (z : Fin n → Bool) (K : ℕ) :
    goodSet C z K ⊆ goodSet C z (K + 1) := by
  intro k hk
  rw [mem_goodSet] at hk ⊢
  exact ⟨by omega, hk.2⟩

-- labels: every wire false at z has its singleton part inside one label class, and the number
-- of label classes drops by at most one per good gate
lemma inv {n : ℕ} {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C) (hR : ReadsBack n C)
    (z : Fin n → Bool) :
    ∀ K, K ≤ C.gates.length → ∃ lab : Fin n → ℕ,
      (∀ w, w < n + K → val C (List.ofFn z) w = false →
        ∀ p ∈ part n C w, ∀ q ∈ part n C w, lab p = lab q) ∧
      n ≤ (Finset.univ.image lab).card + (goodSet C z K).card := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨fun p => p.val, ?_, ?_⟩
    · intro w hw _ p hp q hq
      have hw' : w < n := by omega
      rw [mem_part, val_ofFn' C _ w hw'] at hp hq
      have e1 := of_decide_eq_true hp
      have e2 := of_decide_eq_true hq
      show p.val = q.val
      rw [← e1, ← e2]
    · rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ, Fintype.card_fin]
      omega
  | succ K ih =>
    intro hK
    have hKlt : K < C.gates.length := by omega
    obtain ⟨lab, ha, hb⟩ := ih (by omega)
    have hmono : (goodSet C z K).card ≤ (goodSet C z (K + 1)).card :=
      Finset.card_le_card (goodSet_mono C z K)
    have caseA : (val C (List.ofFn z) (n + K) = false →
        ∀ p ∈ part n C (n + K), ∀ q ∈ part n C (n + K), lab p = lab q) →
        ∃ lab' : Fin n → ℕ, (∀ w, w < n + (K + 1) → val C (List.ofFn z) w = false →
          ∀ p ∈ part n C w, ∀ q ∈ part n C w, lab' p = lab' q) ∧
          n ≤ (Finset.univ.image lab').card + (goodSet C z (K + 1)).card := by
      intro h
      refine ⟨lab, ?_, by omega⟩
      intro w hw hlow
      by_cases hwK : w < n + K
      · exact ha w hwK hlow
      · have hwe : w = n + K := by omega
        subst hwe
        exact h hlow
    by_cases hlow : val C (List.ofFn z) (n + K) = false
    swap
    · exact caseA (fun h => absurd h hlow)
    have hin : ∀ i ∈ (gateAt C K).inputs, i < n + K := hR K hKlt
    rcases (op_cases hM hKlt).1 with hop | hop
    · apply caseA
      intro _ p hp q hq
      have hnot : ¬ (∀ i ∈ (gateAt C K).inputs, i < n + K ∧ val C (List.ofFn z) i = true) := by
        intro hall
        have ht := (val_and (n := n) (x := List.ofFn z) (by simp) hKlt hop).mpr hall
        rw [hlow] at ht; cases ht
      have hex : ∃ i ∈ (gateAt C K).inputs, val C (List.ofFn z) i = false := by
        by_contra hno
        apply hnot
        intro i hi
        refine ⟨hin i hi, ?_⟩
        by_contra hf
        exact hno ⟨i, hi, by simpa using hf⟩
      obtain ⟨i, hi, hiz⟩ := hex
      have sub : ∀ r ∈ part n C (n + K), r ∈ part n C i := by
        intro r hr
        rw [mem_part] at hr ⊢
        exact ((val_and (n := n) (by simp) hKlt hop).mp hr i hi).2
      exact ha i (hin i hi) hiz p (sub p hp) q (sub q hq)
    · have hlowin : ∀ i ∈ (gateAt C K).inputs, val C (List.ofFn z) i = false := by
        intro i hi
        by_contra hne
        have ht : val C (List.ofFn z) i = true := by simpa using hne
        have ht2 := (val_or (n := n) (x := List.ofFn z) (by simp) hKlt hop).mpr
          ⟨i, hi, hin i hi, ht⟩
        rw [hlow] at ht2; cases ht2
      have hsrc : ∀ r ∈ part n C (n + K), ∃ i ∈ (gateAt C K).inputs, r ∈ part n C i := by
        intro r hr
        rw [mem_part] at hr
        obtain ⟨i, hi, _, hv⟩ := (val_or (n := n) (by simp) hKlt hop).mp hr
        exact ⟨i, hi, mem_part.mpr hv⟩
      by_cases hc : ∀ p ∈ part n C (n + K), ∀ q ∈ part n C (n + K), lab p = lab q
      · exact caseA (fun _ => hc)
      have hex2 : ∃ p ∈ part n C (n + K), ∃ q ∈ part n C (n + K), lab p ≠ lab q := by
        by_contra hno
        apply hc
        intro p hp q hq
        by_contra hpq
        exact hno ⟨p, hp, q, hq, hpq⟩
      obtain ⟨p, hp, q, hq, hpq⟩ := hex2
      obtain ⟨a, haIn, hpa⟩ := hsrc p hp
      obtain ⟨b, hbIn, hqb⟩ := hsrc q hq
      have hab : a ≠ b := by
        intro habe
        rw [← habe] at hqb
        exact hpq (ha a (hin a haIn) (hlowin a haIn) p hpa q hqb)
      have hall := two_of_le2 _ (op_cases hM hKlt).2 a b haIn hbIn hab
      have hpne : p ≠ q := fun h => hpq (by rw [h])
      have hgood : (goodSet C z K).card + 1 ≤ (goodSet C z (K + 1)).card := by
        have hnotin : K ∉ goodSet C z K := by
          rw [mem_goodSet]; omega
        have hsub : insert K (goodSet C z K) ⊆ goodSet C z (K + 1) := by
          intro k hk
          rw [Finset.mem_insert] at hk
          rcases hk with hk | hk
          · rw [hk, mem_goodSet]
            have h2 := Finset.one_lt_card.mpr ⟨p, hp, q, hq, hpne⟩
            exact ⟨by omega, hlow, by omega⟩
          · exact goodSet_mono C z K hk
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_insert_eq_ite, if_neg hnotin] at hcard
        exact hcard
      have key : ∀ t ∈ part n C (n + K),
          (if lab t = lab q then lab p else lab t) = lab p := by
        intro t ht
        obtain ⟨c, hcIn, htc⟩ := hsrc t ht
        rcases hall c hcIn with hca | hcb
        · rw [hca] at htc
          have hl : lab t = lab p := ha a (hin a haIn) (hlowin a haIn) t htc p hpa
          rw [hl]
          split_ifs <;> rfl
        · rw [hcb] at htc
          have hl : lab t = lab q := ha b (hin b hbIn) (hlowin b hbIn) t htc q hqb
          rw [if_pos hl]
      refine ⟨fun r => if lab r = lab q then lab p else lab r, ?_, ?_⟩
      · intro w hw hlw r hr s hs
        by_cases hwK : w < n + K
        · have hrs := ha w hwK hlw r hr s hs
          show (if lab r = lab q then lab p else lab r) = (if lab s = lab q then lab p else lab s)
          rw [hrs]
        · have hwe : w = n + K := by omega
          subst hwe
          show (if lab r = lab q then lab p else lab r) = (if lab s = lab q then lab p else lab s)
          rw [key r hr, key s hs]
      · have himg : (Finset.univ.image lab).card - 1 ≤
            (Finset.univ.image (fun r => if lab r = lab q then lab p else lab r)).card := by
          refine le_trans (Finset.pred_card_le_card_erase (a := lab q)) (Finset.card_le_card ?_)
          intro t ht
          rw [Finset.mem_erase, Finset.mem_image] at ht
          obtain ⟨hne, r, _, hrt⟩ := ht
          rw [Finset.mem_image]
          refine ⟨r, Finset.mem_univ _, ?_⟩
          rw [if_neg (by rw [hrt]; exact hne), hrt]
        omega

def gset {n m : ℕ} (L : Fin m → Finset (Fin n)) (D : Circuit) (j : Fin m) : Finset ℕ :=
  goodSet D (fun i : Fin n => decide (i ∉ L j)) D.gates.length

theorem main (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : Circuit) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (hM : PEqualNP.MetaComplexity.Monotone2 D) (hR : ReadsBack n D)
    (h1 : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true)
    (h0 : ∀ j : Fin m,
      (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  have hper : ∀ j, (A j).card - 1 ≤ (gset L D j).card := by
    intro j
    obtain ⟨lab, ha, hb⟩ := inv hM hR (fun i : Fin n => decide (i ∉ L j)) D.gates.length le_rfl
    by_cases hne : (A j).Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have ho : o j < n + D.gates.length := by
        by_contra hge
        have hf : val D (List.ofFn (fun i : Fin n => decide (i = p0))) (o j) = false :=
          val_ge (n := n) (by simp) (by omega)
        have h1' : val D (List.ofFn (fun i : Fin n => decide (i = p0))) (o j) = true :=
          h1 j p0 hp0
        rw [hf] at h1'; cases h1'
      have hconst : ∀ p ∈ A j, ∀ q ∈ A j, lab p = lab q := by
        intro p hp q hq
        exact ha (o j) ho (h0 j) p (mem_part.mpr (h1 j p hp)) q (mem_part.mpr (h1 j q hq))
      have c1 : ((Finset.univ \ A j).image lab).card ≤ n - (A j).card := by
        refine le_trans Finset.card_image_le ?_
        rw [Finset.card_univ_sdiff, Fintype.card_fin]
      have c2 : ((A j).image lab).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro s hs t ht
        rw [Finset.mem_image] at hs ht
        obtain ⟨p, hp, hps⟩ := hs
        obtain ⟨q, hq, hqt⟩ := ht
        rw [← hps, ← hqt]
        exact hconst p hp q hq
      have hc1 : (Finset.univ.image lab).card ≤ (n - (A j).card) + 1 := by
        have hu : (Finset.univ : Finset (Fin n)) = (Finset.univ \ A j) ∪ A j := by
          rw [Finset.sdiff_union_of_subset (Finset.subset_univ _)]
        rw [hu, Finset.image_union]
        exact le_trans (Finset.card_union_le _ _) (by omega)
      have hAn : (A j).card ≤ n := by
        have := Finset.card_le_univ (A j)
        rwa [Fintype.card_fin] at this
      have hb' : n ≤ (Finset.univ.image lab).card + (gset L D j).card := hb
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  have hsubL : ∀ j k, k ∈ gset L D j → part n D (n + k) ⊆ L j := by
    intro j k hk p hp
    have hk' := (mem_goodSet.mp hk).2.1
    rw [mem_part] at hp
    by_contra hpL
    have ht := val_mono hM (fun i : Fin n => decide (i = p)) (fun i : Fin n => decide (i ∉ L j))
      (by
        intro t ht
        have htp : t = p := of_decide_eq_true ht
        rw [htp]
        exact decide_eq_true hpL) (n + k) hp
    rw [hk'] at ht; cases ht
  have hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (gset L D i) (gset L D j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro k hki hkj
    have h2 : 2 ≤ (part n D (n + k)).card := (mem_goodSet.mp hki).2.2
    have h3 : (part n D (n + k)).card ≤ (L i ∩ L j).card :=
      Finset.card_le_card (Finset.subset_inter (hsubL i k hki) (hsubL j k hkj))
    have h4 := hL i j hij
    omega
  calc ∑ j : Fin m, ((A j).card - 1) ≤ ∑ j : Fin m, (gset L D j).card :=
        Finset.sum_le_sum (fun j _ => hper j)
    _ = (Finset.univ.biUnion (gset L D)).card :=
        (Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)).symm
    _ ≤ (Finset.range D.gates.length).card := Finset.card_le_card (by
        intro k hk
        rw [Finset.mem_biUnion] at hk
        obtain ⟨j, _, hk⟩ := hk
        rw [Finset.mem_range]
        exact (mem_goodSet.mp hk).1)
    _ = D.size := by simp [Circuit.size]

end PEqualNP.Outside.L_meta_1624

theorem PEqualNP.Outside.L_meta_1624 : ∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  intro n m L A D o hL hM hR _ h1 h0
  exact PEqualNP.Outside.L_meta_1624.main n m L A D o hL hM hR h1 h0
