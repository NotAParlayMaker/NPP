import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3256
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem all_false (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ U : List Bool, (∀ i, U.getD i false = false) → ∀ i, (wf gs U).getD i false = false := by
  induction gs with
  | nil => intro U h i; exact h i
  | cons g gs ih =>
    intro U h i
    rw [wf_cons]
    refine ih (fun g' hg' => hleg g' (by simp [hg'])) _ ?_ i
    intro t
    obtain ⟨hop, hlen⟩ := hleg g (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false) = false := by
      rw [hab]
      simp only [List.map_cons, List.map_nil, h]
      rcases hop with h' | h' <;> rw [h'] <;> rfl
    rw [hv]
    rcases Nat.lt_trichotomy t U.length with ht | ht | ht
    · rw [getD_snoc_lt _ _ _ ht]; exact h t
    · subst ht; rw [getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ ht]

theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _

theorem rep_false (n i : ℕ) : (List.replicate n false).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem to_true (B : List Bool) (n : ℕ) (hB : B.length = n) (i : ℕ) :
    B.getD i false = true → (List.replicate n true).getD i false = true := by
  intro h
  have hi : i < n := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at h
    exact absurd h (by simp)
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hi]

theorem from_false (B : List Bool) (n i : ℕ) :
    (List.replicate n false).getD i false = true → B.getD i false = true := by
  intro h
  rw [rep_false] at h
  exact absurd h (by simp)

theorem sandL (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (n w : ℕ)
    (h : ∀ x6 : Fin n → Bool, (wf gs (List.ofFn x6 ++ List.replicate n false)).getD w false
      = (wf gs (List.ofFn x6 ++ List.replicate n true)).getD w false)
    (A B : List Bool) (x6 : Fin n → Bool) (hA : A = List.ofFn x6) (hB : B.length = n) :
    (wf gs (A ++ B)).getD w false = (wf gs (A ++ List.replicate n false)).getD w false := by
  have lo_mid := mono2 gs hleg (A ++ List.replicate n false) (A ++ B) (by simp [hB])
    (app_mono A A _ B rfl (fun _ => id) (from_false B n)) w
  have mid_hi := mono2 gs hleg (A ++ B) (A ++ List.replicate n true) (by simp [hB])
    (app_mono A A B _ rfl (fun _ => id) (to_true B n hB)) w
  have e := h x6
  rw [← hA] at e
  cases hl : (wf gs (A ++ List.replicate n false)).getD w false
  · by_contra hne
    have hm : (wf gs (A ++ B)).getD w false = true := by simpa using hne
    have := mid_hi hm
    rw [← e, hl] at this
    exact absurd this (by simp)
  · exact lo_mid hl

theorem sandP (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (n w : ℕ)
    (h : ∀ x6 : Fin n → Bool, (wf gs (List.replicate n false ++ List.ofFn x6)).getD w false
      = (wf gs (List.replicate n true ++ List.ofFn x6)).getD w false)
    (A B : List Bool) (x6 : Fin n → Bool) (hB : B = List.ofFn x6) (hA : A.length = n) :
    (wf gs (A ++ B)).getD w false = (wf gs (List.replicate n false ++ B)).getD w false := by
  have lo_mid := mono2 gs hleg (List.replicate n false ++ B) (A ++ B) (by simp [hA])
    (app_mono _ A B B (by simp [hA]) (from_false A n) (fun _ => id)) w
  have mid_hi := mono2 gs hleg (A ++ B) (List.replicate n true ++ B) (by simp [hA])
    (app_mono A _ B B (by simp [hA]) (to_true A n hA) (fun _ => id)) w
  have e := h x6
  rw [← hB] at e
  cases hl : (wf gs (List.replicate n false ++ B)).getD w false
  · by_contra hne
    have hm : (wf gs (A ++ B)).getD w false = true := by simpa using hne
    have := mid_hi hm
    rw [← e, hl] at this
    exact absurd this (by simp)
  · exact lo_mid hl


abbrev V (C : Circuit) (n : ℕ) (l0 : Fin n) (S : Finset (Fin n)) (w : ℕ) : Bool :=
  (wf C.gates (PEqualNP.GenericRejection.incidenceInput S {l0})).getD w false

theorem inc_len (n : ℕ) (l0 : Fin n) (S : Finset (Fin n)) :
    (PEqualNP.GenericRejection.incidenceInput S {l0}).length = n + n := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem inc_mono (n : ℕ) (l0 : Fin n) (S S' : Finset (Fin n)) (h : S ⊆ S') (i : ℕ) :
    (PEqualNP.GenericRejection.incidenceInput S {l0}).getD i false = true →
    (PEqualNP.GenericRejection.incidenceInput S' {l0}).getD i false = true := by
  unfold PEqualNP.GenericRejection.incidenceInput
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ (by simpa using hi)]
    exact ofFn_mono n _ _ (fun v hv => by simp only [decide_eq_true_eq] at hv ⊢; exact h hv) i
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem V_mono (C : Circuit) (n : ℕ) (l0 : Fin n)
    (hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S S' : Finset (Fin n)) (h : S ⊆ S') (w : ℕ) :
    V C n l0 S w = true → V C n l0 S' w = true :=
  mono2 C.gates hleg _ _ (by rw [inc_len, inc_len]) (inc_mono n l0 S S' h) w

theorem V_point (C : Circuit) (n : ℕ) (l0 : Fin n) (S : Finset (Fin n)) (p : Fin n) :
    V C n l0 S p.val = decide (p ∈ S) := by
  unfold V
  rw [wf_keep _ _ _ (by rw [inc_len]; omega)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem V_line (C : Circuit) (n : ℕ) (l0 : Fin n) (S S' : Finset (Fin n)) (w : ℕ)
    (hw1 : n ≤ w) (hw2 : w < n + n) : V C n l0 S w = V C n l0 S' w := by
  unfold V
  rw [wf_keep _ _ _ (by rw [inc_len]; omega), wf_keep _ _ _ (by rw [inc_len]; omega)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp; omega)]
  simp

theorem gate2 (C : Circuit) (n : ℕ) (l0 : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (k : ℕ) (hk : k < C.gates.length) :
    ∃ a b, a < n + n + k ∧ b < n + n + k ∧
      (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) ∧
      PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] ∧
      (∀ S, C.gates[k].op = GateOp.and → V C n l0 S (n + n + k) = (V C n l0 S a && V C n l0 S b)) ∧
      (∀ S, C.gates[k].op = GateOp.or → V C n l0 S (n + n + k) = (V C n l0 S a || V C n l0 S b)) := by
  obtain ⟨hao, hrb, h2⟩ := hC
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hlt : ∀ i ∈ [a, b], i < n + n + k := by
    intro i hi
    have := hrb k hk i
    rw [hG, hin] at this
    exact this hi
  have gen : ∀ S, V C n l0 S (n + n + k) = C.gates[k].op.eval
      [V C n l0 S a, V C n l0 S b] := by
    intro S
    have g1 := gate_val C.gates (PEqualNP.GenericRejection.incidenceInput S {l0}) k hk
    rw [inc_len, hin] at g1
    show (wf C.gates (PEqualNP.GenericRejection.incidenceInput S {l0})).getD (n + n + k) false = _
    rw [g1]
    simp only [List.map_cons, List.map_nil, V]
    rw [wire_take C.gates _ k a (by rw [inc_len]; exact hlt a (by simp)) (le_of_lt hk),
      wire_take C.gates _ k b (by rw [inc_len]; exact hlt b (by simp)) (le_of_lt hk)]
  refine ⟨a, b, hlt a (by simp), hlt b (by simp), hao _ hmem, hG, fun S hop => ?_, fun S hop => ?_⟩
  · rw [gen, hop]; simp [GateOp.eval]
  · rw [gen, hop]; simp [GateOp.eval]

theorem merge_card {n : ℕ} (A : Finset (Fin n)) (lab : Fin n → Fin n) (p0 q0 : Fin n) :
    (A.image lab).card ≤
      (A.image (fun x => if lab x = lab q0 then lab p0 else lab x)).card + 1 := by
  classical
  have hsub : (A.image lab).erase (lab q0) ⊆
      A.image (fun x => if lab x = lab q0 then lab p0 else lab x) := by
    intro c hc
    obtain ⟨hne, hc⟩ := Finset.mem_erase.1 hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_image.2 ⟨x, hx, by simp [hne]⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := A.image lab) (a := lab q0)
  omega

end PEqualNP.Outside.L_meta_3256

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3256

theorem PEqualNP.Outside.L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C A l0 hC hout htrue hfalse
  classical
  have hC0 := hC
  obtain ⟨hao, hrb, h2⟩ := hC
  have hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨hao g hg, le_of_eq (h2 g hg)⟩
  let O : Finset ℕ := (Finset.range C.gates.length).filter (fun j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      V C n l0 Aᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ V C n l0 {p} (n + n + j) = true ∧ V C n l0 {q} (n + n + j) = true)
  have sound_sub : ∀ w (p : Fin n), V C n l0 Aᶜ w = false → V C n l0 {p} w = true → p ∈ A := by
    intro w p hs hp
    by_contra hpA
    have := V_mono C n l0 hleg {p} Aᶜ (by simpa using hpA) w hp
    rw [hs] at this
    cases this
  have key : ∀ j ≤ C.gates.length, ∃ lab : Fin n → Fin n,
      (∀ w < n + n + j, V C n l0 Aᶜ w = false → ∀ p q : Fin n,
        V C n l0 {p} w = true → V C n l0 {q} w = true → lab p = lab q) ∧
      A.card ≤ (A.image lab).card + (O.filter (· < j)).card := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨id, ?_, by simp⟩
      intro w hw hs p q hp hq
      by_cases hwn : w < n
      · have e1 := V_point C n l0 {p} ⟨w, hwn⟩
        have e2 := V_point C n l0 {q} ⟨w, hwn⟩
        simp only at e1 e2
        rw [e1] at hp
        rw [e2] at hq
        simp only [Finset.mem_singleton, decide_eq_true_eq] at hp hq
        simp [← hp, ← hq]
      · have e := V_line C n l0 {p} Aᶜ w (by omega) (by omega)
        rw [e, hs] at hp
        cases hp
    | succ j ih =>
      intro hj
      obtain ⟨lab, hinv, hcnt⟩ := ih (by omega)
      have hk : j < C.gates.length := by omega
      obtain ⟨a, b, ha, hb, hop, hG, hval⟩ := gate2 C n l0 hC0 j hk
      -- the new wire: either labels already agree, or it is a merging OR gate
      have newgate : ∀ p q : Fin n, V C n l0 Aᶜ (n + n + j) = false →
          V C n l0 {p} (n + n + j) = true → V C n l0 {q} (n + n + j) = true →
          lab p = lab q ∨ (j ∈ O ∧ ((V C n l0 {p} a = true ∧ V C n l0 {q} b = true) ∨
            (V C n l0 {q} a = true ∧ V C n l0 {p} b = true))) := by
        intro p q hs hp hq
        by_cases hand : C.gates[j].op = GateOp.and
        · rw [hval.1 _ hand] at hs
          rw [hval.1 _ hand] at hp
          rw [hval.1 _ hand] at hq
          simp only [Bool.and_eq_true, Bool.and_eq_false_iff] at hs hp hq
          left
          rcases hs with hs | hs
          · exact hinv a ha hs p q hp.1 hq.1
          · exact hinv b hb hs p q hp.2 hq.2
        · have hor : C.gates[j].op = GateOp.or := hop.resolve_left hand
          rw [hval.2 _ hor] at hs
          rw [hval.2 _ hor] at hp
          rw [hval.2 _ hor] at hq
          simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at hs hp hq
          by_cases hpq : p = q
          · left; rw [hpq]
          have hjO : j ∈ O := by
            refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, by rw [hG]; exact hor, ?_, p, q, hpq, ?_, ?_⟩
            · rw [hval.2 _ hor, Bool.or_eq_false_iff]; exact hs
            · rw [hval.2 _ hor, Bool.or_eq_true]; exact hp
            · rw [hval.2 _ hor, Bool.or_eq_true]; exact hq
          rcases hp with hp | hp <;> rcases hq with hq | hq
          · left; exact hinv a ha hs.1 p q hp hq
          · right; exact ⟨hjO, Or.inl ⟨hp, hq⟩⟩
          · right; exact ⟨hjO, Or.inr ⟨hq, hp⟩⟩
          · left; exact hinv b hb hs.2 p q hp hq
      have filt_le : (O.filter (· < j)).card ≤ (O.filter (· < j + 1)).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by omega⟩
      by_cases hmerge : j ∈ O ∧ (∃ p0, V C n l0 {p0} a = true) ∧ (∃ q0, V C n l0 {q0} b = true)
      · obtain ⟨hjO, ⟨p0, hp0⟩, ⟨q0, hq0⟩⟩ := hmerge
        have hsj : V C n l0 Aᶜ (n + n + j) = false := (Finset.mem_filter.1 hjO).2.2.1
        have hor : C.gates[j].op = GateOp.or := by
          have := (Finset.mem_filter.1 hjO).2.1
          rwa [hG] at this
        have hsab : V C n l0 Aᶜ a = false ∧ V C n l0 Aᶜ b = false := by
          rw [hval.2 _ hor] at hsj
          simpa using hsj
        refine ⟨fun x => if lab x = lab q0 then lab p0 else lab x, ?_, ?_⟩
        · intro w hw hs p q hp hq
          rcases (show w < n + n + j ∨ w = n + n + j by omega) with hw' | rfl
          · have := hinv w hw' hs p q hp hq
            simp only [this]
          · rcases newgate p q hs hp hq with h | ⟨_, h⟩
            · simp only [h]
            · rcases h with ⟨hpa, hqb⟩ | ⟨hqa, hpb⟩
              · have e1 := hinv a ha hsab.1 p p0 hpa hp0
                have e2 := hinv b hb hsab.2 q q0 hqb hq0
                simp only [e1, e2]
                split_ifs <;> rfl
              · have e1 := hinv a ha hsab.1 q p0 hqa hp0
                have e2 := hinv b hb hsab.2 p q0 hpb hq0
                simp only [e1, e2]
                split_ifs <;> rfl
        · have hins : O.filter (· < j + 1) = insert j (O.filter (· < j)) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hx, hxj⟩
              by_cases hxe : x = j
              · left; exact hxe
              · right; exact ⟨hx, by omega⟩
            · rintro (rfl | ⟨hx, hxj⟩)
              · exact ⟨hjO, by omega⟩
              · exact ⟨hx, by omega⟩
          have hnot : j ∉ O.filter (· < j) := by simp
          rw [hins, Finset.card_insert_of_notMem hnot]
          have := merge_card A lab p0 q0
          omega
      · refine ⟨lab, ?_, le_trans hcnt (by omega)⟩
        intro w hw hs p q hp hq
        rcases (show w < n + n + j ∨ w = n + n + j by omega) with hw' | rfl
        · exact hinv w hw' hs p q hp hq
        · rcases newgate p q hs hp hq with h | ⟨hjO, h⟩
          · exact h
          · exfalso
            apply hmerge
            rcases h with ⟨hpa, hqb⟩ | ⟨hqa, hpb⟩
            · exact ⟨hjO, ⟨p, hpa⟩, ⟨q, hqb⟩⟩
            · exact ⟨hjO, ⟨q, hqa⟩, ⟨p, hpb⟩⟩
  obtain ⟨lab, hinv, hcnt⟩ := key C.gates.length le_rfl
  have hout' : C.output < n + n + C.gates.length := hout
  have hsout : V C n l0 Aᶜ C.output = false := hfalse
  have hone : (A.image lab).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro c hc d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hd
    exact hinv C.output hout' hsout p q (htrue p hp) (htrue q hq)
  have hsubO : O.filter (· < C.gates.length) ⊆ O := Finset.filter_subset _ _
  have hcardO := Finset.card_le_card hsubO
  refine ⟨O, by omega, fun x hx => ?_⟩
  obtain ⟨hxr, hop, hs, p, q, hpq, hp, hq⟩ := Finset.mem_filter.1 hx
  refine ⟨Finset.mem_range.1 hxr, hop, ?_⟩
  dsimp only
  exact ⟨hs, ⟨p, q, hpq, hp, hq⟩, fun r hr => sound_sub _ r hs hr⟩
