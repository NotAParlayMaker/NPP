import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds

private def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

private lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

private lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

private lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

private lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

private lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

private lemma mono2 (gs : List Gate)
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

private lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

private lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this


private lemma expandBound {A : Type*} [DecidableEq A]
    (S : Finset A) (support : ℕ → Finset A) (bad : ℕ → Prop)
    (limit : ℕ) (good : ℕ → Prop)
    (base : ∀ w < limit, (support w).card ≤ 1)
    (desc : ∀ w, limit ≤ w → bad w →
      ∃ V : Finset ℕ, (∀ v ∈ V, v < w ∧ bad v) ∧
        (∀ p ∈ support w, ∃ v ∈ V, p ∈ support v) ∧
        V.card ≤ 2 ∧ (1 < V.card → good w)) :
    ∀ bound (F : Finset ℕ), (∀ w ∈ F, w < bound ∧ bad w) →
      (∀ p ∈ S, ∃ w ∈ F, p ∈ support w) →
      ∃ Q : Finset ℕ, (∀ w ∈ Q, w < bound ∧ good w) ∧ S.card ≤ Q.card + F.card := by
  classical
  intro bound
  induction bound with
  | zero =>
    intro F hf hc
    have hempty : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro p hp
      obtain ⟨w, hw, _⟩ := hc p hp
      exact (Nat.not_lt_zero w) (hf w hw).1)
    exact ⟨∅, by simp, by simp [hempty]⟩
  | succ k ih =>
    intro F hf hc
    by_cases small : k + 1 ≤ limit
    · let U := F.biUnion support
      have hs : S ⊆ U := fun p hp => Finset.mem_biUnion.mpr (hc p hp)
      have hU : U.card ≤ F.card * 1 :=
        Finset.card_biUnion_le_card_mul F support 1
          (fun w hw => base w (by have := (hf w hw).1; omega))
      refine ⟨∅, by simp, ?_⟩
      have := Finset.card_le_card hs
      simp at hU ⊢
      omega
    · by_cases hk : k ∈ F
      · obtain ⟨V, hv, hcov, hsize, hgood⟩ := desc k (by omega) (hf k hk).2
        let T := F.erase k ∪ V
        have ht : ∀ w ∈ T, w < k ∧ bad w := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · have hn := Finset.ne_of_mem_erase hw
            have hh := hf w (Finset.mem_of_mem_erase hw)
            exact ⟨by omega, hh.2⟩
          · exact hv w hw
        have hc' : ∀ p ∈ S, ∃ w ∈ T, p ∈ support w := by
          intro p hp
          obtain ⟨w, hw, hwp⟩ := hc p hp
          by_cases eq : w = k
          · subst w
            obtain ⟨v, hvm, hvp⟩ := hcov p hwp
            exact ⟨v, Finset.mem_union_right _ hvm, hvp⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq, hw⟩), hwp⟩
        obtain ⟨Q, hQ, hbound⟩ := ih T ht hc'
        have hT : T.card ≤ F.card - 1 + V.card := by
          unfold T
          simpa only [Finset.card_erase_of_mem hk] using Finset.card_union_le (F.erase k) V
        have hpos : 0 < F.card := Finset.card_pos.mpr ⟨k, hk⟩
        by_cases htwo : 1 < V.card
        · have kn : k ∉ Q := fun h => (Nat.lt_irrefl k) (hQ k h).1
          refine ⟨insert k Q, ?_, ?_⟩
          · intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact ⟨by omega, hgood htwo⟩
            · exact ⟨Nat.lt_succ_of_lt (hQ w hw).1, (hQ w hw).2⟩
          · rw [Finset.card_insert_of_notMem kn]
            omega
        · exact ⟨Q, fun w hw => ⟨Nat.lt_succ_of_lt (hQ w hw).1, (hQ w hw).2⟩, by omega⟩
      · have hf' : ∀ w ∈ F, w < k ∧ bad w := by
          intro w hw
          have h := hf w hw
          have hn : w ≠ k := fun e => hk (e ▸ hw)
          exact ⟨by omega, h.2⟩
        obtain ⟨Q, hQ, hbound⟩ := ih F hf' hc
        exact ⟨Q, fun w hw => ⟨Nat.lt_succ_of_lt (hQ w hw).1, (hQ w hw).2⟩, hbound⟩


theorem L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  classical
  intro n C S line hC hout hp hn
  let value (X : Finset (Fin n)) (w : ℕ) :=
    (wf C.gates (PEqualNP.GenericRejection.incidenceInput X {line})).getD w false
  let supp (w : ℕ) := Finset.univ.filter fun p : Fin n => value {p} w = true
  let bad (w : ℕ) := value Sᶜ w = false
  let good (w : ℕ) := n + n ≤ w ∧ w < n + n + C.size ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - (n+n))).op = GateOp.or ∧
      bad w ∧ 1 < (supp w).card
  have len (X : Finset (Fin n)) :
      (PEqualNP.GenericRejection.incidenceInput X ({line} : Finset (Fin n))).length = n+n := by
    simp [PEqualNP.GenericRejection.incidenceInput]
  have left (X : Finset (Fin n)) (w : ℕ) (hw : w < n) :
      value X w = decide ((⟨w,hw⟩ : Fin n) ∈ X) := by
    unfold value
    rw [wf_keep _ _ _ (by rw [len]; omega)]
    simp [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show w < (List.ofFn fun p : Fin n => decide (p ∈ X)).length by simpa),
      hw]
  have right (X : Finset (Fin n)) (w : ℕ) (hw : n ≤ w) (h' : w < n+n) :
      value X w = decide ((⟨w-n, by omega⟩ : Fin n) ∈ ({line} : Finset (Fin n))) := by
    unfold value
    rw [wf_keep _ _ _ (by rw [len]; omega)]
    simp [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (show (List.ofFn fun p : Fin n => decide (p ∈ X)).length ≤ w by simpa),
      show w-n < n by omega]
  have mono (X Y : Finset (Fin n)) (hXY : X ⊆ Y) (w : ℕ) :
      value X w = true → value Y w = true := by
    apply mono2 C.gates (fun g hg => ⟨hC.1 g hg, (hC.2.2 g hg).le⟩)
    · rw [len, len]
    · intro i
      by_cases hi : i < n
      · rw [← wf_keep C.gates (PEqualNP.GenericRejection.incidenceInput X {line}) i (by rw [len]; omega),
            ← wf_keep C.gates (PEqualNP.GenericRejection.incidenceInput Y {line}) i (by rw [len]; omega)]
        change value X i = true → value Y i = true
        rw [left X i hi, left Y i hi]
        simpa only [decide_eq_true_eq] using (fun h => hXY h)
      · by_cases hj : i < n+n
        · rw [← wf_keep C.gates (PEqualNP.GenericRejection.incidenceInput X {line}) i (by rw [len]; omega),
              ← wf_keep C.gates (PEqualNP.GenericRejection.incidenceInput Y {line}) i (by rw [len]; omega)]
          change value X i = true → value Y i = true
          rw [right X i (by omega) hj, right Y i (by omega) hj]
          exact id
        · rw [List.getD_eq_default _ _ (by rw [len]; omega)]
          simp
  have suppS (w : ℕ) (hw : bad w) (p : Fin n) (hm : p ∈ supp w) : p ∈ S := by
    by_contra h
    have hsub : ({p} : Finset (Fin n)) ⊆ Sᶜ := by simpa using h
    have ht := mono {p} Sᶜ hsub w (Finset.mem_filter.mp hm).2
    change value Sᶜ w = false at hw
    simp [hw] at ht
  have base : ∀ w < n+n, (supp w).card ≤ 1 ∨ ¬ bad w := by
    intro w hw
    by_cases h : w < n
    · left
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have h₁ := (Finset.mem_filter.mp ha).2
      have h₂ := (Finset.mem_filter.mp hb).2
      rw [left _ _ h] at h₁ h₂
      have ea : (⟨w,h⟩ : Fin n) = a := by simpa using h₁
      have eb : (⟨w,h⟩ : Fin n) = b := by simpa using h₂
      exact ea.symm.trans eb
    · by_cases hb : bad w
      · left
        have hzero : supp w = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
          intro a ha
          have ha' := (Finset.mem_filter.mp ha).2
          change value Sᶜ w = false at hb
          rw [right _ _ (by omega) hw] at ha' hb
          rw [hb] at ha'
          contradiction)
        simp [hzero]
      · exact Or.inr hb
  let supp' (w : ℕ) := if bad w then supp w else ∅
  have b' : ∀ w < n+n, (supp' w).card ≤ 1 := by
    intro w hw
    by_cases hb : bad w
    · simpa [supp', hb] using (base w hw).resolve_right (not_not.mpr hb)
    · simp [supp', hb]
  have desc : ∀ w, n+n ≤ w → (w < n+n+C.size ∧ bad w) →
      ∃ V : Finset ℕ, (∀ v ∈ V, v < w ∧ (v < n+n+C.size ∧ bad v)) ∧
        (∀ p ∈ supp' w, ∃ v ∈ V, p ∈ supp' v) ∧
        V.card ≤ 2 ∧ (1 < V.card → good w) := by
    intro w hw ⟨hvalid,hbad⟩
    let k := w-(n+n)
    have eq : w = n+n+k := by dsimp [k]; omega
    have hk : k < C.gates.length := by change k < C.size; omega
    have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hk]
    have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
    obtain ⟨a,b,hin⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
    have hlt : ∀ i ∈ [a,b], i < w := by
      intro i hi
      have h := hC.2.1 k hk i
      rw [hG, hin] at h
      rw [eq]
      exact h hi
    have ha := hlt a (by simp)
    have hb := hlt b (by simp)
    have gv (X : Finset (Fin n)) :
        value X w = C.gates[k].op.eval [value X a, value X b] := by
      unfold value
      rw [eq]
      have h := gate_val C.gates (PEqualNP.GenericRejection.incidenceInput X {line}) k hk
      rw [len, hin] at h
      rw [h]
      simp only [List.map_cons, List.map_nil]
      rw [← wire_take C.gates _ k a (by rw [len]; omega) (le_of_lt hk),
          ← wire_take C.gates _ k b (by rw [len]; omega) (le_of_lt hk)]
    have single (v : ℕ) (hv : v < w) (hvbad : bad v)
        (hvcover : ∀ p ∈ supp w, p ∈ supp v) :
        ∃ V : Finset ℕ, (∀ u ∈ V, u < w ∧ (u < n+n+C.size ∧ bad u)) ∧
          (∀ p ∈ supp' w, ∃ u ∈ V, p ∈ supp' u) ∧
          V.card ≤ 2 ∧ (1 < V.card → good w) := by
      refine ⟨{v}, ?_, ?_, by simp, by simp⟩
      · simpa using And.intro hv (And.intro (show v < n+n+C.size by omega) hvbad)
      · intro p hp'
        exact ⟨v, by simp, by simpa [supp', hvbad] using hvcover p (by simpa [supp', hbad] using hp')⟩
    rcases hC.1 _ hmem with hop | hop
    · have he (X : Finset (Fin n)) : value X w = (value X a && value X b) := by
        rw [gv, hop]; simp [GateOp.eval]
      have neg := hbad
      change value Sᶜ w = false at neg
      rw [he, Bool.and_eq_false_iff] at neg
      rcases neg with neg | neg
      · apply single a ha neg
        intro p h
        have ht := (Finset.mem_filter.mp h).2
        rw [he, Bool.and_eq_true] at ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.1⟩
      · apply single b hb neg
        intro p h
        have ht := (Finset.mem_filter.mp h).2
        rw [he, Bool.and_eq_true] at ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.2⟩
    · have he (X : Finset (Fin n)) : value X w = (value X a || value X b) := by
        rw [gv, hop]; simp [GateOp.eval]
      have neg := hbad
      change value Sᶜ w = false at neg
      rw [he, Bool.or_eq_false_iff] at neg
      have hna : bad a := neg.1
      have hnb : bad b := neg.2
      have cover (p : Fin n) (h : p ∈ supp w) : p ∈ supp a ∨ p ∈ supp b := by
        have ht := (Finset.mem_filter.mp h).2
        rw [he, Bool.or_eq_true] at ht
        exact ht.imp (fun t => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t⟩)
                     (fun t => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t⟩)
      by_cases hm : 1 < (supp w).card
      · refine ⟨{a,b}, ?_, ?_, ?_, ?_⟩
        · intro v hv
          simp at hv
          rcases hv with rfl | rfl
          · exact ⟨ha, by omega, hna⟩
          · exact ⟨hb, by omega, hnb⟩
        · intro p h
          rcases cover p (by simpa [supp', hbad] using h) with t | t
          · exact ⟨a, by simp, by simpa [supp', hna] using t⟩
          · exact ⟨b, by simp, by simpa [supp', hnb] using t⟩
        · exact (Finset.card_insert_le _ _).trans (by simp)
        · intro _
          refine ⟨hw,hvalid,?_,hbad,hm⟩
          have hkEq : w-(n+n) = k := rfl
          rw [hkEq,hG,hop]
      · by_cases hs : (supp w).Nonempty
        · obtain ⟨p,hp⟩ := hs
          have only := Finset.card_le_one.mp (by omega : (supp w).card ≤ 1)
          rcases cover p hp with t | t
          · exact single a ha hna (fun p' hp' => (only p' hp' p hp).symm ▸ t)
          · exact single b hb hnb (fun p' hp' => (only p' hp' p hp).symm ▸ t)
        · refine ⟨∅, by simp, ?_, by simp, by simp⟩
          intro p h
          exact False.elim (hs ⟨p, by simpa [supp',hbad] using h⟩)
  have hroot : bad C.output := hn
  have hrootcov : ∀ p ∈ S, ∃ w ∈ ({C.output} : Finset ℕ), p ∈ supp' w := by
    intro p h
    refine ⟨C.output, by simp, ?_⟩
    simp only [supp', hroot, ite_eq_left, supp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp p h
  obtain ⟨Q,hQ,hcount⟩ := expandBound S supp' (fun w => w < n+n+C.size ∧ bad w)
    (n+n) good b' desc (n+n+C.size) {C.output}
    (by intro w hw; have eq := Finset.mem_singleton.mp hw; subst w; exact ⟨hout,hout,hroot⟩) hrootcov
  refine ⟨Q.image (fun w => w-(n+n)), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · simpa using hcount
    · intro a ha b hb heq
      have h₁ := (hQ a ha).2.1
      have h₂ := (hQ b hb).2.1
      change a-(n+n) = b-(n+n) at heq
      omega
  · intro j hj
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hwl,hwh,hop,hneg,hm⟩ := (hQ w hw).2
    have eq : n+n+(w-(n+n)) = w := by omega
    refine ⟨by omega,hop,?_,?_,?_⟩
    · rw [eq]
      exact hneg
    · rw [eq]
      obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp hm
      exact ⟨a,b,hab,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩
    · intro p h
      rw [eq] at h
      exact suppS w hneg p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

end PEqualNP.Outside
