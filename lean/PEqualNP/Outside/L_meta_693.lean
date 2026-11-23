import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_693

open PEqualNP.CircuitLowerBounds

-- Wire evaluation helpers adapted from the checked L-meta-640 proof.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma runWires_nil (x : List Bool) : runWires [] x = x := rfl

lemma runWires_append (gs1 gs2 : List Gate) (x : List Bool) :
    runWires (gs1 ++ gs2) x = runWires gs2 (runWires gs1 x) := by
  simp [runWires, List.foldl_append]

lemma runWires_singleton (g : Gate) (x : List Bool) :
    runWires [g] x = stepWire x g := rfl

lemma runWires_length (gs : List Gate) (x : List Bool) :
    (runWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [runWires]
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [stepWire]
    omega

lemma getD_append_left_lt (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma runWires_getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (runWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (runWires gs (stepWire x g)).getD i false = x.getD i false
    have hlt : i < (stepWire x g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire x g) hlt]
    exact getD_append_left_lt x _ i hi

lemma wires_eq_runWires (C : Circuit) (x : List Bool) :
    C.wires x = runWires C.gates x := rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact runWires_length C.gates x

lemma wires_getD_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  rw [wires_eq_runWires, runWires_getD_prefix]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  · simp

lemma wires_getD_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval
        ((C.gates[k]).inputs.map fun a =>
          if a < x.length + k then (C.wires x).getD a false else false) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  let pref := runWires (C.gates.take k) x
  have hpref_len : pref.length = x.length + k := by
    change (runWires (C.gates.take k) x).length = x.length + k
    rw [runWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hwires : C.wires x = runWires (C.gates.drop (k + 1)) (stepWire pref C.gates[k]) := by
    rw [wires_eq_runWires]
    conv_lhs => rw [hsplit]
    rw [runWires_append, runWires_append, runWires_singleton]
  have hstep_len : x.length + k < (stepWire pref C.gates[k]).length := by
    simp [stepWire, hpref_len]
  rw [hwires, runWires_getD_prefix _ _ _ hstep_len]
  have hstep_eq : (stepWire pref C.gates[k]).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => pref.getD a false) := by
    rw [← hpref_len]
    exact getD_append_singleton_eq pref _
  rw [hstep_eq]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < x.length + k
  · rw [if_pos ha]
    have ha' : a < (stepWire pref C.gates[k]).length := by omega
    rw [runWires_getD_prefix _ _ _ ha']
    have ha'' : a < pref.length := by omega
    exact (getD_append_left_lt pref _ a ha'').symm
  · rw [if_neg ha]
    exact getD_of_le pref a (by omega)

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) :=
  (C.wires (List.ofFn x)).getD w false

private theorem op_transfer {g : Gate} (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : ℕ → Bool} (hab : ∀ w ∈ g.inputs, a w = true → b w = true)
    (h : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
  rcases hg with he | he
  · simp [he, GateOp.eval] at h ⊢
    exact fun w hw => hab w hw (h w hw)
  · simp [he, GateOp.eval] at h ⊢
    obtain ⟨w, hw, ht⟩ := h
    exact ⟨w, hw, hab w hw ht⟩

private theorem gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.size) :
    value C x (n+j) = (C.gates[j]'hj).op.eval
      ((C.gates[j]'hj).inputs.map fun w => if w < n+j then value C x w else false) := by
  simpa [value] using wires_getD_gate C (List.ofFn x) j hj

private theorem value_mono {n : ℕ} (C : Circuit)
    (ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · unfold value
      rw [wires_getD_input C x ⟨w, hw⟩, wires_getD_input C y ⟨w, hw⟩]
      exact hxy ⟨w, hw⟩
    · let j := w - n
      have eqw : w = n+j := by dsimp [j]; omega
      by_cases hj : j < C.size
      · rw [eqw, gate_value C x j hj, gate_value C y j hj]
        apply op_transfer (ops _ (List.getElem_mem _))
        intro z _ hz
        split at hz
        next h => simpa [h] using ih z (by omega) hz
        next => contradiction
      · have hlen : (C.wires (List.ofFn x)).length ≤ w := by
          rw [wires_length, List.length_ofFn]; omega
        unfold value
        rw [getD_of_le _ _ hlen]
        simp

end PEqualNP.Outside.L_meta_693

open PEqualNP.Outside.L_meta_693 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_693 : ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card := by
  classical
  intro n k r S C Q ψ gates promise hr bounded parent label outside root
  let ins (j : ℕ) := ((C.gates[j]?).map (fun g => g.inputs.toFinset)).getD ∅
  have ins_eq {j : ℕ} (hj : j ∈ Q) :
      ins j = (C.gates[j]'(bounded j hj)).inputs.toFinset := by
    simp [ins, List.getElem?_eq_getElem (bounded j hj)]
  let U := Q.biUnion ins
  let inner := (Q.erase r).image (fun j => n+j)
  have inside : inner ⊆ U := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hne,hq⟩ := Finset.mem_erase.mp hj
    obtain ⟨a, ha, _, g, hg, hi⟩ := parent j hq hne
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    simpa [ins, hg] using hi
  have hu : U.card ≤ Q.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro j hj
    rw [ins_eq hj]
    exact (List.toFinset_card_le _).trans (gates _ (List.getElem_mem _)).2.le
  have hi : inner.card = Q.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
      Finset.card_erase_of_mem hr]
  let B := (U \ inner).filter (fun w => (∀ j ∈ Q, w ≠ n+j) ∧ ψ w = true)
  have hB : B.card ≤ Q.card + 1 := by
    have h₁ := Finset.card_le_card (Finset.filter_subset (fun w => (∀ j ∈ Q, w ≠ n+j) ∧ ψ w = true) (U \ inner))
    have h₂ := Finset.card_sdiff_add_card_eq_card inside
    change B.card ≤ (U \ inner).card at h₁
    omega
  have witness : ∀ w ∈ B, ∃ p : Fin n, p ∉ S ∧ value C (fun q => decide (q=p)) w = true := by
    intro w hw
    obtain ⟨_, hn, ht⟩ := Finset.mem_filter.mp hw
    have neg := outside w hn ht
    by_contra! h
    apply neg
    intro p hp
    by_contra hps
    have := h p hps
    have htrue := (Finset.mem_filter.mp hp).2
    simp_all [value]
  choose pick pickSpec using witness
  let T := B.attach.image (fun w => pick w.val w.property)
  let x : Fin n → Bool := fun q => decide (q ∈ T)
  have avoid (q) (hq : q ∈ S) : x q = false := by
    apply decide_eq_false
    intro ht
    obtain ⟨w, _, he⟩ := Finset.mem_image.mp ht
    exact (pickSpec w.val w.property).1 (he.symm ▸ hq)
  have boundary (w) (hw : w ∈ B) : value C x w = true := by
    apply value_mono C (fun g hg => (gates g hg).1) _ x _ w (pickSpec w hw).2
    intro i he
    have heq : i = pick w hw := of_decide_eq_true he
    subst i
    exact decide_eq_true (Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩)
  have transfer (j : ℕ) (hj : j ∈ Q) (ht : ψ (n+j) = true) : value C x (n+j) = true := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      have len := bounded j hj
      let g := C.gates[j]'len
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem len
      rw [label j hj g hg] at ht
      rw [gate_value C x j len]
      apply op_transfer (g := g) (gates g (List.getElem_mem _)).1 _ ht
      intro w hw htrue
      by_cases hlt : w < n+j
      · simp only [if_pos hlt] at htrue ⊢
        by_cases hin : ∃ i ∈ Q, w = n+i
        · obtain ⟨i, hi, rfl⟩ := hin
          exact ih i (by omega) hi htrue
        · have hn : ∀ i ∈ Q, w ≠ n+i := by simpa using hin
          apply boundary
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩, ?_⟩, hn, htrue⟩
          · simpa [ins, hg] using hw
          · intro hw'
            obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hw'
            exact hn i (Finset.mem_erase.mp hi).2 he.symm
      · simp [hlt] at htrue
  have cardT : T.card ≤ B.card := by
    exact Finset.card_image_le.trans Finset.card_attach.le
  by_contra! hsmall
  have hs : (Finset.univ.filter (fun q => x q = true)).card ≤ k := by
    have heq : Finset.univ.filter (fun q => x q = true) = T := by ext q; simp [x]
    rw [heq]
    omega
  have h0 := promise x hs avoid
  have h1 := transfer r hr root
  change value C x (n+r) = false at h0
  simp_all
