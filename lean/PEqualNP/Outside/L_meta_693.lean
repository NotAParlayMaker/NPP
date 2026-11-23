import Mathlib.Tactic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_693_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [hstep, ht]
    simp

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma gateOp_eval_map_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    (inputs : List ℕ) (f1 f2 : ℕ → Bool)
    (hle : ∀ w ∈ inputs, f1 w = true → f2 w = true) :
    op.eval (inputs.map f1) = true → op.eval (inputs.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
    intro h b hb
    obtain ⟨w, hw, rfl⟩ := hb
    exact hle w hw (h (f1 w) ⟨w, hw, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
    rintro ⟨b, ⟨w, hw, rfl⟩, hfw⟩
    exact ⟨f2 w, ⟨w, hw, rfl⟩, hle w hw hfw⟩

lemma wiresFrom_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
    (∀ i, w1.getD i false = true → w2.getD i false = true) →
    (∀ i, (wiresFrom gs w1).getD i false = true → (wiresFrom gs w2).getD i false = true) := by
  induction gs with
  | nil => intro w1 w2 _ hle i hi; exact hle i hi
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hgs g' (by simp [hg'])
    let v1 := g.op.eval (g.inputs.map fun i => w1.getD i false)
    let v2 := g.op.eval (g.inputs.map fun i => w2.getD i false)
    apply ih hgs' (w1 ++ [v1]) (w2 ++ [v2]) (by simp [hlen])
    intro i hi
    by_cases hlt : i < w1.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle i hi
    · by_cases heq : i = w1.length
      · subst heq
        have hv1 : (w1 ++ [v1]).getD w1.length false = v1 := by simp
        have hv2 : (w2 ++ [v2]).getD w1.length false = v2 := by rw [hlen]; simp
        rw [hv1] at hi
        rw [hv2]
        exact gateOp_eval_map_mono hg g.inputs _ _ (fun w _ hw => hle w hw) hi
      · have hdef : (w1 ++ [v1]).getD i false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        rw [hdef] at hi
        exact False.elim (Bool.false_ne_true hi)

lemma getD_wiresFrom_gate (gs : List Gate) :
    ∀ (w : List Bool) (j : ℕ) (g : Gate),
    gs[j]? = some g →
    (wiresFrom gs w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (wiresFrom gs w).getD i false else false) := by
  induction gs with
  | nil => intro w j g hj; simp at hj
  | cons g0 gs ih =>
    intro w j g hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      rcases hj with rfl
      have hstep : wiresFrom (g0 :: gs) w =
          wiresFrom gs (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]) := by
        simp [wiresFrom]
      have hw1 : w.length < (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).length := by
        simp
      rw [hstep, Nat.add_zero, getD_wiresFrom_lt gs _ w.length hw1]
      have hv : (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) := by simp
      rw [hv]
      congr 1
      apply List.map_inj_left.2
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, getD_wiresFrom_lt gs _ i (by omega), List.getD_append _ _ _ _ hi]
      · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have hstep : wiresFrom (g0 :: gs) w =
          wiresFrom gs (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]) := by
        simp [wiresFrom]
      have hlen : (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by
        simp
      rw [hstep]
      have hadd : w.length + (j + 1) =
          (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).length + j := by omega
      simpa only [hadd] using ih _ j g hj

def slotVal (C : Circuit) (p : ℕ × Fin 2) : ℕ :=
  match C.gates[p.1]? with
  | some g => g.inputs.getD p.2.1 0
  | none => 0

lemma slotVal_exists_of_mem {C : Circuit} {j w : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hlen : g.inputs.length = 2) (hw : w ∈ g.inputs) :
    ∃ s : Fin 2, slotVal C (j, s) = w := by
  rcases g with ⟨op, inputs⟩
  dsimp at hlen hw
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | xs⟩⟩ <;> simp at hlen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · refine ⟨0, ?_⟩
    simp [slotVal, hg]
  · refine ⟨1, ?_⟩
    simp [slotVal, hg]

end PEqualNP.Outside.L_meta_693_aux

theorem PEqualNP.Outside.L_meta_693 : ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card := by
  classical
  intro n k r S C Q ψ hgates hpromise hrQ hQsize hparent hψ houtside hroot
  let AllSlots : Finset (ℕ × Fin 2) := Q ×ˢ (Finset.univ : Finset (Fin 2))
  let InternalSlots : Finset (ℕ × Fin 2) :=
    AllSlots.filter (fun p => ∃ j0 ∈ Q.erase r,
      PEqualNP.Outside.L_meta_693_aux.slotVal C p = n + j0)
  let OutsideSlots : Finset (ℕ × Fin 2) :=
    AllSlots.filter (fun p => ∀ j ∈ Q,
      PEqualNP.Outside.L_meta_693_aux.slotVal C p ≠ n + j)
  let FSlots : Finset (ℕ × Fin 2) :=
    AllSlots.filter (fun p => ψ (PEqualNP.Outside.L_meta_693_aux.slotVal C p) = true ∧
      ∀ j ∈ Q, PEqualNP.Outside.L_meta_693_aux.slotVal C p ≠ n + j)
  let F : Finset ℕ := FSlots.image (PEqualNP.Outside.L_meta_693_aux.slotVal C)
  have hdisj : Disjoint InternalSlots OutsideSlots := by
    rw [Finset.disjoint_left]
    intro p hpI hpO
    simp only [InternalSlots, OutsideSlots, Finset.mem_filter] at hpI hpO
    obtain ⟨j0, hj0, hval⟩ := hpI.2
    exact hpO.2 j0 (Finset.mem_of_mem_erase hj0) hval
  have hsub : InternalSlots ∪ OutsideSlots ⊆ AllSlots := by
    intro p hp
    rcases Finset.mem_union.1 hp with hpI | hpO
    · exact (Finset.mem_filter.1 hpI).1
    · exact (Finset.mem_filter.1 hpO).1
  have hcardAll : AllSlots.card = 2 * Q.card := by
    simp [AllSlots, Finset.card_product, mul_comm]
  have hcardSum : InternalSlots.card + OutsideSlots.card ≤ 2 * Q.card := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hcardAll]
    exact Finset.card_le_card hsub
  have hsurj : Q.erase r ⊆
      InternalSlots.image (fun p => PEqualNP.Outside.L_meta_693_aux.slotVal C p - n) := by
    intro j0 hj0
    obtain ⟨hne, hj0Q⟩ := Finset.mem_erase.1 hj0
    obtain ⟨j', hj'Q, _, g, hg, hmem⟩ := hparent j0 hj0Q hne
    have hgj'_in : g ∈ C.gates := List.mem_of_getElem? hg
    have hlen : g.inputs.length = 2 := (hgates g hgj'_in).2
    obtain ⟨s, hs⟩ := PEqualNP.Outside.L_meta_693_aux.slotVal_exists_of_mem hg hlen hmem
    refine Finset.mem_image.2 ⟨(j', s), ?_, by omega⟩
    simp only [InternalSlots, AllSlots, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      and_true]
    exact ⟨hj'Q, j0, hj0, hs⟩
  have hcardInt : Q.card - 1 ≤ InternalSlots.card := by
    calc
      Q.card - 1 = (Q.erase r).card := (Finset.card_erase_of_mem hrQ).symm
      _ ≤ (InternalSlots.image (fun p => PEqualNP.Outside.L_meta_693_aux.slotVal C p - n)).card :=
        Finset.card_le_card hsurj
      _ ≤ InternalSlots.card := Finset.card_image_le
  have hFsub : FSlots ⊆ OutsideSlots := by
    intro p hp
    simp only [FSlots, OutsideSlots, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have hcardF : F.card ≤ Q.card + 1 := by
    have hF_le_O : F.card ≤ OutsideSlots.card :=
      Finset.card_image_le.trans (Finset.card_le_card hFsub)
    have hQpos : 1 ≤ Q.card := Finset.card_pos.2 ⟨r, hrQ⟩
    omega
  have hp_exists : ∀ w ∈ F, ∃ p : Fin n, p ∉ S ∧
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true := by
    intro w hwF
    obtain ⟨slot, hslot, rfl⟩ := Finset.mem_image.1 hwF
    simp only [FSlots, Finset.mem_filter] at hslot
    have hnsub := houtside _ hslot.2.2 hslot.2.1
    rw [Finset.not_subset] at hnsub
    obtain ⟨p, hp1, hp2⟩ := hnsub
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1
    exact ⟨p, hp2, hp1⟩
  choose pw hpw_notS hpw_wire using hp_exists
  let T : Finset (Fin n) := F.attach.image (fun w => pw w.1 w.2)
  have hTcard : T.card ≤ F.card := by
    calc
      T.card ≤ F.attach.card := Finset.card_image_le
      _ = F.card := Finset.card_attach
  have hTnotS : ∀ q ∈ T, q ∉ S := by
    intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hq
    exact hpw_notS w.1 w.2
  let xT : Fin n → Bool := fun q => decide (q ∈ T)
  have hF_true : ∀ w ∈ F, (C.wires (List.ofFn xT)).getD w false = true := by
    intro w hwF
    let ep : Fin n → Bool := fun q => decide (q = pw w hwF)
    have hmono : ∀ i, (C.wires (List.ofFn ep)).getD i false = true →
        (C.wires (List.ofFn xT)).getD i false = true := by
      apply PEqualNP.Outside.L_meta_693_aux.wiresFrom_mono C.gates
      · intro g hg; exact (hgates g hg).1
      · simp
      · intro i hi
        by_cases hin : i < n
        · have hi' : ep ⟨i, hin⟩ = true := by
            simpa [List.getD_eq_getElem?_getD, hin] using hi
          have hpi : ⟨i, hin⟩ = pw w hwF := by simpa [ep] using hi'
          have hmemT : (⟨i, hin⟩ : Fin n) ∈ T := by
            rw [hpi]
            exact Finset.mem_image.2 ⟨⟨w, hwF⟩, Finset.mem_attach _ _, rfl⟩
          simpa [xT, List.getD_eq_getElem?_getD, hin] using hmemT
        · have hdef : (List.ofFn ep).getD i false = false :=
            List.getD_eq_default _ _ (by simp; omega)
          rw [hdef] at hi
          exact False.elim (Bool.false_ne_true hi)
    exact hmono w (hpw_wire w hwF)
  have hQ_true : ∀ j : ℕ, j ∈ Q → ψ (n + j) = true →
      (C.wires (List.ofFn xT)).getD (n + j) false = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hjQ hpsij
      have hjC : j < C.gates.length := hQsize j hjQ
      obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g := ⟨C.gates[j], List.getElem?_eq_getElem hjC⟩
      have hgate_op := (hgates g (List.mem_of_getElem? hg)).1
      have hgate_len := (hgates g (List.mem_of_getElem? hg)).2
      have hpsi_j := hψ j hjQ g hg
      rw [hpsij] at hpsi_j
      have hgate_eval := PEqualNP.Outside.L_meta_693_aux.getD_wiresFrom_gate C.gates (List.ofFn xT) j g hg
      have hxTlen : (List.ofFn xT).length = n := by simp
      rw [hxTlen] at hgate_eval
      change (C.wires (List.ofFn xT)).getD (n + j) false = _ at hgate_eval
      rw [hgate_eval]
      apply PEqualNP.Outside.L_meta_693_aux.gateOp_eval_map_mono hgate_op g.inputs _ _ _ hpsi_j.symm
      intro w hw_mem hw_true
      by_cases hwlt : w < n + j
      · rw [if_pos hwlt] at hw_true
        rw [if_pos hwlt]
        by_cases hwQ : ∃ j' ∈ Q, w = n + j'
        · obtain ⟨j', hj'Q, rfl⟩ := hwQ
          exact ih j' (by omega) hj'Q hw_true
        · push_neg at hwQ
          obtain ⟨s, hs⟩ := PEqualNP.Outside.L_meta_693_aux.slotVal_exists_of_mem hg hgate_len hw_mem
          apply hF_true w
          refine Finset.mem_image.2 ⟨(j, s), ?_, hs⟩
          simp only [FSlots, AllSlots, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            and_true, hs]
          exact ⟨hjQ, hw_true, hwQ⟩
      · rw [if_neg hwlt] at hw_true
        exact False.elim (Bool.false_ne_true hw_true)
  have hroot_true : (C.wires (List.ofFn xT)).getD (n + r) false = true :=
    hQ_true r hrQ hroot
  by_contra hlt_k
  have hle_k : (Finset.univ.filter (fun q : Fin n => xT q = true)).card ≤ k := by
    have hfilt : Finset.univ.filter (fun q : Fin n => xT q = true) = T := by
      ext q; simp [xT]
    rw [hfilt]
    omega
  have hfalse : (C.wires (List.ofFn xT)).getD (n + r) false = false := by
    apply hpromise xT hle_k
    intro q hqS
    simp only [xT, decide_eq_false_iff_not]
    intro hqT
    exact hTnotS q hqT hqS
  rw [hroot_true] at hfalse
  simp at hfalse
