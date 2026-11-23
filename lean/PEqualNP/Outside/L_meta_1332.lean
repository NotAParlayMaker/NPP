import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332

open PEqualNP.CircuitLowerBounds

def substGate (dead p : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if p ∈ g.inputs then ⟨GateOp.or, []⟩ else g
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => i != p)⟩
  | GateOp.not => ⟨GateOp.not, g.inputs.map (fun i => if i = p then dead else i)⟩
  | _ => g

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc_lt (w : List Bool) (v : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
    List.getElem_append_left hi]

lemma getD_snoc_eq (w : List Bool) (v : Bool) :
    (w ++ [v]).getD w.length false = v := by
  simp

lemma any_filter_ne (l : List ℕ) (p : ℕ) (w₁ w₂ : List Bool)
    (heq : ∀ i, i ≠ p → w₁.getD i false = w₂.getD i false)
    (hp : w₂.getD p false = false) :
    ((l.filter (fun i => i != p)).map fun i => w₁.getD i false).any id =
      (l.map fun i => w₂.getD i false).any id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases hap : a = p
    · subst hap
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.any_cons, id_eq, hp, Bool.false_or]
      exact ih
    · have hne : (a != p) = true := bne_iff_ne.mpr hap
      simp only [List.filter_cons, hne, ↓reduceIte, List.map_cons, List.any_cons, id_eq,
        heq a hap, ih]

lemma substGate_eval (dead p : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (w₁ w₂ : List Bool) (hdead : w₁.length ≤ dead)
    (heq : ∀ i, i ≠ p → w₁.getD i false = w₂.getD i false)
    (hp : w₂.getD p false = false) :
    (substGate dead p g).op.eval ((substGate dead p g).inputs.map fun i => w₁.getD i false) =
      g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
  have hd : w₁.getD dead false = false := List.getD_eq_default _ _ hdead
  rcases g with ⟨op, ins⟩
  simp only at hg
  rcases hg with rfl | rfl | rfl
  · by_cases hmem : p ∈ ins
    · simp only [substGate, hmem, ↓reduceIte, GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      have h1 := hall (w₂.getD p false) (List.mem_map_of_mem hmem)
      rw [hp] at h1
      simp at h1
    · simp only [substGate, hmem, ↓reduceIte, GateOp.eval]
      congr 1
      apply List.map_congr_left
      intro u hu
      exact heq u (fun hup => hmem (hup ▸ hu))
  · simp only [substGate, GateOp.eval]
    exact any_filter_ne ins p w₁ w₂ heq hp
  · simp only [substGate, GateOp.eval, List.map_map]
    congr 1
    congr 1
    apply List.map_congr_left
    intro u _
    simp only [Function.comp_apply]
    by_cases hup : u = p
    · subst hup
      simp only [↓reduceIte]
      exact hd.trans hp.symm
    · simp only [hup, ↓reduceIte]
      exact heq u hup

lemma foldl_substGate (dead p : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length → p < w₁.length →
      w₁.length + gs.length ≤ dead →
      (∀ i, i ≠ p → w₁.getD i false = w₂.getD i false) →
      w₂.getD p false = false →
      ∀ i, i ≠ p →
        ((gs.map (substGate dead p)).foldl step w₁).getD i false =
          (gs.foldl step w₂).getD i false := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ _ heq _ i hi
    exact heq i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hp hdead heq hp0 i hi
    simp only [List.map_cons, List.foldl_cons]
    have hval := substGate_eval dead p g (hg g List.mem_cons_self) w₁ w₂ (by simp at hdead; omega) heq hp0
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (step w₁ (substGate dead p g)) (step w₂ g)
    · simp [step, hlen]
    · simp [step]; omega
    · simp only [step, List.length_append, List.length_cons, List.length_nil]
      simp only [List.length_cons] at hdead
      omega
    · intro j hj
      by_cases hlt : j < w₁.length
      · rw [step, step, getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
        exact heq j hj
      · by_cases hjeq : j = w₁.length
        · subst hjeq
          rw [step, step, getD_snoc_eq, hlen, getD_snoc_eq]
          exact hval
        · rw [List.getD_eq_default _ _ (by simp [step]; omega),
            List.getD_eq_default _ _ (by simp [step]; omega)]
    · rw [step, getD_snoc_lt _ _ _ (by omega)]
      exact hp0
    · exact hi

lemma substGate_wf (dead p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((substGate dead p g).op = GateOp.and ∨ (substGate dead p g).op = GateOp.or ∨
      (substGate dead p g).op = GateOp.not) ∧ (substGate dead p g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · by_cases hmem : p ∈ ins <;> simp [substGate, hmem, hlen]
  · refine ⟨Or.inr (Or.inl rfl), ?_⟩
    simp only [substGate]
    exact le_trans (List.length_filter_le _ _) hlen
  · simp [substGate, hlen]

lemma substGate_op_not (dead p : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : (substGate dead p g).op = GateOp.not) : g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  simp only at hg
  rcases hg with rfl | rfl | rfl
  · by_cases hmem : p ∈ ins <;> simp [substGate, hmem] at hnot
  · simp [substGate] at hnot
  · rfl

lemma substGate_len_lt_of_mem (dead p : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (hmem : p ∈ g.inputs) :
    (substGate dead p g).inputs.length < 2 := by
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hmem
  rcases hop with rfl | rfl
  · simp [substGate, hmem]
  · simp only [substGate]
    have hlt : (ins.filter (fun i => i != p)).length < ins.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨p, hmem, by simp⟩
    omega

lemma substGate_two_and_or (dead p : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h1 : (substGate dead p g).op = GateOp.and ∨ (substGate dead p g).op = GateOp.or)
    (h2 : (substGate dead p g).inputs.length = 2) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl
  · by_cases hmem : p ∈ ins
    · simp [substGate, hmem] at h2
    · simp [substGate, hmem] at h2
      exact ⟨Or.inl rfl, h2⟩
  · simp only [substGate] at h2
    have hle := List.length_filter_le (fun i => i != p) ins
    exact ⟨Or.inr rfl, by dsimp; omega⟩
  · simp [substGate] at h1

end PEqualNP.Outside.L_meta_1332

theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _ gates out hwf heval p _ a b hab ha_op ha_len ha_mem hb_op hb_len hb_mem t ι hι I hI
  let dead : ℕ := n + gates.length
  let gl : List PEqualNP.CircuitLowerBounds.Gate :=
    gates.map (PEqualNP.Outside.L_meta_1332.substGate dead p.val)
  have hlen : gl.length = gates.length := List.length_map _
  let ol : Fin m → ℕ := fun o => if out o = p.val then dead else out o
  let emb : Fin gates.length ↪ Fin gl.length := ⟨Fin.cast hlen.symm, Fin.cast_injective _⟩
  let κ : Fin t → Fin gl.length := fun r => emb (ι r)
  let J : Finset (Fin gl.length) := ((I.erase a).erase b).map emb
  refine ⟨gl, ol, κ, J, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
    exact PEqualNP.Outside.L_meta_1332.substGate_wf dead p.val g (hwf g hg)
  · intro q3 hnot
    let q : Fin gates.length := q3.cast hlen
    have hget : gl.get q3 = PEqualNP.Outside.L_meta_1332.substGate dead p.val (gates.get q) := by
      simp [gl, q]
    rw [hget] at hnot
    have hqnot : (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not :=
      PEqualNP.Outside.L_meta_1332.substGate_op_not dead p.val (gates.get q)
        (hwf (gates.get q) (List.get_mem gates q)).1 hnot
    obtain ⟨r2, hr2⟩ := hι q hqnot
    refine ⟨r2, ?_⟩
    simp [κ, emb, hr2, q]
  · intro q4 hq4
    let q : Fin gates.length := q4.cast hlen
    have hget : gl.get q4 = PEqualNP.Outside.L_meta_1332.substGate dead p.val (gates.get q) := by
      simp [gl, q]
    rw [hget] at hq4
    have hqI : q ∈ I := hI q (PEqualNP.Outside.L_meta_1332.substGate_two_and_or dead p.val
      (gates.get q) (hwf (gates.get q) (List.get_mem gates q)) hq4.1 hq4.2)
    have hqa : q ≠ a := by
      intro heq
      subst heq
      have hlt := PEqualNP.Outside.L_meta_1332.substGate_len_lt_of_mem dead p.val
        (gates.get q) ha_op ha_len ha_mem
      omega
    have hqb : q ≠ b := by
      intro heq
      subst heq
      have hlt := PEqualNP.Outside.L_meta_1332.substGate_len_lt_of_mem dead p.val
        (gates.get q) hb_op hb_len hb_mem
      omega
    have hmem : q ∈ (I.erase a).erase b :=
      Finset.mem_erase.mpr ⟨hqb, Finset.mem_erase.mpr ⟨hqa, hqI⟩⟩
    have hcast : emb q = q4 := by simp [emb, q]
    rw [← hcast]
    exact Finset.mem_map_of_mem emb hmem
  · have haI : a ∈ I := hI a ⟨ha_op, ha_len⟩
    have hbI : b ∈ I.erase a := Finset.mem_erase.mpr ⟨hab.symm, hI b ⟨hb_op, hb_len⟩⟩
    have hcard : J.card = ((I.erase a).erase b).card := Finset.card_map emb
    have hc1 : (I.erase a).card + 1 = I.card := Finset.card_erase_add_one haI
    have hc2 : ((I.erase a).erase b).card + 1 = (I.erase a).card := Finset.card_erase_add_one hbI
    omega
  · intro o2 x2
    let x' : Fin n → Bool := fun v => if v = p then false else x2 v
    have htarget : decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) =
        decide (∃ v ∈ S o2, x' v = true) := by
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨v, hvS, hvp, hvx⟩
        exact ⟨v, hvS, by simp [x', hvp, hvx]⟩
      · rintro ⟨v, hvS, hvx⟩
        by_cases hvp : v = p
        · simp [x', hvp] at hvx
        · exact ⟨v, hvS, hvp, by simpa [x', hvp] using hvx⟩
    rw [htarget, ← heval o2 x']
    change (gl.foldl PEqualNP.Outside.L_meta_1332.step (List.ofFn x2)).getD (ol o2) false =
      (gates.foldl PEqualNP.Outside.L_meta_1332.step (List.ofFn x')).getD (out o2) false
    by_cases ho : out o2 = p.val
    · simp only [ol, ho, ↓reduceIte]
      have h1 : (gl.foldl PEqualNP.Outside.L_meta_1332.step (List.ofFn x2)).getD dead false = false := by
        apply List.getD_eq_default
        rw [PEqualNP.Outside.L_meta_1332.foldl_step_len, List.length_ofFn, hlen]
      have h2 : (gates.foldl PEqualNP.Outside.L_meta_1332.step (List.ofFn x')).getD p.val false = false := by
        have hkeep : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
            p.val < w.length → (gs.foldl PEqualNP.Outside.L_meta_1332.step w).getD p.val false =
              w.getD p.val false := by
          intro gs
          induction gs with
          | nil => intro w _; rfl
          | cons g gs ih =>
            intro w hw
            rw [List.foldl_cons, ih (PEqualNP.Outside.L_meta_1332.step w g)
              (by simp [PEqualNP.Outside.L_meta_1332.step]; omega)]
            exact PEqualNP.Outside.L_meta_1332.getD_snoc_lt w _ p.val hw
        rw [hkeep gates (List.ofFn x') (by simp)]
        simp [List.getD_eq_getElem?_getD, x']
      rw [h1, h2]
    · simp only [ol, ho, ↓reduceIte]
      apply PEqualNP.Outside.L_meta_1332.foldl_substGate dead p.val gates
        (fun g hg => (hwf g hg).1) (List.ofFn x2) (List.ofFn x')
      · simp
      · simp
      · simp [dead]
      · intro i hip
        by_cases hin : i < n
        · have hne : (⟨i, hin⟩ : Fin n) ≠ p := fun h => hip (congrArg Fin.val h)
          simp [List.getD_eq_getElem?_getD, hin, x', hne]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
      · simp [List.getD_eq_getElem?_getD, x']
      · exact ho
