import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3256

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_step_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWire acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWire acc g)]
    simp [stepWire]
    omega

private lemma foldl_step_getD (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl stepWire acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire acc g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire acc g) hi']
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma gateOp_and_eval (u v : Bool) : GateOp.and.eval [u, v] = (u && v) := by
  cases u <;> cases v <;> rfl

private lemma gateOp_or_eval (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
  cases u <;> cases v <;> rfl

private lemma wireValue_gate {n : ℕ} (C : Circuit) (x : List Bool) (hx : x.length = n)
    (hRB : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length) :
    wireValue C x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireValue C x i) := by
  have hgate : gateAt C k = C.gates[k] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have htake : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    have hdrop : C.gates.drop k = gateAt C k :: C.gates.drop (k + 1) := by
      rw [hgate, List.drop_eq_getElem_cons hk]
    conv_lhs => rw [← List.take_append_drop k C.gates, hdrop]
  let acc := (C.gates.take k).foldl stepWire x
  have hlen : acc.length = n + k := by
    dsimp [acc]
    rw [foldl_step_len, hx, List.length_take_of_le (Nat.le_of_lt hk)]
  have hwires : C.wires x = (C.gates.drop (k + 1)).foldl stepWire (stepWire acc (gateAt C k)) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [htake]
    rw [List.foldl_append, List.foldl_cons]
  have hget : wireValue C x (n + k) = (stepWire acc (gateAt C k)).getD (n + k) false := by
    dsimp [wireValue]
    rw [hwires]
    apply foldl_step_getD
    simp [stepWire, hlen]
  rw [hget]
  have hlast : (stepWire acc (gateAt C k)).getD (n + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => acc.getD i false) := by
    simp [stepWire, hlen, List.getD_eq_getElem?_getD]
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + k := hRB k hk i hi
  have hi_acc : i < acc.length := by omega
  dsimp [wireValue]
  rw [hwires]
  have h1 : ((C.gates.drop (k + 1)).foldl stepWire (stepWire acc (gateAt C k))).getD i false =
      (stepWire acc (gateAt C k)).getD i false :=
    foldl_step_getD _ _ i (by simp [stepWire]; omega)
  rw [h1]
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi_acc]

private lemma wireValue_input {n : ℕ} (C : Circuit) (x : List Bool) (hx : x.length = n)
    (w : ℕ) (hw : w < n) :
    wireValue C x w = x.getD w false := by
  dsimp [wireValue]
  rw [wires_eq_foldl]
  exact foldl_step_getD C.gates x w (by omega)

private lemma incidenceInput_len {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    (incidenceInput X Y).length = n + m := by
  simp [incidenceInput]

private lemma incidenceInput_getD_left {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m))
    (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
  simp [incidenceInput, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]

private lemma incidenceInput_getD_right {n m : ℕ} (X : Finset (Fin n)) (Y : Finset (Fin m))
    (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + m) :
    (incidenceInput X Y).getD i false = decide (⟨i - n, by omega⟩ ∈ Y) := by
  have hlen1 : (List.ofFn (fun p : Fin n => decide (p ∈ X))).length = n := by simp
  rw [incidenceInput, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen1]
  have hlt : i - n < m := by omega
  simp [hlt]

private lemma wireValue_mono {x1 : ℕ} (x2 : Circuit) (hAO : IsAO2 (x1 + x1) x2)
    (x4 : Fin x1) (S T : Finset (Fin x1)) (hST : S ⊆ T) :
    ∀ w : ℕ,
      wireValue x2 (incidenceInput S {x4}) w = true →
      wireValue x2 (incidenceInput T {x4}) w = true := by
  have hlenS : (incidenceInput S {x4}).length = x1 + x1 := incidenceInput_len S {x4}
  have hlenT : (incidenceInput T {x4}).length = x1 + x1 := incidenceInput_len T {x4}
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwin : w < x1 + x1
    · rw [wireValue_input x2 _ hlenS w hwin] at hw
      rw [wireValue_input x2 _ hlenT w hwin]
      by_cases hw1 : w < x1
      · rw [incidenceInput_getD_left S {x4} w hw1] at hw
        rw [incidenceInput_getD_left T {x4} w hw1]
        simp only [decide_eq_true_eq] at hw ⊢
        exact hST hw
      · have hle : x1 ≤ w := Nat.le_of_not_lt hw1
        rw [incidenceInput_getD_right S {x4} w hle hwin] at hw
        rw [incidenceInput_getD_right T {x4} w hle hwin]
        exact hw
    · have hge : x1 + x1 ≤ w := Nat.le_of_not_lt hwin
      let k := w - (x1 + x1)
      have hw_eq : w = x1 + x1 + k := by omega
      by_cases hk : k < x2.gates.length
      · rw [hw_eq] at hw ⊢
        rw [wireValue_gate x2 _ hlenS hAO.2.1 k hk] at hw
        rw [wireValue_gate x2 _ hlenT hAO.2.1 k hk]
        have hg_mem : gateAt x2 k ∈ x2.gates := by
          simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        have hlen2 : (gateAt x2 k).inputs.length = 2 := hAO.2.2 (gateAt x2 k) hg_mem
        rcases hlen2_eq : (gateAt x2 k).inputs with _ | ⟨a, _ | ⟨b, _ | c⟩⟩ <;>
          simp [hlen2_eq] at hlen2
        have ha : a < x1 + x1 + k := hAO.2.1 k hk a (by simp [hlen2_eq])
        have hb : b < x1 + x1 + k := hAO.2.1 k hk b (by simp [hlen2_eq])
        have ha' : a < w := by omega
        have hb' : b < w := by omega
        have hop : (gateAt x2 k).op = GateOp.and ∨ (gateAt x2 k).op = GateOp.or :=
          hAO.1 (gateAt x2 k) hg_mem
        rw [hlen2_eq] at hw
        rcases hop with hop | hop
        · rw [hop, List.map_cons, List.map_cons, List.map_nil, gateOp_and_eval] at hw ⊢
          obtain ⟨hwa, hwb⟩ := Bool.and_eq_true_iff.mp hw
          exact Bool.and_eq_true_iff.mpr ⟨ih a ha' hwa, ih b hb' hwb⟩
        · rw [hop, List.map_cons, List.map_cons, List.map_nil, gateOp_or_eval] at hw ⊢
          rcases Bool.or_eq_true_iff.mp hw with hwa | hwb
          · exact Bool.or_eq_true_iff.mpr (Or.inl (ih a ha' hwa))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (ih b hb' hwb))
      · have hlenW : (x2.wires (incidenceInput S {x4})).length = x1 + x1 + x2.gates.length := by
          rw [wires_eq_foldl, foldl_step_len, hlenS]
        have hnot : ¬ w < (x2.wires (incidenceInput S {x4})).length := by omega
        dsimp [wireValue] at hw
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hnot)] at hw
        simp at hw

private lemma mem_of_single_true {x1 : ℕ} (x2 : Circuit) (hAO : IsAO2 (x1 + x1) x2)
    (x3 : Finset (Fin x1)) (x4 : Fin x1) (w : ℕ)
    (hfalse : wireValue x2 (incidenceInput x3ᶜ {x4}) w = false)
    (p : Fin x1) (hp : wireValue x2 (incidenceInput {p} {x4}) w = true) :
    p ∈ x3 := by
  by_contra hnot
  have hsub : {p} ⊆ x3ᶜ := by
    intro q hq
    simp only [Finset.mem_singleton] at hq
    subst hq
    simpa using hnot
  have ht := wireValue_mono x2 hAO x4 {p} x3ᶜ hsub w hp
  rw [ht] at hfalse
  simp at hfalse

private lemma card_le_image_merge (s : Finset ℕ) (u v : ℕ) :
    s.card ≤ (s.image (fun y => if y = v then u else y)).card + 1 := by
  have hsub : s ⊆ insert v (s.image (fun y => if y = v then u else y)) := by
    intro y hy
    by_cases hyv : y = v
    · simp [hyv]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨y, hy, by simp [hyv]⟩
  calc
    s.card ≤ (insert v (s.image (fun y => if y = v then u else y))).card := Finset.card_le_card hsub
    _ ≤ (s.image (fun y => if y = v then u else y)).card + 1 := Finset.card_insert_le _ _

end PEqualNP.Outside.L_meta_3256

theorem PEqualNP.Outside.L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro x1 x2 x3 x4 hAO hout hpos hneg
  let : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
    PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let f : ℕ → Finset (Fin x1) → Bool := fun w S =>
    PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput S {x4}) w
  let A : ℕ → Finset (Fin x1) := fun w => Finset.univ.filter fun p : Fin x1 => f w {p} = true
  let x9 : Finset ℕ := (Finset.range x2.size).filter fun j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt x2 j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    f (x1 + x1 + j) x3ᶜ = false ∧
    2 ≤ (A (x1 + x1 + j)).card
  refine ⟨x9, ?_, ?_⟩
  · have hinv : ∀ k ≤ x2.size, ∃ c : Fin x1 → ℕ,
        x3.card ≤ (x3.image c).card + (x9 ∩ Finset.range k).card ∧
        ∀ w < x1 + x1 + k, f w x3ᶜ = false → ∀ p ∈ A w, ∀ q ∈ A w, c p = c q := by
      intro k hk
      induction k with
      | zero =>
        refine ⟨fun p => p.val, ?_, ?_⟩
        · have hinj : Function.Injective (fun p : Fin x1 => p.val) := Fin.val_injective
          rw [Finset.card_image_of_injective x3 hinj]
          omega
        · intro w hw hwfalse p hp q hq
          have hw' : w < x1 + x1 := by omega
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          have hlenp := PEqualNP.Outside.L_meta_3256.incidenceInput_len (n := x1) (m := x1) {p} {x4}
          have hlenq := PEqualNP.Outside.L_meta_3256.incidenceInput_len (n := x1) (m := x1) {q} {x4}
          have hlenc := PEqualNP.Outside.L_meta_3256.incidenceInput_len (n := x1) (m := x1) x3ᶜ {x4}
          dsimp [f] at hwfalse hp hq
          rw [PEqualNP.Outside.L_meta_3256.wireValue_input x2 _ hlenc w hw'] at hwfalse
          rw [PEqualNP.Outside.L_meta_3256.wireValue_input x2 _ hlenp w hw'] at hp
          rw [PEqualNP.Outside.L_meta_3256.wireValue_input x2 _ hlenq w hw'] at hq
          by_cases hw1 : w < x1
          · rw [PEqualNP.Outside.L_meta_3256.incidenceInput_getD_left {p} {x4} w hw1] at hp
            rw [PEqualNP.Outside.L_meta_3256.incidenceInput_getD_left {q} {x4} w hw1] at hq
            simp only [decide_eq_true_eq, Finset.mem_singleton] at hp hq
            subst hp
            subst hq
            rfl
          · have hle : x1 ≤ w := Nat.le_of_not_lt hw1
            rw [PEqualNP.Outside.L_meta_3256.incidenceInput_getD_right x3ᶜ {x4} w hle hw'] at hwfalse
            rw [PEqualNP.Outside.L_meta_3256.incidenceInput_getD_right {p} {x4} w hle hw'] at hp
            rw [hp] at hwfalse
            simp at hwfalse
      | succ k ih =>
        obtain ⟨c, hc_card, hc_eq⟩ := ih (Nat.le_of_lt hk)
        have hk_gates : k < x2.gates.length := hk
        have hg_mem : PEqualNP.MetaComplexity.NestedCover.gateAt x2 k ∈ x2.gates := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hk_gates]
        have hlen2 : (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).inputs.length = 2 :=
          hAO.2.2 _ hg_mem
        rcases hinp : (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).inputs with
          _ | ⟨a, _ | ⟨b, _ | d⟩⟩ <;> simp [hinp] at hlen2
        have ha : a < x1 + x1 + k := hAO.2.1 k hk_gates a (by simp [hinp])
        have hb : b < x1 + x1 + k := hAO.2.1 k hk_gates b (by simp [hinp])
        have hgate_eval : ∀ S : Finset (Fin x1),
            f (x1 + x1 + k) S =
              (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).op.eval [f a S, f b S] := by
          intro S
          dsimp [f]
          rw [PEqualNP.Outside.L_meta_3256.wireValue_gate x2 _
            (PEqualNP.Outside.L_meta_3256.incidenceInput_len S {x4}) hAO.2.1 k hk_gates]
          simp [hinp]
        by_cases hneg_k : f (x1 + x1 + k) x3ᶜ = false
        · have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).op =
              PEqualNP.CircuitLowerBounds.GateOp.and ∨
              (PEqualNP.MetaComplexity.NestedCover.gateAt x2 k).op =
              PEqualNP.CircuitLowerBounds.GateOp.or := hAO.1 _ hg_mem
          rcases hop with hop | hop
          · refine ⟨c, ?_, ?_⟩
            · have hsub : x9 ∩ Finset.range k ⊆ x9 ∩ Finset.range (k + 1) := by
                intro z hz
                simp only [Finset.mem_inter, Finset.mem_range] at hz ⊢
                exact ⟨hz.1, Nat.lt_succ_of_lt hz.2⟩
              exact le_trans hc_card (Nat.add_le_add_left (Finset.card_le_card hsub) _)
            · intro w hw hwfalse p hp q hq
              by_cases hwk : w < x1 + x1 + k
              · exact hc_eq w hwk hwfalse p hp q hq
              · have hweq : w = x1 + x1 + k := by omega
                subst hweq
                have hfa_or_b : f a x3ᶜ = false ∨ f b x3ᶜ = false := by
                  have hge := hgate_eval x3ᶜ
                  rw [hneg_k, hop, PEqualNP.Outside.L_meta_3256.gateOp_and_eval] at hge
                  exact Bool.and_eq_false_iff.mp hge.symm
                simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
                have hpa : f a {p} = true ∧ f b {p} = true := by
                  have hge := hgate_eval {p}
                  rw [hp, hop, PEqualNP.Outside.L_meta_3256.gateOp_and_eval] at hge
                  exact Bool.and_eq_true_iff.mp hge.symm
                have hqa : f a {q} = true ∧ f b {q} = true := by
                  have hge := hgate_eval {q}
                  rw [hq, hop, PEqualNP.Outside.L_meta_3256.gateOp_and_eval] at hge
                  exact Bool.and_eq_true_iff.mp hge.symm
                rcases hfa_or_b with hfa | hfb
                · exact hc_eq a ha hfa p (by simpa [A] using hpa.1) q (by simpa [A] using hqa.1)
                · exact hc_eq b hb hfb p (by simpa [A] using hpa.2) q (by simpa [A] using hqa.2)
          · have hfa : f a x3ᶜ = false := by
              have hge := hgate_eval x3ᶜ
              rw [hneg_k, hop, PEqualNP.Outside.L_meta_3256.gateOp_or_eval] at hge
              exact (Bool.or_eq_false_iff.mp hge.symm).1
            have hfb : f b x3ᶜ = false := by
              have hge := hgate_eval x3ᶜ
              rw [hneg_k, hop, PEqualNP.Outside.L_meta_3256.gateOp_or_eval] at hge
              exact (Bool.or_eq_false_iff.mp hge.symm).2
            by_cases hAa : (A a).Nonempty
            · by_cases hAb : (A b).Nonempty
              · obtain ⟨p0, hp0⟩ := hAa
                obtain ⟨q0, hq0⟩ := hAb
                by_cases hcpq : c p0 = c q0
                · refine ⟨c, ?_, ?_⟩
                  · have hsub : x9 ∩ Finset.range k ⊆ x9 ∩ Finset.range (k + 1) := by
                      intro z hz
                      simp only [Finset.mem_inter, Finset.mem_range] at hz ⊢
                      exact ⟨hz.1, Nat.lt_succ_of_lt hz.2⟩
                    exact le_trans hc_card (Nat.add_le_add_left (Finset.card_le_card hsub) _)
                  · intro w hw hwfalse p hp q hq
                    by_cases hwk : w < x1 + x1 + k
                    · exact hc_eq w hwk hwfalse p hp q hq
                    · have hweq : w = x1 + x1 + k := by omega
                      subst hweq
                      have hmem : ∀ r ∈ A (x1 + x1 + k), c r = c p0 := by
                        intro r hr
                        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hr
                        have hror := hgate_eval {r}
                        rw [hr, hop, PEqualNP.Outside.L_meta_3256.gateOp_or_eval] at hror
                        rcases Bool.or_eq_true_iff.mp hror.symm with hra | hrb
                        · exact hc_eq a ha hfa r (by simpa [A] using hra) p0 hp0
                        · rw [hc_eq b hb hfb r (by simpa [A] using hrb) q0 hq0, ← hcpq]
                      exact (hmem p hp).trans (hmem q hq).symm
                · let c' : Fin x1 → ℕ := fun p => if c p = c q0 then c p0 else c p
                  have hp0_in : p0 ∈ A (x1 + x1 + k) := by
                    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp0 ⊢
                    rw [hgate_eval {p0}, hop, hp0]
                    rfl
                  have hq0_in : q0 ∈ A (x1 + x1 + k) := by
                    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hq0 ⊢
                    rw [hgate_eval {q0}, hop, hq0]
                    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
                  have hp0_ne_q0 : p0 ≠ q0 := fun heq => hcpq (congrArg c heq)
                  have hcard2 : 2 ≤ (A (x1 + x1 + k)).card := by
                    have hsub : ({p0, q0} : Finset (Fin x1)) ⊆ A (x1 + x1 + k) := by
                      intro z hz
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                      rcases hz with rfl | rfl <;> assumption
                    have h2 : ({p0, q0} : Finset (Fin x1)).card = 2 :=
                      Finset.card_pair hp0_ne_q0
                    rw [← h2]
                    exact Finset.card_le_card hsub
                  have hk_x9 : k ∈ x9 := by
                    simp only [x9, Finset.mem_filter, Finset.mem_range]
                    exact ⟨hk, hop, hneg_k, hcard2⟩
                  have hinter : x9 ∩ Finset.range (k + 1) = insert k (x9 ∩ Finset.range k) := by
                    ext z
                    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_insert]
                    constructor
                    · rintro ⟨hz1, hz2⟩
                      rcases Nat.lt_succ_iff_lt_or_eq.mp hz2 with hlt | rfl
                      · exact Or.inr ⟨hz1, hlt⟩
                      · exact Or.inl rfl
                    · rintro (rfl | ⟨hz1, hz2⟩)
                      · exact ⟨hk_x9, Nat.lt_succ_self z⟩
                      · exact ⟨hz1, Nat.lt_succ_of_lt hz2⟩
                  have hk_notin : k ∉ x9 ∩ Finset.range k :=
                    fun h => Nat.lt_irrefl k (Finset.mem_range.mp (Finset.mem_inter.mp h).2)
                  have hinter_card : (x9 ∩ Finset.range (k + 1)).card =
                      (x9 ∩ Finset.range k).card + 1 := by
                    rw [hinter, Finset.card_insert_of_notMem hk_notin]
                  have himg_eq : x3.image c' =
                      (x3.image c).image (fun y => if y = c q0 then c p0 else y) := by
                    ext y
                    simp [c']
                  have hc_card' : (x3.image c).card ≤ (x3.image c').card + 1 := by
                    rw [himg_eq]
                    exact PEqualNP.Outside.L_meta_3256.card_le_image_merge (x3.image c) (c p0) (c q0)
                  refine ⟨c', by omega, ?_⟩
                  intro w hw hwfalse p hp q hq
                  by_cases hwk : w < x1 + x1 + k
                  · have := hc_eq w hwk hwfalse p hp q hq
                    dsimp [c']
                    rw [this]
                  · have hweq : w = x1 + x1 + k := by omega
                    subst hweq
                    have hmem : ∀ r ∈ A (x1 + x1 + k), c' r = c p0 := by
                      intro r hr
                      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hr
                      have hror := hgate_eval {r}
                      rw [hr, hop, PEqualNP.Outside.L_meta_3256.gateOp_or_eval] at hror
                      rcases Bool.or_eq_true_iff.mp hror.symm with hra | hrb
                      · have hcr : c r = c p0 := hc_eq a ha hfa r (by simpa [A] using hra) p0 hp0
                        dsimp [c']
                        rw [hcr]
                        simp [hcpq]
                      · have hcr : c r = c q0 := hc_eq b hb hfb r (by simpa [A] using hrb) q0 hq0
                        dsimp [c']
                        rw [hcr]
                        simp
                    exact (hmem p hp).trans (hmem q hq).symm
              · refine ⟨c, ?_, ?_⟩
                · have hsub : x9 ∩ Finset.range k ⊆ x9 ∩ Finset.range (k + 1) := by
                    intro z hz
                    simp only [Finset.mem_inter, Finset.mem_range] at hz ⊢
                    exact ⟨hz.1, Nat.lt_succ_of_lt hz.2⟩
                  exact le_trans hc_card (Nat.add_le_add_left (Finset.card_le_card hsub) _)
                · intro w hw hwfalse p hp q hq
                  by_cases hwk : w < x1 + x1 + k
                  · exact hc_eq w hwk hwfalse p hp q hq
                  · have hweq : w = x1 + x1 + k := by omega
                    subst hweq
                    have hsubA : ∀ r ∈ A (x1 + x1 + k), r ∈ A a := by
                      intro r hr
                      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
                      have hror := hgate_eval {r}
                      rw [hr, hop, PEqualNP.Outside.L_meta_3256.gateOp_or_eval] at hror
                      rcases Bool.or_eq_true_iff.mp hror.symm with hra | hrb
                      · exact hra
                      · exfalso; exact hAb ⟨r, by simpa [A] using hrb⟩
                    exact hc_eq a ha hfa p (hsubA p hp) q (hsubA q hq)
            · refine ⟨c, ?_, ?_⟩
              · have hsub : x9 ∩ Finset.range k ⊆ x9 ∩ Finset.range (k + 1) := by
                  intro z hz
                  simp only [Finset.mem_inter, Finset.mem_range] at hz ⊢
                  exact ⟨hz.1, Nat.lt_succ_of_lt hz.2⟩
                exact le_trans hc_card (Nat.add_le_add_left (Finset.card_le_card hsub) _)
              · intro w hw hwfalse p hp q hq
                by_cases hwk : w < x1 + x1 + k
                · exact hc_eq w hwk hwfalse p hp q hq
                · have hweq : w = x1 + x1 + k := by omega
                  subst hweq
                  have hsubA : ∀ r ∈ A (x1 + x1 + k), r ∈ A b := by
                    intro r hr
                    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
                    have hror := hgate_eval {r}
                    rw [hr, hop, PEqualNP.Outside.L_meta_3256.gateOp_or_eval] at hror
                    rcases Bool.or_eq_true_iff.mp hror.symm with hra | hrb
                    · exfalso; exact hAa ⟨r, by simpa [A] using hra⟩
                    · exact hrb
                  exact hc_eq b hb hfb p (hsubA p hp) q (hsubA q hq)
        · refine ⟨c, ?_, ?_⟩
          · have hsub : x9 ∩ Finset.range k ⊆ x9 ∩ Finset.range (k + 1) := by
              intro z hz
              simp only [Finset.mem_inter, Finset.mem_range] at hz ⊢
              exact ⟨hz.1, Nat.lt_succ_of_lt hz.2⟩
            exact le_trans hc_card (Nat.add_le_add_left (Finset.card_le_card hsub) _)
          · intro w hw hwfalse p hp q hq
            have hwk : w < x1 + x1 + k := by
              by_contra hnot
              have hweq : w = x1 + x1 + k := by omega
              subst hweq
              exact hneg_k hwfalse
            exact hc_eq w hwk hwfalse p hp q hq
    by_cases hx3_ne : x3.Nonempty
    · obtain ⟨c, hc_card, hc_eq⟩ := hinv x2.size (le_refl _)
      have hinter : x9 ∩ Finset.range x2.size = x9 := by
        ext z
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hz, _⟩; exact hz
        · intro hz
          exact ⟨hz, (Finset.mem_filter.mp hz).1⟩
      rw [hinter] at hc_card
      have hsub_A : ∀ p ∈ x3, p ∈ A x2.output := by
        intro p hp
        simpa [A, f, PEqualNP.CircuitLowerBounds.wireValue, PEqualNP.CircuitLowerBounds.Circuit.eval]
          using hpos p hp
      have hconst : ∀ p ∈ x3, ∀ q ∈ x3, c p = c q := by
        intro p hp q hq
        exact hc_eq x2.output hout hneg p (hsub_A p hp) q (hsub_A q hq)
      obtain ⟨p0, hp0⟩ := hx3_ne
      have himg_sub : x3.image c ⊆ {c p0} := by
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
        simp [hconst p hp p0 hp0]
      have himg_card : (x3.image c).card ≤ 1 := by
        simpa using Finset.card_le_card himg_sub
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hx3_ne]
      simp
  · intro j hj
    simp only [x9, Finset.mem_filter, Finset.mem_range] at hj
    rcases hj with ⟨hj_lt, hj_op, hj_neg, hj_card⟩
    refine ⟨hj_lt, hj_op, hj_neg, ?_, ?_⟩
    · have h1lt : 1 < (A (x1 + x1 + j)).card := by omega
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1lt
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact ⟨p, q, hpq, hp, hq⟩
    · intro p hp
      exact PEqualNP.Outside.L_meta_3256.mem_of_single_true x2 hAO x3 x4 (x1 + x1 + j) hj_neg p hp
