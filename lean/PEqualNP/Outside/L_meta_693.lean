import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_693

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_length (l : List Gate) (w : List Bool) :
    (l.foldl step w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp
  | cons g l ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_getD (l : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (l.foldl step w).getD i false = w.getD i false := by
  induction l generalizing w with
  | nil => rfl
  | cons g l ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact step_getD w g i hi

theorem foldl_gate (l1 l2 : List Gate) (g : Gate) (x : List Bool) :
    ((l1 ++ g :: l2).foldl step x).getD (x.length + l1.length) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + l1.length then ((l1 ++ g :: l2).foldl step x).getD i false
        else false) := by
  rw [List.foldl_append, List.foldl_cons]
  have hlen := foldl_length l1 x
  rw [← hlen]
  generalize l1.foldl step x = W
  rw [foldl_getD l2 (step W g) W.length (by simp [step])]
  have h1 : (step W g).getD W.length false =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp [step]
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · rw [foldl_getD l2 (step W g) i (by simp [step]; omega)]
    exact (step_getD W g i hi).symm
  · exact List.getD_eq_default _ _ (by omega)

theorem foldl_gate' (gs l1 l2 : List Gate) (g : Gate) (h : gs = l1 ++ g :: l2)
    (x : List Bool) :
    (gs.foldl step x).getD (x.length + l1.length) false =
      g.op.eval (g.inputs.map fun i =>
        if i < x.length + l1.length then (gs.foldl step x).getD i false else false) := by
  subst h
  exact foldl_gate l1 l2 g x

def val (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def rd (C : Circuit) {n : ℕ} (x : Fin n → Bool) (t a : ℕ) : Bool :=
  if a < t then val C x a else false

theorem rd_true (C : Circuit) {n : ℕ} (x : Fin n → Bool) (t a : ℕ) :
    rd C x t a = true ↔ a < t ∧ val C x a = true := by
  unfold rd
  split_ifs with h <;> simp [h]

theorem val_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : val C x w = false := by
  unfold val
  rw [wires_eq]
  apply List.getD_eq_default
  rw [foldl_length, List.length_ofFn]
  exact hw

theorem val_gate (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => rd C x (n + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have h := foldl_gate' C.gates (C.gates.take j) (C.gates.drop (j + 1)) C.gates[j] hsplit
    (List.ofFn x)
  rw [List.length_ofFn, List.length_take, Nat.min_eq_left hj.le] at h
  exact h

theorem gate_form (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b : ℕ, (∀ x : Fin n → Bool, val C x (n + j) = (rd C x (n + j) a && rd C x (n + j) b)) ∨
      (∀ x : Fin n → Bool, val C x (n + j) = (rd C x (n + j) a || rd C x (n + j) b)) := by
  obtain ⟨hop, hlen⟩ := hg C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  refine ⟨a, b, ?_⟩
  rcases hop with h | h
  · left
    intro x
    rw [val_gate C x j hj, h, hab]
    simp [GateOp.eval]
  · right
    intro x
    rw [val_gate C x j hj, h, hab]
    simp [GateOp.eval]

theorem val_mono (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hw : w < n
    · rw [val_input C y w hw]
      rw [val_input C x w hw] at hx
      exact hxy _ hx
    · by_cases hw2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        obtain ⟨a, b, hab | hab⟩ := gate_form C n hg j (by omega)
        · rw [hab] at hx ⊢
          rw [Bool.and_eq_true, rd_true, rd_true] at hx ⊢
          exact ⟨⟨hx.1.1, ih a hx.1.1 hx.1.2⟩, ⟨hx.2.1, ih b hx.2.1 hx.2.2⟩⟩
        · rw [hab] at hx ⊢
          rw [Bool.or_eq_true, rd_true, rd_true] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl ⟨hx.1, ih a hx.1 hx.2⟩
          · exact Or.inr ⟨hx.1, ih b hx.1 hx.2⟩
      · rw [val_big C x w (by omega)] at hx
        exact absurd hx (by simp)


def ins (C : Circuit) (j : ℕ) : List ℕ :=
  if h : j < C.gates.length then (C.gates[j]).inputs else []

theorem ins_eq (C : Circuit) (j : ℕ) (h : j < C.gates.length) :
    ins C j = (C.gates[j]).inputs := by
  unfold ins
  rw [dif_pos h]

theorem ins_card (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) (j : ℕ) :
    (ins C j).toFinset.card ≤ 2 := by
  unfold ins
  split_ifs with h
  · exact (List.toFinset_card_le _).trans (hg _ (List.getElem_mem h)).2.le
  · simp

theorem and_eval (u v : Bool) : GateOp.and.eval [u, v] = (u && v) := by
  simp [GateOp.eval]

theorem or_eval (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
  simp [GateOp.eval]

theorem main (n k r : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false)
    (hr : r ∈ Q) (hQ : ∀ j ∈ Q, j < C.size)
    (hpar : ∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs)
    (hψ : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false)))
    (hout : ∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true →
      ¬ (Finset.univ.filter (fun p : Fin n =>
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)) ⊆ S)
    (hroot : ψ (n + r) = true) : k ≤ Q.card := by
  classical
  have hQ' : ∀ j ∈ Q, j < C.gates.length := hQ
  let U : Finset ℕ := Q.biUnion (fun j => (ins C j).toFinset)
  let R : Finset ℕ := U.filter (fun w => (∀ j ∈ Q, w ≠ n + j) ∧ ψ w = true)
  let I : Finset ℕ := (Q.erase r).image (fun j => n + j)
  have hUcard : U.card ≤ 2 * Q.card := by
    calc U.card ≤ ∑ j ∈ Q, ((ins C j).toFinset).card := Finset.card_biUnion_le
      _ ≤ Q.card • 2 := Finset.sum_le_card_nsmul _ _ _ (fun j _ => ins_card C hg j)
      _ = 2 * Q.card := by rw [smul_eq_mul, mul_comm]
  have hIcard : I.card = Q.card - 1 := by
    show ((Q.erase r).image (fun j => n + j)).card = Q.card - 1
    rw [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h),
      Finset.card_erase_of_mem hr]
  have hIU : I ⊆ U := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    rw [Finset.mem_erase] at hj
    obtain ⟨j', hj', _, g, hg', hin⟩ := hpar j hj.2 hj.1
    refine Finset.mem_biUnion.mpr ⟨j', hj', ?_⟩
    have hlt := hQ' j' hj'
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hg'
    rw [List.mem_toFinset, ins_eq C j' hlt, hg']
    exact hin
  have hRI : R ⊆ U \ I := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    refine Finset.mem_sdiff.mpr ⟨hw'.1, fun hwI => ?_⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hwI
    exact hw'.2.1 j (Finset.mem_of_mem_erase hj) rfl
  have hRcard : R.card ≤ Q.card + 1 := by
    have h1 := Finset.card_le_card hRI
    have h2 := Finset.card_sdiff_add_card_eq_card hIU
    have hpos : 0 < Q.card := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  have hpick : ∀ w ∈ R, ∃ p : Fin n, p ∉ S ∧
      val C (fun q : Fin n => decide (q = p)) w = true := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    obtain ⟨p, hp, hpS⟩ := Finset.not_subset.mp (hout w hw'.2.1 hw'.2.2)
    exact ⟨p, hpS, (Finset.mem_filter.mp hp).2⟩
  choose pf hpf using hpick
  let T : Finset (Fin n) := R.attach.image (fun w => pf w.1 w.2)
  have hTcard : T.card ≤ R.card := by
    have h1 : T.card ≤ R.attach.card := Finset.card_image_le
    rwa [Finset.card_attach] at h1
  let x : Fin n → Bool := fun q => decide (q ∈ T)
  have hxdef : ∀ q, x q = true ↔ q ∈ T := fun q => decide_eq_true_iff
  have hxS : ∀ q ∈ S, x q = false := by
    intro q hq
    rw [← Bool.not_eq_true, hxdef]
    intro hqT
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hqT
    exact (hpf w.1 w.2).1 hq
  have hxT : Finset.univ.filter (fun q : Fin n => x q = true) = T := by
    ext q
    rw [Finset.mem_filter, hxdef]
    simp
  have hval : ∀ j, j ∈ Q → ψ (n + j) = true → val C x (n + j) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hψj
      have hlt := hQ' j hj
      have hgj := hψ j hj C.gates[j] (List.getElem?_eq_getElem hlt)
      have h2 := hgj.symm.trans hψj
      rw [val_gate C x j hlt]
      obtain ⟨hop, hlen⟩ := hg C.gates[j] (List.getElem_mem hlt)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      have key : ∀ w, w ∈ (C.gates[j]).inputs → (if w < n + j then ψ w else false) = true →
          rd C x (n + j) w = true := by
        intro w hw hw2
        have hwlt : w < n + j := by
          by_contra h
          rw [if_neg h] at hw2
          exact Bool.false_ne_true hw2
        rw [if_pos hwlt] at hw2
        rw [rd_true]
        refine ⟨hwlt, ?_⟩
        by_cases hin : ∃ j0 ∈ Q, w = n + j0
        · obtain ⟨j0, hj0, rfl⟩ := hin
          exact ih j0 (by omega) hj0 hw2
        · push_neg at hin
          have hwR : w ∈ R := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩, hin, hw2⟩
            rw [List.mem_toFinset, ins_eq C j hlt]
            exact hw
          refine val_mono C n hg _ x ?_ w (hpf w hwR).2
          intro q hq
          have hq' : q = pf w hwR := by simpa using hq
          rw [hxdef]
          exact Finset.mem_image.mpr ⟨⟨w, hwR⟩, Finset.mem_attach _ _, hq'.symm⟩
      rw [hab] at h2 key ⊢
      have ka := key a (by simp)
      have kb := key b (by simp)
      simp only [List.map_cons, List.map_nil] at h2 ⊢
      rcases hop with h | h
      · rw [h, and_eval, Bool.and_eq_true] at h2 ⊢
        exact ⟨ka h2.1, kb h2.2⟩
      · rw [h, or_eval, Bool.or_eq_true] at h2 ⊢
        exact h2.imp ka kb
  have hrootv := hval r hr hroot
  have hk : k < T.card := by
    by_contra hcon
    have h0 := hprom x (by rw [hxT]; omega) hxS
    unfold val at hrootv
    rw [h0] at hrootv
    exact Bool.false_ne_true hrootv
  omega

end PEqualNP.Outside.L_meta_693

theorem PEqualNP.Outside.L_meta_693 : ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card := by
  intro n k r S C Q ψ hg hprom hr hQ hpar hψ hout hroot
  exact PEqualNP.Outside.L_meta_693.main n k r S C Q ψ hg hprom hr hQ hpar hψ hout hroot
