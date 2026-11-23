import PEqualNP.Defs
import Mathlib

-- Mythos 6 et Codex Betelgeuse

namespace PEqualNP.Outside.L_meta_782_aux
namespace WhenTrue

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_before (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getElem?_append_left hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) :
    (run gs x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun w =>
        if w < x.length + j then (run gs x).getD w false else false) := by
  induction gs generalizing x j with
  | nil => simp at hg
  | cons a gs ih =>
    cases j with
    | zero =>
      have hag : a = g := by simpa using hg
      subst a
      let v := g.op.eval (g.inputs.map fun i => x.getD i false)
      change (run gs (x ++ [v])).getD (x.length + 0) false = _
      rw [run_before gs (x ++ [v]) _ (by simp)]
      have hread : (fun w => if w < x.length + 0 then
          (run (g :: gs) x).getD w false else false) =
          (fun w => x.getD w false) := by
        funext w
        by_cases hw : w < x.length
        · simp only [Nat.add_zero, ite_eq_left hw]
          exact run_before (g :: gs) x w hw
        · simp [hw]
      rw [hread]
      simp [v]
    | succ j =>
      have htail : gs[j]? = some g := by simpa using hg
      let y := x ++ [a.op.eval (a.inputs.map fun i => x.getD i false)]
      have hy : y.length = x.length + 1 := by simp [y]
      have h := ih y j htail
      have hlen : y.length + j = x.length + (j + 1) := by omega
      rw [hlen] at h
      exact h

lemma eval_mono (g : Gate) (f h : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfh : ∀ w ∈ g.inputs, f w = true → h w = true)
    (hf : g.op.eval (g.inputs.map f) = true) :
    g.op.eval (g.inputs.map h) = true := by
  rcases hop with ha | ho
  · simp only [ha, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hf ⊢
    intro w hw
    exact hfh w hw (hf w hw)
  · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hf ⊢
    rcases hf with ⟨w, hw, hfw⟩
    exact ⟨w, hw, hfh w hw hfw⟩

lemma append_mono (x y : List Bool) (a b : Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (x ++ [a]).getD i false = true → (y ++ [b]).getD i false = true := by
  intro i hi
  by_cases hix : i < x.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hix] at hi
    have hiy : i < y.length := by omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiy] using hxy i hi
  · have hxle : x.length ≤ i := by omega
    have hyle : y.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hxle] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hyle]
    rw [← hlen]
    by_cases he : i = x.length
    · subst i
      simpa using hab (by simpa using hi)
    · have hsub : 1 ≤ i - x.length := by omega
      have hn : ([a] : List Bool)[i - x.length]? = none :=
        List.getElem?_eq_none (by simpa using hsub)
      simp [hn] at hi

lemma run_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih (by intro a ha; exact hgs a (List.mem_cons_of_mem _ ha))
    · simp [hlen]
    · exact append_mono x y _ _ hlen hxy
        (eval_mono g _ _ (hgs g (by simp)) (by intro w _; exact hxy w))

lemma circuit_mono (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ i, (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  apply run_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hin : i < n
  · simp [hin] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · simp [hin] at hi

def inputsOf (C : Circuit) (j : ℕ) : List ℕ :=
  match C.gates[j]? with
  | some g => g.inputs
  | none => []

def allInputs (C : Circuit) (Q : Finset ℕ) : Finset ℕ :=
  Q.biUnion (fun j => (inputsOf C j).toFinset)

def boundary (C : Circuit) (n : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  allInputs C Q \ Q.image (fun j => n + j)

lemma boundary_card (C : Circuit) (n r : ℕ) (Q : Finset ℕ)
    (hC : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hr : r ∈ Q)
    (hp : ∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧
      ∃ g : Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) :
    (boundary C n Q).card ≤ Q.card + 1 := by
  have htotal : (allInputs C Q).card ≤ Q.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro j _
    cases hg : C.gates[j]? with
    | none => simp [inputsOf, hg]
    | some g =>
      simpa [inputsOf, hg, hC g (List.mem_of_getElem? hg)] using
        List.toFinset_card_le g.inputs
  have hsub : (Q.erase r).image (fun j => n + j) ⊆
      allInputs C Q ∩ Q.image (fun j => n + j) := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    rcases Finset.mem_erase.mp hj with ⟨hjr, hjQ⟩
    rcases hp j hjQ hjr with ⟨j', hj'Q, _, g, hg, hin⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_biUnion.mpr
      exact ⟨j', hj'Q, by simp [inputsOf, hg, hin]⟩
    · exact Finset.mem_image.mpr ⟨j, hjQ, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (by
    intro a b hab
    exact Nat.add_left_cancel hab)] at hcard
  have herase := Finset.card_erase_add_one hr
  have hsplit := Finset.card_sdiff_add_card_inter
    (allInputs C Q) (Q.image (fun j => n + j))
  change (allInputs C Q \ Q.image (fun j => n + j)).card ≤ _
  omega

lemma circuit_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun w => if w < n + j then
        (C.wires (List.ofFn x)).getD w false else false) := by
  simpa only [List.length_ofFn, run, Circuit.wires] using run_gate C.gates (List.ofFn x) j g hg

lemma label_sound (C : Circuit) (n : ℕ) (Q : Finset ℕ) (ψ : ℕ → Bool)
    (x : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hsize : ∀ j ∈ Q, j < C.size)
    (hlabel : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map fun w => if w < n + j then ψ w else false))
    (hout : ∀ w ∈ boundary C n Q, ψ w = true →
      (C.wires (List.ofFn x)).getD w false = true) :
    ∀ j ∈ Q, ψ (n + j) = true →
      (C.wires (List.ofFn x)).getD (n + j) false = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hψj
    have hjlen : j < C.gates.length := hsize j hj
    let g : Gate := C.gates[j]'hjlen
    have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlen
    rw [circuit_gate C n x j g hg]
    apply eval_mono g (fun w => if w < n + j then ψ w else false)
      (fun w => if w < n + j then (C.wires (List.ofFn x)).getD w false else false)
      (hC g (List.mem_of_getElem? hg))
    · intro w hw hψw
      by_cases hlt : w < n + j
      · simp only [ite_eq_left hlt] at hψw ⊢
        by_cases hwQ : w ∈ Q.image (fun i => n + i)
        · rcases Finset.mem_image.mp hwQ with ⟨i, hiQ, hwi⟩
          have hij : i < j := by omega
          subst w
          exact ih i hij hiQ hψw
        · apply hout w _ hψw
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, hwQ⟩
          exact Finset.mem_biUnion.mpr ⟨j, hj, by simp [inputsOf, hg, hw]⟩
      · simp [hlt] at hψw
    · exact (hlabel j hj g hg).symm.trans hψj

lemma true_bound :
  ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card := by
  classical
  intro n k r S C Q ψ hC hpromise hr hsize hparent hlabel hout hroot
  let B := (boundary C n Q).filter (fun w => ψ w = true)
  have hex : ∀ w : {w // w ∈ B}, ∃ p : Fin n,
      p ∉ S ∧ (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w.val false = true := by
    intro w
    have hw := Finset.mem_filter.mp w.property
    have hneq : ∀ j ∈ Q, w.val ≠ n + j := by
      intro j hj he
      apply (Finset.mem_sdiff.mp hw.1).2
      exact Finset.mem_image.mpr ⟨j, hj, he.symm⟩
    have hnsub := hout w.val hneq hw.2
    rcases Finset.not_subset.mp hnsub with ⟨p, hp, hpS⟩
    exact ⟨p, hpS, (Finset.mem_filter.mp hp).2⟩
  choose f hf using hex
  let T : Finset (Fin n) := B.attach.image f
  let x : Fin n → Bool := fun p => decide (p ∈ T)
  have hTcard : T.card ≤ Q.card + 1 := by
    calc
      T.card ≤ B.attach.card := Finset.card_image_le
      _ = B.card := Finset.card_attach
      _ ≤ (boundary C n Q).card := Finset.card_filter_le _ _
      _ ≤ Q.card + 1 := boundary_card C n r Q
        (fun g hg => (hC g hg).2) hr hparent
  have hmiss : ∀ p ∈ T, p ∉ S := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨w, _, hwp⟩
    rw [← hwp]
    exact (hf w).1
  have hext : ∀ w ∈ boundary C n Q, ψ w = true →
      (C.wires (List.ofFn x)).getD w false = true := by
    intro w hw hψ
    have hwB : w ∈ B := Finset.mem_filter.mpr ⟨hw, hψ⟩
    let a : {w // w ∈ B} := ⟨w, hwB⟩
    have hpT : f a ∈ T := Finset.mem_image.mpr ⟨a, by simp, rfl⟩
    apply circuit_mono C (fun g hg => (hC g hg).1) n
      (fun q : Fin n => decide (q = f a)) x _ w (hf a).2
    intro q hq
    have hqp : q = f a := by simpa using hq
    subst q
    simpa [x] using hpT
  have hone := label_sound C n Q ψ x (fun g hg => (hC g hg).1)
    hsize hlabel hext r hr hroot
  by_contra hgoal
  have hTle : T.card ≤ k := by omega
  have hweight : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k := by
    have heq : Finset.univ.filter (fun q : Fin n => x q = true) = T := by
      ext p
      simp [x]
    rwa [heq]
  have hzero := hpromise x hweight (by
    intro q hq
    have hnT : q ∉ T := fun hqT => (hmiss q hqT) hq
    simp [x, hnT])
  rw [hone] at hzero
  contradiction

end WhenTrue
namespace WhenFalse

lemma frontier_bound {α : Type} [DecidableEq α] (L : ℕ → Finset α) (Q : Finset ℕ)
    (step : ∀ j ∈ Q, ∃ B : Finset ℕ,
      B.card ≤ 2 ∧ (∀ b ∈ B, b < j) ∧ L j ⊆ B.biUnion L ∧
      ∀ b ∈ B, b ∉ Q → (L b).card ≤ 1)
    (F : Finset ℕ) (leaves : ∀ w ∈ F, w ∉ Q → (L w).card ≤ 1) :
    (F.biUnion L).card ≤ Q.card + F.card := by
  induction Q using Finset.induction_on_max generalizing F with
  | empty =>
    simp only [Finset.card_empty, Nat.zero_add]
    induction F using Finset.induction_on with
    | empty => simp
    | @insert a F ha ih =>
      rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
      have hb := Finset.card_union_le (L a) (F.biUnion L)
      have hc := leaves a (by simp) (by simp)
      have hd := ih (fun w hw hn => leaves w (by simp [hw]) hn)
      omega
  | insert j Q hmax ih =>
    have hj : j ∉ Q := by
      intro h
      exact Nat.lt_irrefl j (hmax j h)
    have st : ∀ k ∈ Q, ∃ B : Finset ℕ,
        B.card ≤ 2 ∧ (∀ b ∈ B, b < k) ∧ L k ⊆ B.biUnion L ∧
        ∀ b ∈ B, b ∉ Q → (L b).card ≤ 1 := by
      intro k hk
      obtain ⟨B, hB, hlt, hcov, hleaf⟩ := step k (by simp [hk])
      refine ⟨B, hB, hlt, hcov, ?_⟩
      intro b hb hbq
      apply hleaf b hb
      simp only [Finset.mem_insert, not_or]
      exact ⟨by have := hlt b hb; have := hmax k hk; omega, hbq⟩
    by_cases hjF : j ∈ F
    · obtain ⟨B, hB, hlt, hcov, hleaf⟩ := step j (by simp)
      let G := F.erase j ∪ B
      have lg : ∀ w ∈ G, w ∉ Q → (L w).card ≤ 1 := by
        intro w hw hn
        rcases Finset.mem_union.mp hw with hw | hw
        · have hw' := Finset.mem_erase.mp hw
          apply leaves w hw'.2
          simpa only [Finset.mem_insert, not_or] using And.intro hw'.1 hn
        · apply hleaf w hw
          simp only [Finset.mem_insert, not_or]
          exact ⟨by have := hlt w hw; omega, hn⟩
      have cover : F.biUnion L ⊆ G.biUnion L := by
        intro p hp
        obtain ⟨w, hw, hp⟩ := Finset.mem_biUnion.mp hp
        by_cases hwj : w = j
        · subst w
          obtain ⟨b, hb, hp⟩ := Finset.mem_biUnion.mp (hcov hp)
          exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_union_right _ hb, hp⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwj, hw⟩), hp⟩
      have bound := ih st G lg
      have hc := Finset.card_le_card cover
      have hG : G.card ≤ (F.erase j).card + B.card := Finset.card_union_le _ _
      have he := Finset.card_erase_add_one hjF
      rw [Finset.card_insert_of_notMem hj]
      omega
    · have lf : ∀ w ∈ F, w ∉ Q → (L w).card ≤ 1 := by
        intro w hw hn
        apply leaves w hw
        simp only [Finset.mem_insert, not_or]
        exact ⟨by intro h; subst w; exact hjF hw, hn⟩
      have bound := ih st F lf
      rw [Finset.card_insert_of_notMem hj]
      omega

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons a gs ih =>
    simp only [run, List.foldl_cons]
    change (run gs _).length = _
    rw [ih]
    simp
    omega

lemma run_get_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons a gs ih =>
    simp only [run, List.foldl_cons]
    change (run gs _).getD i false = _
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_get_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) :
    (run gs x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun w =>
        if w < x.length + j then (run gs x).getD w false else false) := by
  induction gs generalizing x j with
  | nil => simp at hg
  | cons a gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst g
      simp only [Nat.add_zero]
      have hleft : (run (a :: gs) x).getD x.length false =
          a.op.eval (a.inputs.map fun i => x.getD i false) := by
        change (run gs (x ++ [_])).getD x.length false = _
        rw [run_get_input _ _ _ (by simp)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hleft]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases h : w < x.length
      · rw [ite_eq_left h, run_get_input _ _ _ h]
      · simp [h]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hg
      have h := ih (x ++ [a.op.eval (a.inputs.map fun i => x.getD i false)]) j hg
      have he : (x ++ [a.op.eval (a.inputs.map fun i => x.getD i false)]).length + j =
          x.length + (j + 1) := by simp; omega
      simpa only [he, run, List.foldl_cons] using h

def support (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true

lemma support_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    (support n C w).card ≤ 1 := by
  have hsub : support n C w ⊆ {⟨w, hw⟩} := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    change (run C.gates _).getD w false = true at hp'
    rw [run_get_input _ _ _ (by simpa using hw)] at hp'
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_eq_left,
      Option.getD_some, decide_eq_true_eq] at hp'
    simpa using hp'.symm
  simpa using Finset.card_le_card hsub

lemma support_gate (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (p : Fin n) :
    (p ∈ support n C (n + j)) ↔
      g.op.eval (g.inputs.map fun w =>
        if w < n + j then decide (p ∈ support n C w) else false) = true := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  have h := run_get_gate C.gates
    (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
  simp only [List.length_ofFn] at h
  change (_ = true) ↔ _
  rw [show C.wires (List.ofFn (fun q : Fin n => decide (q = p))) =
    run C.gates (List.ofFn (fun q : Fin n => decide (q = p))) from rfl]
  rw [h]
  simp

lemma binary_cover {α : Type} [DecidableEq α] (L : ℕ → Finset α)
    (ψ : ℕ → Bool) (u a b : ℕ) (op : GateOp) (hmono : op = .and ∨ op = .or)
    (hlabel : op.eval [if a < u then ψ a else false, if b < u then ψ b else false] = false)
    (hvalue : ∀ p ∈ L u,
      op.eval [if a < u then decide (p ∈ L a) else false,
        if b < u then decide (p ∈ L b) else false] = true) :
    L u ⊆ (({a, b} : Finset ℕ).filter fun w => w < u ∧ ψ w = false).biUnion L := by
  intro p hp
  have hv := hvalue p hp
  have h : (a < u ∧ ψ a = false ∧ p ∈ L a) ∨
      (b < u ∧ ψ b = false ∧ p ∈ L b) := by
    rcases hmono with rfl | rfl
    all_goals
      by_cases ha : a < u <;> by_cases hb : b < u <;>
        cases hpa : ψ a <;> cases hpb : ψ b <;>
        simp_all [GateOp.eval]
  rcases h with h | h
  · exact Finset.mem_biUnion.mpr ⟨a, by simp [h.1, h.2.1], h.2.2⟩
  · exact Finset.mem_biUnion.mpr ⟨b, by simp [h.1, h.2.1], h.2.2⟩

lemma count_support (n r : ℕ) (S : Finset (Fin n)) (C : Circuit)
    (Q : Finset ℕ) (ψ : ℕ → Bool)
    (hmono : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hr : r ∈ Q)
    (hgood : ∀ j ∈ Q, j < C.size ∧ support n C (n + j) ⊆ S ∧
      2 ≤ (support n C (n + j)).card)
    (hclosed : ∀ j ∈ Q, ∀ j' : ℕ, j' < j →
      (∃ g : Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
      support n C (n + j') ⊆ S → 2 ≤ (support n C (n + j')).card → j' ∈ Q)
    (hlabel : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map fun w => if w < n + j then ψ w else false))
    (houtside : ∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → support n C w ⊆ S)
    (hroot : ψ (n + r) = false) : (support n C (n + r)).card ≤ Q.card + 1 := by
  classical
  let L := support n C
  let P := (Q.image fun j => n + j).filter fun w => ψ w = false
  have memP : ∀ w, w ∈ P ↔ (∃ j ∈ Q, n + j = w) ∧ ψ w = false := by
    intro w
    simp [P]
  have step : ∀ u ∈ P, ∃ B : Finset ℕ,
      B.card ≤ 2 ∧ (∀ b ∈ B, b < u) ∧ L u ⊆ B.biUnion L ∧
      ∀ b ∈ B, b ∉ P → (L b).card ≤ 1 := by
    intro u hu
    obtain ⟨⟨j, hj, rfl⟩, hψ⟩ := (memP u).mp hu
    have hjlt : j < C.gates.length := (hgood j hj).1
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := by simp [g, hjlt]
    have hgm : g ∈ C.gates := List.getElem_mem _
    obtain ⟨hm, hlen⟩ := hmono g hgm
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    let B := ({a, b} : Finset ℕ).filter fun w => w < n + j ∧ ψ w = false
    have hB : ∀ w, w ∈ B ↔ (w = a ∨ w = b) ∧ w < n + j ∧ ψ w = false := by
      intro w
      simp [B]
    refine ⟨B, ?_, ?_, ?_, ?_⟩
    · have hpair : ({a, b} : Finset ℕ).card ≤ 2 := by
        by_cases h : a = b <;> simp [h]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hpair
    · intro w hw
      exact ((hB w).mp hw).2.1
    · apply binary_cover L ψ (n + j) a b g.op hm
      · have hh := hlabel j hj g hg
        simpa only [hab, List.map_cons, List.map_nil, hψ] using hh.symm
      · intro p hp
        have hh := (support_gate n C j g hg p).mp hp
        simpa only [hab, List.map_cons, List.map_nil] using hh
    · intro w hw hnot
      obtain ⟨hwab, hwlt, hwψ⟩ := (hB w).mp hw
      by_cases hwn : w < n
      · exact support_input n C w hwn
      · have houtside' : ∀ k ∈ Q, w ≠ n + k := by
          intro k hk he
          apply hnot
          exact (memP w).mpr ⟨⟨k, hk, he.symm⟩, hwψ⟩
        have hwS : L w ⊆ S := houtside w houtside' hwψ
        by_contra hcard
        have hwcard : 2 ≤ (L w).card := by omega
        have he : n + (w - n) = w := by omega
        have hwj : w - n < j := by omega
        have hmem : w - n ∈ Q := hclosed j hj (w - n) hwj
          ⟨g, hg, by rw [he, hab]; simpa using hwab⟩
          (by simpa only [he] using hwS) (by simpa only [he] using hwcard)
        exact houtside' (w - n) hmem he.symm
  have hpr : n + r ∈ P := (memP _).mpr ⟨⟨r, hr, rfl⟩, hroot⟩
  have hbound := frontier_bound L P step {n + r} (by
    intro w hw hn
    have he : w = n + r := by simpa using hw
    subst w
    exact False.elim (hn hpr))
  have hc : P.card ≤ Q.card := le_trans
    (Finset.card_le_card (Finset.filter_subset _ _)) (Finset.card_image_le)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hbound
  exact le_trans hbound (Nat.add_le_add_right hc 1)

end WhenFalse
open PEqualNP.CircuitLowerBounds
open WhenFalse (support)

def gatesFor (n : Nat) (C : Circuit) (S : Finset (Fin n)) : Finset Nat :=
  (Finset.range C.size).filter fun j => support n C (n+j) ⊆ S ∧ 2 ≤ (support n C (n+j)).card

def depends (n : Nat) (C : Circuit) (P : Finset Nat) (a b : Nat) : Prop :=
  a ∈ P ∧ b ∈ P ∧ a < b ∧ ∃ g : Gate, C.gates[b]? = some g ∧ n+a ∈ g.inputs

noncomputable def mark (n : Nat) (C : Circuit) (S : Finset (Fin n)) (Q : Finset Nat) (w : Nat) : Bool :=
  if n ≤ w ∧ w-n ∈ Q then
    match C.gates[w-n]? with
    | none => false
    | some g => g.op.eval (g.inputs.map fun b => if _h : b < w then mark n C S Q b else false)
  else decide (¬ support n C w ⊆ S)
termination_by w

lemma private_bound (n r k d : Nat) (C : Circuit) (S : Finset (Fin n))
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hr : r ∈ gatesFor n C S) (dk : d ≤ k) (ds : d+1 ≤ (support n C (n+r)).card)
    (promise : ∀ x : Fin n → Bool, (Finset.univ.filter fun q => x q = true).card ≤ k →
      (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n+r) false = false) :
    d ≤ (gatesFor n C S).card := by
  classical
  let P := gatesFor n C S
  let R := depends n C P
  let Q := P.filter fun j => Relation.ReflTransGen R j r
  let ψ := mark n C S Q
  have rQ : r ∈ Q := Finset.mem_filter.mpr ⟨hr, Relation.ReflTransGen.refl⟩
  have sub : Q ⊆ P := Finset.filter_subset _ _
  have good (j) (hj : j ∈ Q) :
      j < C.size ∧ support n C (n+j) ⊆ S ∧ 2 ≤ (support n C (n+j)).card := by
    have t := Finset.mem_filter.mp (sub hj)
    exact ⟨Finset.mem_range.mp t.1, t.2⟩
  have parent (j) (hj : j ∈ Q) (hne : j ≠ r) :
      ∃ b ∈ Q, j < b ∧ ∃ g : Gate, C.gates[b]? = some g ∧ n+j ∈ g.inputs := by
    have hpath : Relation.ReflTransGen R j r := (Finset.mem_filter.mp hj).2
    obtain h | ⟨b,e,eb⟩ := hpath.cases_head
    · exact (hne h).elim
    · exact ⟨b,Finset.mem_filter.mpr ⟨e.2.1,eb⟩,e.2.2⟩
  have child (j) (hj : j ∈ Q) (a) (ha : a < j)
      (e : ∃ g : Gate, C.gates[j]? = some g ∧ n+a ∈ g.inputs)
      (hs : support n C (n+a) ⊆ S) (hc : 2 ≤ (support n C (n+a)).card) : a ∈ Q := by
    have ap : a ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans ha (good j hj).1),hs,hc⟩
    have rel : R a j := ⟨ap,sub hj,ha,e⟩
    exact Finset.mem_filter.mpr ⟨ap, Relation.ReflTransGen.head rel (Finset.mem_filter.mp hj).2⟩
  have lab (j) (hj : j ∈ Q) (g : Gate) (hg : C.gates[j]? = some g) :
      ψ (n+j) = g.op.eval (g.inputs.map fun w => if w < n+j then ψ w else false) := by
    change mark n C S Q (n+j) = _
    rw [mark]
    simp [hj, hg, ψ]
  have outside (w) (hw : ∀ j ∈ Q, w ≠ n+j) : ψ w = decide (¬ support n C w ⊆ S) := by
    have hn : ¬ (n ≤ w ∧ w-n ∈ Q) := by
      rintro ⟨hle,hm⟩
      exact hw (w-n) hm (by omega)
    change mark n C S Q w = _
    rw [mark,ite_eq_right hn]
  have cardQ : Q.card ≤ (gatesFor n C S).card := Finset.card_le_card sub
  cases val : ψ (n+r) with
  | false =>
    have h := WhenFalse.count_support n r S C Q ψ hC rQ good child lab
      (fun w hw h => by rw [outside w hw] at h; simpa using h) val
    omega
  | true =>
    have h := WhenTrue.true_bound n k r S C Q ψ hC promise rQ
      (fun j hj => (good j hj).1) parent lab
      (fun w hw h => by rw [outside w hw] at h; exact of_decide_eq_true h) val
    omega

end PEqualNP.Outside.L_meta_782_aux

open PEqualNP.Outside.L_meta_782_aux in
theorem PEqualNP.Outside.L_meta_782 :
∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c inter many hC inside promise dk dc
  let Q := fun i => gatesFor n C (S i)
  have each (i : Fin m) : c i ≤ (Q i).card := by
    have cnt : 2 ≤ (WhenFalse.support n C (o i)).card := many i
    have lo : n ≤ o i := by
      by_contra! h
      have := WhenFalse.support_input n C (o i) h
      omega
    have hi : o i < n+C.size := by
      by_contra! h
      have empty : WhenFalse.support n C (o i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        rw [List.getD_eq_default] at hp'
        · contradiction
        · have len := WhenFalse.run_length C.gates (List.ofFn (fun b : Fin n => decide (b = p)))
          simp only [List.length_ofFn] at len
          change (WhenFalse.run C.gates _).length ≤ o i
          change o i ≥ n + C.gates.length at h
          omega
      rw [empty, Finset.card_empty] at cnt
      omega
    let r := o i - n
    have e : n + r = o i := by dsimp [r]; omega
    have fits : WhenFalse.support n C (o i) ⊆ S i :=
      fun p hp => inside i p (Finset.mem_filter.mp hp).2
    have hr : r ∈ gatesFor n C (S i) := by
      apply Finset.mem_filter.mpr
      rw [e]
      refine ⟨Finset.mem_range.mpr ?_,fits,cnt⟩
      omega
    exact private_bound n r k (c i) C (S i) hC hr (dk i) (by rw [e]; exact dc i)
      (by rw [e]; exact promise i)
  have disj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint Q := by
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro g hi hj
    have a := (Finset.mem_filter.mp hi).2
    have b := (Finset.mem_filter.mp hj).2
    have subset : WhenFalse.support n C (n+g) ⊆ S i ∩ S j :=
      fun k hk => Finset.mem_inter.mpr ⟨a.1 hk,b.1 hk⟩
    have h := Finset.card_le_card subset
    have h' := inter i j ne
    have h'' := a.2
    omega
  calc
    ∑ i, c i ≤ ∑ i, (Q i).card := Finset.sum_le_sum fun i _ => each i
    _ = (Finset.univ.biUnion Q).card := (Finset.card_biUnion disj).symm
    _ ≤ (Finset.range C.size).card := Finset.card_le_card (by
      intro j hj
      obtain ⟨i,_,h⟩ := Finset.mem_biUnion.mp hj
      exact (Finset.mem_filter.mp h).1)
    _ = C.size := Finset.card_range _
