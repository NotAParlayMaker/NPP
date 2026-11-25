import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepWire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepWire
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma op_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ (l1 l2 : List Bool), List.Forall₂ (fun a b => a = true → b = true) l1 l2 →
      op.eval l1 = true → op.eval l2 = true := by
  intro l1 l2 hrel
  rcases hop with rfl | rfl
  · induction hrel with
    | nil => intro h; exact h
    | cons hhd htl ih =>
      simp only [GateOp.eval, List.all_cons, Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      exact ⟨hhd h1, ih h2⟩
  · induction hrel with
    | nil => intro h; exact h
    | cons hhd htl ih =>
      simp only [GateOp.eval, List.any_cons, Bool.or_eq_true]
      rintro (h1 | h2)
      · exact Or.inl (hhd h1)
      · exact Or.inr (ih h2)

lemma map_forall2 {α : Type*} (f g : α → Bool) (l : List α)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    List.Forall₂ (fun a b => a = true → b = true) (l.map f) (l.map g) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma mono_core (n : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, ∃ S : Finset (Fin n), S.card ≤ W.card + gs.length ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) → ∀ w ∈ W,
        (gs.foldl stepWire (List.ofFn x)).getD w false = true →
          (gs.foldl stepWire (List.ofFn y)).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W
    refine ⟨Finset.univ.filter (fun i : Fin n => i.val ∈ W), ?_, ?_⟩
    · simp only [List.length_nil, add_zero]
      apply Finset.card_le_card_of_injOn (fun i => i.val)
      · intro i hi; simpa using hi
      · intro i _ j _ h; exact Fin.ext h
    · intro x y hxy w hw hval
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD] at hval ⊢
      by_cases hwn : w < n
      · have hx : (List.ofFn x)[w]? = some (x ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]; simp
        have hy : (List.ofFn y)[w]? = some (y ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]; simp
        rw [hx] at hval
        rw [hy]
        simp only [Option.getD_some] at hval ⊢
        exact hxy ⟨w, hwn⟩ (by simp [hw]) hval
      · rw [List.getElem?_eq_none (by simp; omega)] at hval
        simp at hval
  | append_singleton gs g ih =>
    intro W
    have hmono' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (by simp [hg'])
    have hg := hmono g (by simp)
    have key : ∀ (S : Finset (Fin n)) (W' : Finset ℕ),
        (∀ w ∈ W, w < n + gs.length → w ∈ W') →
        (n + gs.length ∈ W → ∀ k ∈ g.inputs, k ∈ W') →
        (∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) → ∀ w ∈ W',
          (gs.foldl stepWire (List.ofFn x)).getD w false = true →
            (gs.foldl stepWire (List.ofFn y)).getD w false = true) →
        ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) → ∀ w ∈ W,
          ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false = true →
            ((gs ++ [g]).foldl stepWire (List.ofFn y)).getD w false = true := by
      intro S W' hlow hin hval x y hxy w hw htrue
      have hv := hval x y hxy
      have hlx := foldl_len gs (List.ofFn x)
      have hly := foldl_len gs (List.ofFn y)
      simp only [List.length_ofFn] at hlx hly
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at htrue ⊢
      rw [step_getD, hlx] at htrue
      rw [step_getD, hly]
      split_ifs at htrue ⊢ with h1 h3
      · exact hv w (hlow w hw h1) htrue
      · subst h3
        refine op_eval_mono g.op hg.1 _ _ ?_ htrue
        exact map_forall2 _ _ g.inputs (fun k hk => hv k (hin hw k hk))
    by_cases hin : n + gs.length ∈ W
    · obtain ⟨S, hS, hval⟩ := ih hmono' (W.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, key S _ ?_ ?_ hval⟩
      · have h1 : (W.erase (n + gs.length) ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hin]
          have := List.toFinset_card_le g.inputs
          omega
        have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hin⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw hlt
        simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨by omega, hw⟩
      · intro _ k hk
        simp [hk]
    · obtain ⟨S, hS, hval⟩ := ih hmono' W
      refine ⟨S, ?_, key S W ?_ ?_ hval⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw _
        exact hw
      · intro h
        exact absurd h hin

def oneEachFn (u v : Fin 4) : Fin 8 → Bool :=
  fun i => decide (i.val = u.val ∨ i.val = 4 + v.val)

lemma ofFn_oneEachFn (u v : Fin 4) : List.ofFn (oneEachFn u v) = oneEach u v := by
  revert u v; decide

lemma need_four (S : Finset (Fin 8))
    (h : ∀ u v u' v' : Fin 4,
      (∀ i ∈ S, oneEachFn u v i = true → oneEachFn u' v' i = true) →
      (511 : ℕ).testBit (4 * u.val + v.val) = true →
      (511 : ℕ).testBit (4 * u'.val + v'.val) = true) :
    4 ≤ S.card := by
  have d0 : ∀ i : Fin 8, i ≠ 0 → oneEachFn 0 1 i = true → oneEachFn 3 1 i = true := by decide
  have d1 : ∀ i : Fin 8, i ≠ 1 → oneEachFn 1 1 i = true → oneEachFn 3 1 i = true := by decide
  have d2 : ∀ i : Fin 8, i ≠ 2 → oneEachFn 2 0 i = true → oneEachFn 3 0 i = true := by decide
  have d4 : ∀ i : Fin 8, i ≠ 4 → oneEachFn 2 0 i = true → oneEachFn 2 1 i = true := by decide
  have h0 : (0 : Fin 8) ∈ S := by
    by_contra hnot
    exact Bool.false_ne_true (h 0 1 3 1 (fun i hi h1 => d0 i (fun e => hnot (e ▸ hi)) h1) (by decide))
  have h1 : (1 : Fin 8) ∈ S := by
    by_contra hnot
    exact Bool.false_ne_true (h 1 1 3 1 (fun i hi h1 => d1 i (fun e => hnot (e ▸ hi)) h1) (by decide))
  have h2 : (2 : Fin 8) ∈ S := by
    by_contra hnot
    exact Bool.false_ne_true (h 2 0 3 0 (fun i hi h1 => d2 i (fun e => hnot (e ▸ hi)) h1) (by decide))
  have h4 : (4 : Fin 8) ∈ S := by
    by_contra hnot
    exact Bool.false_ne_true (h 2 0 2 1 (fun i hi h1 => d4 i (fun e => hnot (e ▸ hi)) h1) (by decide))
  have hsub : ({(0 : Fin 8), 1, 2, 4} : Finset (Fin 8)) ⊆ S := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({(0 : Fin 8), 1, 2, 4} : Finset (Fin 8)).card = 4 := by decide
  have := Finset.card_le_card hsub
  omega

def witness : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 1] }
      , { op := GateOp.and, inputs := [2, 4] }
      , { op := GateOp.or, inputs := [8, 9] } ]
    output := 10 }

end PEqualNP.Outside.L_meta_5600

theorem PEqualNP.Outside.L_meta_5600 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (511 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (511 : ℕ).testBit (4 * u.val + v.val)) 2 := by
  constructor
  · refine ⟨PEqualNP.Outside.L_meta_5600.witness, ?_, le_rfl, ?_⟩
    · simp [PEqualNP.Outside.L_meta_5600.witness, PEqualNP.MetaComplexity.Monotone2]
    · decide
  · rintro ⟨C, hC, hsize, hrep⟩
    have hmono : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have ⟨hop, hlen⟩ := hC g hg
      exact ⟨by simpa using hop, hlen⟩
    obtain ⟨S, hS, hval⟩ := PEqualNP.Outside.L_meta_5600.mono_core 8 C.gates hmono {C.output}
    have h4 : 4 ≤ S.card := by
      apply PEqualNP.Outside.L_meta_5600.need_four S
      intro u v u' v' hle huv
      have hev1 : (C.gates.foldl PEqualNP.Outside.L_meta_5600.stepWire (List.ofFn (PEqualNP.Outside.L_meta_5600.oneEachFn u v))).getD C.output false = true := by
        rw [PEqualNP.Outside.L_meta_5600.ofFn_oneEachFn]
        exact (hrep u v).trans huv
      have hev2 := hval _ _ hle C.output (by simp) hev1
      rw [PEqualNP.Outside.L_meta_5600.ofFn_oneEachFn] at hev2
      exact (hrep u' v').symm.trans hev2
    simp only [Finset.card_singleton] at hS
    unfold PEqualNP.CircuitLowerBounds.Circuit.size at hsize
    omega
