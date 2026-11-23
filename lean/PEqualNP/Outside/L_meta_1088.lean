import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1088

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma two_inputs (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ a b : ℕ, ∀ j ∈ ins, j = a ∨ j = b := by
  match ins, h with
  | [], _ => exact ⟨0, 0, by simp⟩
  | [a], _ => exact ⟨a, a, by simp⟩
  | [a, b], _ => exact ⟨a, b, by simp⟩
  | _ :: _ :: _ :: _, h => simp at h

def Depends {n : ℕ} (gs : List Gate) (i : ℕ) (t : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ j, j ≠ t → x j = y j) ∧ val gs x i ≠ val gs y i

lemma components {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin n → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + gs.length ∧
      ∀ i t, Depends gs i t → label t = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, ?_⟩
    · simp [Finset.card_image_of_injective _ Fin.val_injective]
    · rintro i t ⟨x, y, hxy, hne⟩
      rw [val_nil, val_nil] at hne
      by_cases hi : i < n
      · simp only [hi, dite_true] at hne
        have he : (⟨i, hi⟩ : Fin n) = t := by
          by_contra h
          exact hne (hxy _ h)
        exact congrArg Fin.val he.symm
      · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hcount, hdep⟩ := ih (fun g' h => hg g' (by simp [h]))
    obtain ⟨a, b, hinputs⟩ := two_inputs g.inputs (hg g (by simp))
    let merge (k : ℕ) := if k = wire b then wire a else k
    have ha : merge (wire a) = wire a := by simp [merge]
    have hb : merge (wire b) = wire a := by simp [merge]
    refine ⟨merge ∘ label, fun i => if i = n + gs.length then wire a else merge (wire i),
      ?_, ?_⟩
    · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
        intro v hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
        by_cases he : label t = wire b
        · simp [he]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [List.length_append, List.length_cons, List.length_nil] at ⊢
      omega
    · rintro i t ⟨x, y, hxy, hne⟩
      rw [val_snoc, val_snoc] at hne
      by_cases hi : i = n + gs.length
      · simp only [hi, ite_true, Function.comp_apply] at hne ⊢
        have hd : val gs x a ≠ val gs y a ∨ val gs x b ≠ val gs y b := by
          by_contra! hh
          apply hne
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro j hj
          rcases hinputs j hj with rfl | rfl
          · exact hh.1
          · exact hh.2
        rcases hd with hd | hd
        · rw [hdep a t ⟨x, y, hxy, hd⟩, ha]
        · rw [hdep b t ⟨x, y, hxy, hd⟩, hb]
      · simp only [hi, ite_false, Function.comp_apply] at hne ⊢
        rw [hdep i t ⟨x, y, hxy, hne⟩]

lemma ofFn_get {n : ℕ} (x : List Bool) (hx : x.length = n) :
    List.ofFn (fun i : Fin n => x.getD i.val false) = x := by
  refine List.ext_getElem (by simp [hx]) ?_
  intro i hi hix
  have hilen : i < x.length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilen]

lemma eval_eq_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) = val C.gates x C.output := by
  rfl

lemma set_flip {n : ℕ} (x : List Bool) (hx : x.length = n) (t : Fin n) :
    List.ofFn (fun j : Fin n => if j = t then !(x.getD t.val false) else x.getD j.val false) =
      x.set t.val (!(x.getD t.val false)) := by
  apply List.ext_getElem
  · simp [hx]
  · intro i hi hix
    have hi' : i < n := by simpa [List.length_ofFn] using hi
    have hilen : i < x.length := by simpa [hx] using hi'
    rw [List.getElem_ofFn, List.getElem_set (h := hix)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilen, Option.getD_some]
    by_cases hEq : (⟨i, hi'⟩ : Fin n) = t
    · have hi_eq : i = t.val := congrArg Fin.val hEq
      simp [hEq, hi_eq]
    · have hine : i ≠ t.val := fun he => hEq (Fin.ext he)
      simp [hEq, hine]
      exact fun h => (hine h.symm).elim

lemma essential_depends {n : ℕ} (C : Circuit) (t : Fin n)
    (h : ∃ x : List Bool, x.length = n ∧
      C.eval x ≠ C.eval (x.set t.val (!(x.getD t.val false)))) :
    Depends C.gates C.output t := by
  obtain ⟨x, hx, hne⟩ := h
  let f : Fin n → Bool := fun j => x.getD j.val false
  let g : Fin n → Bool := fun j => if j = t then !(x.getD t.val false) else x.getD j.val false
  refine ⟨f, g, ?_, ?_⟩
  · intro j hj
    simp [f, g, hj]
  · have hf : List.ofFn f = x := ofFn_get x hx
    have hg : List.ofFn g = x.set t.val (!(x.getD t.val false)) := set_flip x hx t
    have h1 : val C.gates f C.output = C.eval x := by
      rw [← eval_eq_val, hf]
    have h2 : val C.gates g C.output = C.eval (x.set t.val (!(x.getD t.val false))) := by
      rw [← eval_eq_val, hg]
    rw [h1, h2]
    exact hne

lemma connectivity {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hess : ∀ i < n, ∃ x : List Bool, x.length = n ∧
      C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) :
    n ≤ C.size + 1 := by
  classical
  obtain ⟨label, wire, hcount, hdep⟩ := components (Finset.univ : Finset (Fin n)) C.gates hg
  have same : ∀ t : Fin n, label t = wire C.output := by
    intro t
    exact hdep C.output t (essential_depends C t (hess t.val t.isLt))
  have hsub : (Finset.univ : Finset (Fin n)).image label ⊆ {wire C.output} := by
    intro v hv
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr (same t)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hcount hc
  change n ≤ _ + C.gates.length at hcount
  simp only [Circuit.size]
  omega

end PEqualNP.Outside.L_meta_1088

open PEqualNP.Outside.L_meta_1088

theorem PEqualNP.Outside.L_meta_1088 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
        (∀ i < n, ∃ x : List Bool, x.length = n ∧
          C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) →
          n ≤ C.size + 1 := by
  intro n C hg hess
  exact connectivity C hg hess
