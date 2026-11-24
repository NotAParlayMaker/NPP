import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3582

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def F (x1 : Fin 9 → Bool) : Bool :=
  x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))

def inp (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]

def tbl : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 64, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 5, 4, 18, 16, 4, 0, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 16, 4, 8, 1, 1, 10, 1, 5, 1, 8, 0, 0, 1, 40, 1, 65, 1, 129, 1, 257, 8, 1, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 0, 0, 1, 65, 1, 128, 1, 256, 128, 1, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 0, 0, 2, 130, 2, 256, 2, 257, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 0, 0, 4, 260, 32, 4, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 0, 0, 8, 9]

def wit (v : Fin 9) (u : Fin 10) (b : Bool) : Fin 9 → Bool :=
  fun i => Nat.testBit (tbl.getD (v.val * 20 + u.val * 2 + b.toNat) 0) i.val

theorem wit_ok : ∀ v : Fin 9, ∀ u : Fin 10, ∀ b : Bool, v ≠ 0 → v ≠ 2 → v.castSucc ≠ u →
    (inp (wit v u b)).getD u.val false = b ∧
      F (wit v u b) ≠ F (Function.update (wit v u b) v (!(wit v u b v))) := by
  decide

theorem single_ok : ∀ v : Fin 9, F (fun i => decide (i = v)) = false := by
  decide

theorem inp_getD (x : Fin 9 → Bool) (i : ℕ) :
    (inp x).getD i false = if h : i < 9 then x ⟨i, h⟩ else if i = 9 then (x 0 || x 2) else false := by
  unfold inp
  by_cases h : i < 9
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    simp only [List.length_ofFn, h, dite_false]
    by_cases h9 : i = 9
    · subst h9; simp
    · simp only [h9, ite_false]
      apply List.getD_eq_default
      simp; omega

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem prefix_getD (gs : List Gate) (X : List Bool) (i : ℕ) (hi : i < X.length) :
    (gs.foldl step X).getD i false = X.getD i false := by
  induction gs generalizing X with
  | nil => rfl
  | cons h t ih =>
    rw [List.foldl_cons, ih (step X h) (by simp [step]; omega)]
    unfold step
    rw [List.getD_append _ _ _ _ hi]

theorem len_one_eq {α : Type} (l : List α) (hl : l.length < 2) (a b : α) (ha : a ∈ l)
    (hb : b ∈ l) : a = b := by
  match l, hl with
  | [], _ => simp at ha
  | [c], _ => simp at ha hb; rw [ha, hb]

theorem agree (gs : List Gate) (X X' : List Bool) (v u : ℕ) (g : Gate) (c : Bool)
    (hlen : X.length = X'.length) (hX : ∀ i, i ≠ v → X.getD i false = X'.getD i false)
    (huv : u ≠ v) (hu : u < X.length) (hXu : X.getD u false = c)
    (hg : g.inputs = [v, u] ∨ g.inputs = [u, v])
    (hgop : (g.op = GateOp.and ∧ c = false) ∨ (g.op = GateOp.or ∧ c = true))
    (hgs : ∀ h ∈ gs, h = g ∨ ((h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧
      h.inputs.length ≤ 2 ∧
      (List.take (bif h.op.eval [false] then 1 else 2) h.inputs).contains v = false)) :
    (gs.foldl step X).length = (gs.foldl step X').length ∧
      ∀ i, i ≠ v → (gs.foldl step X).getD i false = (gs.foldl step X').getD i false := by
  induction gs generalizing X X' with
  | nil => exact ⟨hlen, hX⟩
  | cons h t ih =>
    simp only [List.foldl_cons]
    have hval : h.op.eval (h.inputs.map fun i => X.getD i false) =
        h.op.eval (h.inputs.map fun i => X'.getD i false) := by
      rcases hgs h (by simp) with rfl | ⟨hop, hl, hc⟩
      · have hXu' : X'.getD u false = c := by rw [← hX u huv]; exact hXu
        rcases hgop with ⟨ho, hc⟩ | ⟨ho, hc⟩ <;>
        rcases hg with hi | hi <;> rw [ho, hi] <;> subst hc <;>
          simp only [List.getD_eq_getElem?_getD] at hXu hXu' <;>
          simp [GateOp.eval, hXu, hXu']
      · rcases hop with ho | ho | ho
        · rw [ho] at hc ⊢
          congr 1
          apply List.map_congr_left
          intro i hi
          apply hX
          intro e; subst e
          simp [GateOp.eval, List.take_of_length_le hl] at hc
          exact hc hi
        · rw [ho] at hc ⊢
          congr 1
          apply List.map_congr_left
          intro i hi
          apply hX
          intro e; subst e
          simp [GateOp.eval, List.take_of_length_le hl] at hc
          exact hc hi
        · rw [ho] at hc ⊢
          match hh : h.inputs with
          | [] => rfl
          | a :: r =>
            rw [hh] at hc
            have ha : a ≠ v := by
              intro e; subst e; simp [GateOp.eval] at hc
            have hxa := hX a ha
            simp only [List.getD_eq_getElem?_getD] at hxa
            simp [GateOp.eval, hxa]
    apply ih
    · simp [step, hlen]
    · intro i hi
      unfold step
      by_cases hl : i < X.length
      · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ (by omega)]
        exact hX i hi
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hlen, hval]
    · simp [step]; omega
    · unfold step; rw [List.getD_append _ _ _ _ hu]; exact hXu
    · intro h' hh'; exact hgs h' (by simp [hh'])


theorem core (C : Circuit) (hC : FanInTwo C) (hF : ∀ x, C.eval (inp x) = F x) (v : Fin 9)
    (u : Fin 10) (hv0 : v ≠ 0) (hv2 : v ≠ 2) (hvu : v.castSucc ≠ u) (g : Gate) (c : Bool)
    (hgop : (g.op = GateOp.and ∧ c = false) ∨ (g.op = GateOp.or ∧ c = true))
    (hgin : g.inputs = [v.val, u.val] ∨ g.inputs = [u.val, v.val])
    (hfil : ∀ h ∈ C.gates,
      (List.take (bif h.op.eval [false] then 1 else 2) h.inputs).contains v.val = true → h = g) :
    False := by
  obtain ⟨hXu, hne⟩ := wit_ok v u c hv0 hv2 hvu
  by_cases hout : C.output = v.val
  · have h1 := hF (fun i => decide (i = v))
    rw [single_ok] at h1
    unfold Circuit.eval at h1
    rw [wires_eq, hout, prefix_getD _ _ _ (by simp [inp] <;> omega), inp_getD] at h1
    simp at h1
  · have hag := agree C.gates (inp (wit v u c))
      (inp (Function.update (wit v u c) v (!(wit v u c v)))) v.val u.val g c (by simp [inp])
      ?_ ?_ (by simp [inp] <;> omega) hXu hgin hgop ?_
    · apply hne
      rw [← hF, ← hF]
      unfold Circuit.eval
      rw [wires_eq, wires_eq]
      exact hag.2 _ hout
    · intro i hi
      rw [inp_getD, inp_getD]
      split_ifs with h1 h2
      · rw [Function.update_of_ne (show (⟨i, h1⟩ : Fin 9) ≠ v from fun e => hi (by rw [← e]))]
      · rw [Function.update_of_ne (show (0 : Fin 9) ≠ v from fun e => hv0 e.symm),
          Function.update_of_ne (show (2 : Fin 9) ≠ v from fun e => hv2 e.symm)]
      · rfl
    · intro e; apply hvu; ext; simp [e]
    · intro h hh
      by_cases hc : (List.take (bif h.op.eval [false] then 1 else 2) h.inputs).contains v.val = true
      · left; exact hfil h hh hc
      · right
        obtain ⟨hop, hl⟩ := hC h hh
        refine ⟨by simpa using hop, hl, by simpa using hc⟩

end PEqualNP.Outside.L_meta_3582

theorem PEqualNP.Outside.L_meta_3582 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) → ∀ (x5 : Fin (9 : ℕ)) (x6 : Fin (10 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) → x5 ≠ (2 : Fin (9 : ℕ)) → x5.castSucc ≠ x6 → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10.inputs = [↑x5, ↑x6] ∨ x10.inputs = [↑x6, ↑x5] → (2 : ℕ) ≤ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x5) x2.gates).length := by
  intro f C hC hF v u hv0 hv2 hvu g hgm hgop hgin
  by_contra hlt
  push Not at hlt
  have hfil : ∀ h ∈ C.gates,
      (List.take (bif h.op.eval [false] then 1 else 2) h.inputs).contains v.val = true → h = g := by
    intro h hh hc
    apply PEqualNP.Outside.L_meta_3582.len_one_eq _ hlt h g (List.mem_filter.2 ⟨hh, hc⟩)
      (List.mem_filter.2 ⟨hgm, ?_⟩)
    rcases hgop with ho | ho <;> rcases hgin with hi | hi <;>
      simp [ho, hi, PEqualNP.CircuitLowerBounds.GateOp.eval]
  rcases hgop with ho | ho
  · exact PEqualNP.Outside.L_meta_3582.core C hC (fun x => hF x) v u hv0 hv2 hvu g false
      (Or.inl ⟨ho, rfl⟩) hgin hfil
  · exact PEqualNP.Outside.L_meta_3582.core C hC (fun x => hF x) v u hv0 hv2 hvu g true
      (Or.inr ⟨ho, rfl⟩) hgin hfil
