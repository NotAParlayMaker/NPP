import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_656

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem read_update {n : ℕ} (x : Fin n → Bool) (v : Fin n) (i : ℕ)
    (h : i ≠ v.val) :
    (List.ofFn (Function.update x v true)).getD i false = (List.ofFn x).getD i false := by
  by_cases hi : i < n
  · have hn : (⟨i, hi⟩ : Fin n) ≠ v := fun e => h (congrArg Fin.val e)
    simp [List.getD_eq_getElem?_getD, hi, Function.update_of_ne hn]
  · simp [List.getD_eq_getElem?_getD, hi]

private def Agrees {n : ℕ} (is : List ℕ) (x y : Fin n → Bool) : Prop :=
  ∀ i ∈ is, (List.ofFn x).getD i false = (List.ofFn y).getD i false

private theorem control {n : ℕ} (C : Circuit) (hc : FanInTwo C) (hs : C.size ≤ 1) :
    ∃ is : List ℕ, is.length ≤ 2 ∧ ∀ x y : Fin n → Bool,
      Agrees is x y → C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil =>
    exact ⟨[o], by simp, fun x y h => h o (by simp)⟩
  | cons g gs =>
    have hlen : gs.length = 0 := by simpa [Circuit.size] using hs
    have hnil : gs = [] := List.length_eq_zero_iff.mp hlen
    subst gs
    have hinputs : g.inputs.length ≤ 2 := (hc g (by simp)).2
    change ∃ is : List ℕ, is.length ≤ 2 ∧ ∀ x y : Fin n → Bool, Agrees is x y →
      ((List.ofFn x) ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)]).getD o false =
      ((List.ofFn y) ++ [g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false)]).getD o false
    by_cases ho : o < n
    · refine ⟨[o], by simp, fun x y h => ?_⟩
      rw [List.getD_append _ _ _ _ (by simpa using ho),
        List.getD_append _ _ _ _ (by simpa using ho)]
      exact h o (by simp)
    by_cases he : o = n
    · subst o
      refine ⟨g.inputs, hinputs, fun x y h => ?_⟩
      have hm : g.inputs.map (fun i => (List.ofFn x).getD i false) =
          g.inputs.map (fun i => (List.ofFn y).getD i false) := List.map_congr_left h
      simp only [List.getD_append_right _ _ _ _ (by simp : (List.ofFn x).length ≤ n),
        List.getD_append_right _ _ _ _ (by simp : (List.ofFn y).length ≤ n),
        List.length_ofFn, Nat.sub_self, List.getD_cons_zero, hm]
    · refine ⟨[], by decide, fun x y _ => ?_⟩
      have hsub : 1 ≤ o - n := by omega
      rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      rw [List.getD_eq_default _ _ (by simpa using hsub),
        List.getD_eq_default _ _ (by simpa using hsub)]

private def Changes {n : ℕ} (f : (Fin n → Bool) → Bool) (v : Fin n) : Prop :=
  ∃ x, f (Function.update x v true) ≠ f x

private theorem noOne {n t : ℕ} (hn : 3 < n) (ht : t ≤ 1) (f : (Fin n → Bool) → Bool)
    (h0 : Changes f ⟨0, by omega⟩) (h1 : Changes f ⟨1, by omega⟩)
    (h3 : Changes f ⟨3, hn⟩) : ¬ HasCircuitSize n f t := by
  rintro ⟨C, hf, hsize, he⟩
  obtain ⟨is, hlen, hctrl⟩ := control (n := n) C hf (hsize.trans ht)
  have hm (v : Fin n) (hv : Changes f v) : v.val ∈ is := by
    obtain ⟨x, hx⟩ := hv
    by_contra hnot
    exact hx (by
      rw [← he, ← he]
      apply hctrl
      intro j hj
      exact read_update x v j (fun heq => hnot (heq ▸ hj)))
  have hsub : ({0, 1, 3} : Finset ℕ) ⊆ is.toFinset := by
    intro i hi
    simp at hi
    rcases hi with rfl | rfl | rfl
    · exact List.mem_toFinset.mpr (hm _ h0)
    · exact List.mem_toFinset.mpr (hm _ h1)
    · exact List.mem_toFinset.mpr (hm _ h3)
  have h := Finset.card_le_card hsub
  have hu := (List.toFinset_card_le is).trans hlen
  have hc : ({0, 1, 3} : Finset ℕ).card = 3 := by decide
  omega

private def passenger (x : Fin 3 → Bool) : Bool := x 0 && x 1

private def shortCycle : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [5, 6]⟩], 7⟩

private theorem shortCycle_size : HasCircuitSize 5 (fun x : Fin 5 → Bool =>
    passenger (fun i : Fin 3 => x (Fin.castAdd 2 i)) ||
      (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1)) 3 := by
  refine ⟨shortCycle, ?_, by decide, ?_⟩
  · simp [FanInTwo, shortCycle]
  · decide +kernel

end PEqualNP.Outside.L_meta_656

open PEqualNP.Outside.L_meta_656 in
theorem PEqualNP.Outside.L_meta_656 : ¬ (∀ g : (Fin 3 → Bool) → Bool, (∀ x y : Fin 3 → Bool, (∀ i, x i = true → y i = true) → g x = true → g y = true) → g (fun _ : Fin 3 => false) = false → (∃ x : Fin 3 → Bool, g x = true) → (∃ x : Fin 3 → Bool, x 0 = true ∧ g x = false) → (∃ x : Fin 3 → Bool, x 1 = true ∧ g x = false) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3) || (x 3 && x 1)) s ↔ ((∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 2 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1)) s ↔ ((∃ t : ℕ, 5 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 3 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ (∃ t : ℕ, 2 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) t))) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 3 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 1)) s ↔ ((∃ t : ℕ, 6 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 5 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ (∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) t)))) := by
  intro h
  have hmono : ∀ x y : Fin 3 → Bool,
      (∀ i, x i = true → y i = true) → passenger x = true → passenger y = true := by
    intro x y hxy hx
    have hx' : x 0 = true ∧ x 1 = true := by simpa [passenger] using hx
    simpa [passenger] using And.intro (hxy 0 hx'.1) (hxy 1 hx'.2)
  have hthread := (h passenger hmono (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 3).2.1
  rcases hthread.mp shortCycle_size with ⟨t, ht, _⟩ | ⟨t, ht, hl | hr⟩ | ⟨t, ht, hs⟩
  · omega
  · apply noOne (by decide) (by omega) _ _ _ _ hl
    · exact ⟨fun i => i == 1, (fun h => Bool.noConfusion h)⟩
    · exact ⟨fun i => i == 0, (fun h => Bool.noConfusion h)⟩
    · exact ⟨fun i => i == 0, (fun h => Bool.noConfusion h)⟩
  · apply noOne (by decide) (by omega) _ _ _ _ hr
    · exact ⟨fun i => i == 1, (fun h => Bool.noConfusion h)⟩
    · exact ⟨fun i => i == 0, (fun h => Bool.noConfusion h)⟩
    · exact ⟨fun i => i == 1, (fun h => Bool.noConfusion h)⟩
  · apply noOne (by decide) (by omega) _ _ _ _ hs
    · exact ⟨fun i => i == 1, (fun h => Bool.noConfusion h)⟩
    · exact ⟨fun i => i == 0, (fun h => Bool.noConfusion h)⟩
    · exact ⟨fun i => i == 0, (fun h => Bool.noConfusion h)⟩
