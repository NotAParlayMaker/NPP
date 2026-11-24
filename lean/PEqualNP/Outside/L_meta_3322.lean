import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322_aux
open CircuitLowerBounds

private def remapWire (σ : Equiv.Perm (Fin 14)) (k : ℕ) : ℕ :=
  if hk : k < 14 then (σ ⟨k, hk⟩).val else k

private theorem remapWire_input (σ : Equiv.Perm (Fin 14)) (i : Fin 14) :
    remapWire σ i.val = (σ i).val := by
  simp [remapWire, i.isLt]

private theorem remapWire_lt (σ : Equiv.Perm (Fin 14)) (k n : ℕ) (hn : 14 ≤ n) :
    remapWire σ k < n ↔ k < n := by
  unfold remapWire
  split
  · rename_i hk
    have hσ := (σ ⟨k, hk⟩).isLt
    omega
  · rfl

private theorem remapWire_injective (σ : Equiv.Perm (Fin 14)) :
    Function.Injective (remapWire σ) := by
  intro a b h
  by_cases ha : a < 14 <;> by_cases hb : b < 14
  · have he : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext (by simpa [remapWire, ha, hb] using h)
    exact congrArg Fin.val (σ.injective he)
  · have hh := (σ ⟨a, ha⟩).isLt
    simp only [remapWire, dite_eq_left ha, dite_eq_right hb] at h
    omega
  · have hh := (σ ⟨b, hb⟩).isLt
    simp only [remapWire, dite_eq_right ha, dite_eq_left hb] at h
    omega
  · simpa [remapWire, ha, hb] using h

private def remapSecond (σ : Equiv.Perm (Fin 14)) (i : Fin 15) : Fin 15 :=
  ⟨remapWire σ i.val, (remapWire_lt σ i.val 15 (by decide)).2 i.isLt⟩

private theorem remapSecond_val (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (remapSecond σ i).val = if i < (14 : Fin 15) then (σ (Fin.ofNat 14 i.val)).val else 14 := by
  change remapWire σ i.val = if i < (14 : Fin 15) then _ else _
  have htest : i < (14 : Fin 15) ↔ i.val < 14 := by rfl
  rw [if_congr htest rfl rfl]
  by_cases hi : i.val < 14
  · have he : Fin.ofNat 14 i.val = ⟨i.val, hi⟩ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt hi]
    rw [ite_eq_left hi, he]
    exact remapWire_input σ ⟨i.val, hi⟩
  · have hlt := i.isLt
    have he : i.val = 14 := by omega
    rw [ite_eq_right hi, remapWire, dite_eq_right hi, he]

private def WireRel (σ : Equiv.Perm (Fin 14)) (old new : List Bool) : Prop :=
  old.length = new.length ∧ 14 ≤ old.length ∧
    ∀ k, old.getD k false = new.getD (remapWire σ k) false

private theorem rel_inputs (σ : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    WireRel σ (List.ofFn (x ∘ σ)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro k
  by_cases hk : k < 14
  · have hn := (σ ⟨k, hk⟩).isLt
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    rw [List.getD_eq_getElem _ _ (by simp [remapWire, hk])]
    simp only [List.getElem_ofFn, remapWire, dite_eq_left hk, Function.comp_apply]
  · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [remapWire, hk]; omega)]

private theorem rel_append {σ : Equiv.Perm (Fin 14)} {old new : List Bool}
    (h : WireRel σ old new) (b : Bool) :
    WireRel σ (old ++ [b]) (new ++ [b]) := by
  obtain ⟨hlen, hbase, hval⟩ := h
  refine ⟨by simp [hlen], by simp; omega, ?_⟩
  intro k
  by_cases hk : k < old.length
  · have hk' := (remapWire_lt σ k old.length hbase).2 hk
    rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (hlen ▸ hk')]
    exact hval k
  · have hfix : remapWire σ k = k := by
      have hn : ¬k < 14 := by omega
      simp [remapWire, hn]
    rw [hfix, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

private def remapGate (σ : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire σ)⟩

private def remapCircuit (σ : Equiv.Perm (Fin 14)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (remapGate σ), remapWire σ C.output⟩

private theorem rel_wires (σ : Equiv.Perm (Fin 14)) (gates : List Gate)
    (old new : List Bool) (h : WireRel σ old new) (out : ℕ) :
    (Circuit.eval ⟨gates, out⟩ old) =
      (remapCircuit σ ⟨gates, out⟩).eval new := by
  induction gates generalizing old new with
  | nil => exact h.2.2 out
  | cons g rest ih =>
    have hargs :
        g.inputs.map (fun k => old.getD k false) =
          (g.inputs.map (remapWire σ)).map (fun k => new.getD k false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun k _ => h.2.2 k)
    have hs := rel_append h (g.op.eval (g.inputs.map (fun k => old.getD k false)))
    simp only [Circuit.eval, Circuit.wires, remapCircuit, List.map_cons, List.foldl_cons] at ih ⊢
    change _ = (List.foldl _ (new ++ [g.op.eval
      ((g.inputs.map (remapWire σ)).map (fun k => new.getD k false))])
        (rest.map (remapGate σ))).getD _ _
    rw [← hargs]
    exact ih _ _ hs

private def firstWires (x : Fin 14 → Bool) (a b : Fin 14) (op : GateOp) : List Bool :=
  List.ofFn x ++ [op.eval [x a, x b]]

private def prefixWires (x : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15)
    (op₁ op₂ : GateOp) : List Bool :=
  let w := firstWires x a b op₁
  w ++ [op₂.eval [w.getD c.val false, w.getD d.val false]]

private theorem rel_prefix (σ : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool)
    (a b : Fin 14) (c d : Fin 15) (op₁ op₂ : GateOp) :
    WireRel σ (prefixWires (x ∘ σ) a b c d op₁ op₂)
      (prefixWires x (σ a) (σ b) (remapSecond σ c) (remapSecond σ d) op₁ op₂) := by
  have h : WireRel σ (firstWires (x ∘ σ) a b op₁) (firstWires x (σ a) (σ b) op₁) :=
    rel_append (rel_inputs σ x) _
  unfold prefixWires
  change WireRel σ
    (firstWires (x ∘ σ) a b op₁ ++ [op₂.eval [
      (firstWires (x ∘ σ) a b op₁).getD c.val false,
      (firstWires (x ∘ σ) a b op₁).getD d.val false]]) _
  rw [h.2.2 c.val, h.2.2 d.val]
  exact rel_append h _

private def AndOr (op : GateOp) : Prop := op = GateOp.and ∨ op = GateOp.or

private theorem eval_sorted {α : Type} [LinearOrder α] (f : α → Bool)
    (op : GateOp) (h : AndOr op) (a b : α) :
    op.eval [f (min a b), f (max a b)] = op.eval [f a, f b] := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right (le_of_not_ge hab), max_eq_left (le_of_not_ge hab)]
    rcases h with rfl | rfl
    · simp [GateOp.eval, Bool.and_comm]
    · simp [GateOp.eval, Bool.or_comm]

private theorem prefix_sorted (x : Fin 14 → Bool) (a b : Fin 14) (c d : Fin 15)
    (op₁ op₂ : GateOp) (h₁ : AndOr op₁) (h₂ : AndOr op₂) :
    prefixWires x (min a b) (max a b) (min c d) (max c d) op₁ op₂ =
      prefixWires x a b c d op₁ op₂ := by
  simp only [prefixWires, firstWires, eval_sorted x op₁ h₁]
  exact congrArg (fun v => (List.ofFn x ++ [op₁.eval [x a, x b]]) ++ [v])
    (eval_sorted (fun i : Fin 15 =>
      (List.ofFn x ++ [op₁.eval [x a, x b]]).getD i.val false) op₂ h₂ c d)

private theorem remapCircuit_mono (σ : Equiv.Perm (Fin 14)) (C : Circuit)
    (h : MetaComplexity.Monotone2 C) : MetaComplexity.Monotone2 (remapCircuit σ C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [remapGate] using h g' hg'

private theorem min_lt_max_of_ne {α : Type} [LinearOrder α] {a b : α} (h : a ≠ b) :
    min a b < max a b := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
  · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt

private def pairCode (a b c d : ℕ) : ℕ :=
  (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

private abbrev SplitCircuit := (Fin 14 × Fin 14) × (Fin 15 × Fin 15) × (GateOp × GateOp) × Circuit

private abbrev SplitCircuit.a (S : SplitCircuit) := S.1.1
private abbrev SplitCircuit.b (S : SplitCircuit) := S.1.2
private abbrev SplitCircuit.c (S : SplitCircuit) := S.2.1.1
private abbrev SplitCircuit.d (S : SplitCircuit) := S.2.1.2
private abbrev SplitCircuit.op₁ (S : SplitCircuit) := S.2.2.1.1
private abbrev SplitCircuit.op₂ (S : SplitCircuit) := S.2.2.1.2
private abbrev SplitCircuit.tail (S : SplitCircuit) := S.2.2.2

private def SplitCircuit.code (S : SplitCircuit) : ℕ :=
  pairCode S.a.val S.b.val S.c.val S.d.val

private def SplitCircuit.valid (S : SplitCircuit) (f : (Fin 14 → Bool) → Bool) : Prop :=
  S.a < S.b ∧ S.c < S.d ∧ AndOr S.op₁ ∧ AndOr S.op₂ ∧
    MetaComplexity.Monotone2 S.tail ∧ S.tail.size ≤ 24 ∧
      ∀ x, S.tail.eval (prefixWires x S.a S.b S.c S.d S.op₁ S.op₂) = f x

private theorem SplitCircuit.relabel {S : SplitCircuit} {f : (Fin 14 → Bool) → Bool}
    (h : S.valid f) (σ : Equiv.Perm (Fin 14)) (hσ : ∀ x, f (x ∘ σ) = f x) :
    ∃ T : SplitCircuit, T.valid f ∧ T.code =
      pairCode (σ S.a).val (σ S.b).val (remapSecond σ S.c).val (remapSecond σ S.d).val := by
  obtain ⟨hab, hcd, h₁, h₂, hmono, hsize, hfun⟩ := h
  let a := σ S.a
  let b := σ S.b
  let c := remapSecond σ S.c
  let d := remapSecond σ S.d
  let T : SplitCircuit :=
    ((min a b, max a b), (min c d, max c d), (S.op₁, S.op₂), remapCircuit σ S.tail)
  have hab' : a ≠ b := fun he => hab.ne (σ.injective he)
  have hcd' : c ≠ d := fun he => hcd.ne (Fin.ext (remapWire_injective σ (congrArg Fin.val he)))
  refine ⟨T, ⟨min_lt_max_of_ne hab', min_lt_max_of_ne hcd', h₁, h₂,
    remapCircuit_mono σ S.tail hmono, ?_, ?_⟩, ?_⟩
  · simpa [T, remapCircuit, Circuit.size] using hsize
  · intro x
    change (remapCircuit σ S.tail).eval
      (prefixWires x (min a b) (max a b) (min c d) (max c d) S.op₁ S.op₂) = f x
    rw [prefix_sorted x a b c d _ _ h₁ h₂]
    rw [← rel_wires σ S.tail.gates _ _ (rel_prefix σ x S.a S.b S.c S.d S.op₁ S.op₂) S.tail.output]
    exact (hfun (x ∘ σ)).trans (hσ x)
  · change pairCode (min a b).val (max a b).val (min c d).val (max c d).val =
      pairCode a.val b.val c.val d.val
    have h₁' : min a.val b.val ≤ max a.val b.val := (min_le_left _ _).trans (le_max_left _ _)
    have h₂' : min c.val d.val ≤ max c.val d.val := (min_le_left _ _).trans (le_max_left _ _)
    simp only [pairCode, Fin.val_min, Fin.val_max, min_eq_left h₁', max_eq_right h₁',
      min_eq_left h₂', max_eq_right h₂']

private theorem split_initial (f : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hModel : TopForm.IsAO2 14 C) (hDistinct : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hmin : 2 ≤ C.size) (hmax : C.size ≤ 26)
    (hfun : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = f x) :
    ∃ S : SplitCircuit, S.valid f := by
  rcases C with ⟨gates, out⟩
  obtain ⟨g₁, g₂, tail, rfl⟩ : ∃ g₁ g₂ tail, gates = g₁ :: g₂ :: tail := by
    cases gates with
    | nil => simp [Circuit.size] at hmin
    | cons g rest =>
      cases rest with
      | nil => simp [Circuit.size] at hmin
      | cons g' tail => exact ⟨g, g', tail, rfl⟩
  have hg₁ : g₁ ∈ (g₁ :: g₂ :: tail) := by simp
  have hg₂ : g₂ ∈ (g₁ :: g₂ :: tail) := by simp
  have h₁ : AndOr g₁.op := hModel.1 g₁ hg₁
  have h₂ : AndOr g₂.op := hModel.1 g₂ hg₂
  have ht₁ := hModel.2.1 0 (by simp)
  have ht₂ := hModel.2.1 1 (by simp)
  change ∀ i ∈ g₁.inputs, i < 14 at ht₁
  change ∀ i ∈ g₂.inputs, i < 15 at ht₂
  obtain ⟨a, b, ha⟩ : ∃ a b, g₁.inputs = [a, b] :=
    ⟨_, _, List.eq_getElem_of_length_eq_two _ (hModel.2.2 g₁ hg₁)⟩
  obtain ⟨c, d, hc⟩ : ∃ c d, g₂.inputs = [c, d] :=
    ⟨_, _, List.eq_getElem_of_length_eq_two _ (hModel.2.2 g₂ hg₂)⟩
  let ai : Fin 14 := ⟨a, ht₁ _ (by simp [ha])⟩
  let bi : Fin 14 := ⟨b, ht₁ _ (by simp [ha])⟩
  let ci : Fin 15 := ⟨c, ht₂ _ (by simp [hc])⟩
  let di : Fin 15 := ⟨d, ht₂ _ (by simp [hc])⟩
  have hne₁ : ai ≠ bi := by
    have hn : a ≠ b := by simpa [ha] using hDistinct g₁ hg₁
    exact fun he => hn (congrArg Fin.val he)
  have hne₂ : ci ≠ di := by
    have hn : c ≠ d := by simpa [hc] using hDistinct g₂ hg₂
    exact fun he => hn (congrArg Fin.val he)
  refine ⟨((min ai bi, max ai bi), (min ci di, max ci di), (g₁.op, g₂.op), ⟨tail, out⟩),
    ⟨min_lt_max_of_ne hne₁, min_lt_max_of_ne hne₂, h₁, h₂, ?_, ?_, ?_⟩⟩
  · intro g hg
    have hmem : g ∈ g₁ :: g₂ :: tail := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)
    have hop := hModel.1 g hmem
    have hlen := hModel.2.2 g hmem
    exact ⟨by simpa using hop, hlen.le⟩
  · simp only [Circuit.size, List.length_cons] at hmax ⊢
    omega
  · intro x
    change (Circuit.eval ⟨tail, out⟩
      (prefixWires x (min ai bi) (max ai bi) (min ci di) (max ci di) g₁.op g₂.op)) = f x
    rw [prefix_sorted x ai bi ci di _ _ h₁ h₂]
    have readInput (i : Fin 14) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have he := hfun x
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons, ha, hc, List.map_cons, List.map_nil] at he
    rw [show (List.ofFn x).getD a false = x ai from readInput ai,
      show (List.ofFn x).getD b false = x bi from readInput bi] at he
    exact he

end PEqualNP.Outside.L_meta_3322_aux

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3322_aux

-- Fixing the first two gates up to input symmetries leaves at most 24 gates.
theorem PEqualNP.Outside.L_meta_3322 (f : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hModel : TopForm.IsAO2 14 C) (hDistinct : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hmin : 2 ≤ C.size) (hmax : C.size ≤ 26)
    (hfun : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = f x) :
    ∃ (a b : Fin 14) (c d : Fin 15) (op₁ op₂ : GateOp) (tail : Circuit),
      a < b ∧ c < d ∧ AndOr op₁ ∧ AndOr op₂ ∧
        (∀ σ : Equiv.Perm (Fin 14), (∀ x, f (x ∘ σ) = f x) →
          pairCode a.val b.val c.val d.val ≤
            pairCode (σ a).val (σ b).val
              (if c < (14 : Fin 15) then (σ (Fin.ofNat 14 c.val)).val else 14)
              (if d < (14 : Fin 15) then (σ (Fin.ofNat 14 d.val)).val else 14)) ∧
        MetaComplexity.Monotone2 tail ∧ tail.size ≤ 24 ∧
          ∀ x, tail.eval (prefixWires x a b c d op₁ op₂) = f x := by
  classical
  obtain ⟨S₀, h₀⟩ := split_initial f C hModel hDistinct hmin hmax hfun
  let Q (k : ℕ) : Prop := ∃ S : SplitCircuit, S.valid f ∧ S.code = k
  have hex : ∃ k, Q k := ⟨S₀.code, S₀, h₀, rfl⟩
  obtain ⟨S, hS, hcode⟩ := Nat.find_spec hex
  have hvalid := hS
  obtain ⟨hab, hcd, h₁, h₂, hmono, hsize, heval⟩ := hvalid
  refine ⟨S.a, S.b, S.c, S.d, S.op₁, S.op₂, S.tail, hab, hcd, h₁, h₂, ?_, hmono, hsize, heval⟩
  intro σ hσ
  obtain ⟨T, hT, hcodeT⟩ := SplitCircuit.relabel hS σ hσ
  have hle := Nat.find_min' hex (show Q T.code from ⟨T, hT, rfl⟩)
  rw [← hcode, hcodeT, remapSecond_val, remapSecond_val] at hle
  exact hle
