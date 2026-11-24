import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2004

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl bstep x := rfl

theorem bstep_len (w : List Bool) (g : Gate) : (bstep w g).length = w.length + 1 := by
  simp [bstep]

theorem getD_ge (w : List Bool) (v : ℕ) (hv : w.length ≤ v) : w.getD v false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hv]

theorem bstep_getD_lt (w : List Bool) (g : Gate) (v : ℕ) (hv : v < w.length) :
    (bstep w g).getD v false = w.getD v false := by
  simp [bstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hv]

theorem bstep_getD_self (w : List Bool) (g : Gate) :
    (bstep w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [bstep, List.getD_eq_getElem?_getD]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

def pull : List Gate → ℕ → Finset ℕ → Finset ℕ
  | [], _, F => F
  | g :: G, base, F =>
      if base ∈ pull G (base + 1) F then
        g.inputs.toFinset ∪ ((pull G (base + 1) F).erase base)
      else pull G (base + 1) F

theorem pull_card : ∀ (G : List Gate) (base : ℕ) (F : Finset ℕ),
    (∀ g ∈ G, g.inputs.length ≤ 2) →
    (pull G base F).card ≤ F.card + G.length := by
  intro G
  induction G with
  | nil =>
    intro base F _
    simp [pull]
  | cons g G ih =>
    intro base F hG
    have h := ih (base + 1) F (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
    have hg : g.inputs.length ≤ 2 := hG g List.mem_cons_self
    rw [pull, List.length_cons]
    split_ifs with hb
    · have h1 : ((pull G (base + 1) F).erase base).card + 1 = (pull G (base + 1) F).card :=
        Finset.card_erase_add_one hb
      have h2 := Finset.card_union_le g.inputs.toFinset ((pull G (base + 1) F).erase base)
      have h3 := List.toFinset_card_le g.inputs
      omega
    · omega

theorem pull_sound : ∀ (G : List Gate) (F : Finset ℕ) (w1 w2 : List Bool),
    w1.length = w2.length →
    (∀ v ∈ pull G w1.length F, v < w1.length → w1.getD v false = w2.getD v false) →
    ∀ v ∈ F, (G.foldl bstep w1).getD v false = (G.foldl bstep w2).getD v false := by
  intro G
  induction G with
  | nil =>
    intro F w1 w2 hlen h v hv
    rw [List.foldl_nil, List.foldl_nil]
    by_cases hlt : v < w1.length
    · exact h v hv hlt
    · rw [getD_ge w1 v (Nat.le_of_not_lt hlt),
        getD_ge w2 v (by rw [← hlen]; exact Nat.le_of_not_lt hlt)]
  | cons g G ih =>
    intro F w1 w2 hlen h v hv
    rw [List.foldl_cons, List.foldl_cons]
    refine ih F (bstep w1 g) (bstep w2 g) (by rw [bstep_len, bstep_len, hlen]) ?_ v hv
    intro u hu hult
    rw [bstep_len] at hu hult
    by_cases hub : u = w1.length
    · subst hub
      have hpl : pull (g :: G) w1.length F =
          g.inputs.toFinset ∪ ((pull G (w1.length + 1) F).erase w1.length) := by
        rw [pull, if_pos hu]
      have hmap : (g.inputs.map fun i => w1.getD i false) =
          (g.inputs.map fun i => w2.getD i false) := by
        apply List.map_congr_left
        intro i hi
        by_cases hll : i < w1.length
        · exact h i (by rw [hpl]; exact Finset.mem_union_left _ (List.mem_toFinset.mpr hi)) hll
        · rw [getD_ge w1 _ (Nat.le_of_not_lt hll),
            getD_ge w2 _ (by rw [← hlen]; exact Nat.le_of_not_lt hll)]
      rw [bstep_getD_self w1 g, hlen, bstep_getD_self w2 g, hmap]
    · have hlt : u < w1.length := by omega
      have hmem : u ∈ pull (g :: G) w1.length F := by
        rw [pull]
        split_ifs with hb
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hub, hu⟩)
        · exact hu
      rw [bstep_getD_lt w1 g u hlt, bstep_getD_lt w2 g u (by rw [← hlen]; exact hlt)]
      exact h u hmem hlt

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin x1), ∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x4 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → x1 ≤ x2.size + (1 : ℕ) := by
  intro n C hM hdep
  have hcard := pull_card C.gates n {C.output} (fun g hg => (hM g hg).2)
  have hall : ∀ i : Fin n, i.val ∈ pull C.gates n {C.output} := by
    intro i
    by_contra hni
    obtain ⟨x, y, hxy, hne⟩ := hdep i
    apply hne
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
    rw [wires_eq, wires_eq]
    refine pull_sound C.gates {C.output} (List.ofFn x) (List.ofFn y)
      (by simp) ?_ C.output (Finset.mem_singleton_self _)
    intro v hv hvn
    rw [List.length_ofFn] at hv hvn
    have hfin : (⟨v, hvn⟩ : Fin n) ≠ i := by
      intro heq
      apply hni
      rw [← heq]
      exact hv
    rw [ofFn_getD _ v hvn, ofFn_getD _ v hvn]
    exact hxy _ hfin
  have himg : (Finset.univ.image (fun i : Fin n => i.val)) ⊆ pull C.gates n {C.output} := by
    intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    rw [← hi]
    exact hall i
  have hn : (Finset.univ.image (fun i : Fin n => i.val)).card = n := by
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ, Fintype.card_fin]
  have hle := Finset.card_le_card himg
  have hsz : C.size = C.gates.length := rfl
  rw [Finset.card_singleton] at hcard
  omega

end PEqualNP.Outside.L_meta_2004

theorem PEqualNP.Outside.L_meta_2004 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin x1), ∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x4 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → x1 ≤ x2.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_2004.main
