import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4506

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private def remap (W BIG i : ℕ) : ℕ :=
  if i < W then i else if i = W then BIG else i - 1

private def remapGate (W BIG : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap W BIG)⟩

private lemma getD_remap (W BIG : ℕ) (a b : List Bool) (ha : a.length = W)
    (hbig : W + b.length < BIG) (i : ℕ) :
    (a ++ b).getD (remap W BIG i) false = (a ++ false :: b).getD i false := by
  unfold remap
  by_cases h1 : i < W
  · rw [if_pos h1]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · rw [if_neg h1]
    by_cases h2 : i = W
    · rw [if_pos h2]
      simp only [List.getD_eq_getElem?_getD]
      have hlen : (a ++ b).length ≤ BIG := by simp [ha]; omega
      rw [List.getElem?_eq_none hlen, List.getElem?_append_right (by omega)]
      have hsub : i - a.length = 0 := by omega
      simp [hsub]
    · rw [if_neg h2]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      have hsub : i - a.length = (i - 1 - a.length) + 1 := by omega
      rw [hsub]
      rfl

private lemma foldl_remap (W BIG : ℕ) (gs : List Gate) :
    ∀ (a b : List Bool), a.length = W → W + b.length + gs.length < BIG →
      ∃ b' : List Bool,
        b'.length = b.length + gs.length ∧
        gs.foldl step (a ++ false :: b) = a ++ false :: b' ∧
        (gs.map (remapGate W BIG)).foldl step (a ++ b) = a ++ b' := by
  induction gs with
  | nil =>
    intro a b _ _
    exact ⟨b, by simp, rfl, rfl⟩
  | cons g gs ih =>
    intro a b ha hbig
    have heval :
        ((remapGate W BIG g).inputs.map fun j => (a ++ b).getD j false) =
        (g.inputs.map fun i => (a ++ false :: b).getD i false) := by
      simp only [remapGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact getD_remap W BIG a b ha (by simp at hbig; omega) i
    let v : Bool := g.op.eval (g.inputs.map fun i => (a ++ false :: b).getD i false)
    have hstep1 : step (a ++ false :: b) g = a ++ false :: (b ++ [v]) := by
      simp [step, v, List.append_assoc]
    have hstep2 : step (a ++ b) (remapGate W BIG g) = a ++ (b ++ [v]) := by
      simp only [step, heval, List.append_assoc]
      rfl
    obtain ⟨b', hlen', h1, h2⟩ := ih a (b ++ [v]) ha (by simp at hbig ⊢; omega)
    refine ⟨b', by simp at hlen' ⊢; omega, ?_, ?_⟩
    · simp only [List.foldl_cons, hstep1]
      exact h1
    · simp only [List.map_cons, List.foldl_cons, hstep2]
      exact h2

private lemma compose_false {n : ℕ} (f : (Fin n → Bool) → Bool)
    (x1 x2 : Circuit) (hx1 : FanInTwo x1) (hx2 : FanInTwo x2)
    (heval : ∀ x : Fin n → Bool, x2.eval (x1.wires (List.ofFn x) ++ [false]) = f x) :
    HasCircuitSize n f (x1.size + x2.size) := by
  let W := n + x1.size
  let BIG := W + x2.size + 1
  let C : Circuit := ⟨x1.gates ++ x2.gates.map (remapGate W BIG), remap W BIG x2.output⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_append, List.mem_map] at hg
    rcases hg with hg1 | ⟨g', hg2, rfl⟩
    · exact hx1 g hg1
    · rcases hx2 g' hg2 with ⟨hop, hlen⟩
      exact ⟨hop, by simpa [remapGate] using hlen⟩
  · simp [C, Circuit.size]
  · intro x
    let a := x1.wires (List.ofFn x)
    have ha_len : a.length = W := by
      change (x1.gates.foldl step (List.ofFn x)).length = n + x1.gates.length
      rw [foldl_length, List.length_ofFn]
    have hC_wires : C.wires (List.ofFn x) =
        (x2.gates.map (remapGate W BIG)).foldl step (a ++ []) := by
      change (x1.gates ++ x2.gates.map (remapGate W BIG)).foldl step (List.ofFn x) = _
      rw [List.foldl_append, List.append_nil]
      rfl
    have hx2_wires : x2.wires (a ++ [false]) = x2.gates.foldl step (a ++ false :: []) := rfl
    obtain ⟨b', hlen', h1, h2⟩ := foldl_remap W BIG x2.gates a [] ha_len (by simp [BIG, Circuit.size])
    have hbig' : W + b'.length < BIG := by simp [BIG, Circuit.size] at hlen' ⊢; omega
    calc
      C.eval (List.ofFn x)
          = (C.wires (List.ofFn x)).getD (remap W BIG x2.output) false := rfl
      _ = (a ++ b').getD (remap W BIG x2.output) false := by rw [hC_wires, h2]
      _ = (a ++ false :: b').getD x2.output false := getD_remap W BIG a b' ha_len hbig' x2.output
      _ = (x2.wires (a ++ [false])).getD x2.output false := by rw [hx2_wires, h1]
      _ = x2.eval (x1.wires (List.ofFn x) ++ [false]) := rfl
      _ = f x := heval x

end PEqualNP.Outside.L_meta_4506

theorem PEqualNP.Outside.L_meta_4506 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x5 : Fin (8 : ℕ) → Bool), x2.eval (x1.wires (List.ofFn x5) ++ [Bool.false]) = (x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x6 : Fin (8 : ℕ) → Bool) => x6 (0 : Fin (8 : ℕ)) && x6 (1 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (2 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (3 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (5 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (4 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (5 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (7 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ))) (x1.size + x2.size) :=
  fun x1 x2 hx1 hx2 heval => PEqualNP.Outside.L_meta_4506.compose_false _ x1 x2 hx1 hx2 heval
