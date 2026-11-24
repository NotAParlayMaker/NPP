import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2016_74 :
    (¬ HasCircuitSize 6 (fun x => decide (∃ i j : Fin 6, (i.val+1)%6 = j.val ∧ x i = true ∧ x j = true)) 7) →
    (let f (x : Fin 7 → Bool) := (340282366683253975791449600841168373960 : Nat).testBit (tableIndex x)
     let move (c d : Circuit) := ∃ i p : Nat, ∃ g : Gate, c.gates[i]? = some g ∧
      g.op = .and ∧ g.inputs.length = 2 ∧ p ∈ g.inputs ∧ p < 7+i ∧
      d = PEqualNP.CircuitMoves.eraseGate 7 c i p
     let reach (c : Circuit) (t : (Fin 7 → Bool) → Bool) := ∃ a b : Nat, ∃ gs : List Gate,
      List.Forall₂ (fun g h => g.op = h.op ∧
        List.Forall₂ (fun u v => v = u+1 ∨ v = 0 ∧ (u=a ∨ u=b)) g.inputs h.inputs) c.gates gs ∧
      ∀ x, (⟨gs,c.output+1⟩ : Circuit).eval (true :: List.ofFn x) = t x
     ∀ c : Circuit, FanInTwo c → c.size = 11 → circuitFun 7 c = f →
       reach c (fun x => f x || x 2) →
       (∃ d : Circuit, (circuitFun 7 d = fun x => f x || x 2) ∧
         (move c d ∨ Monotone2 c ∧ ∃ e, move c e ∧ move e d)) ∨
       HasCircuitSize 7 (fun x => f (Function.update x 2 false)) 7) →
    (let f (x : Fin 7 → Bool) := (340282366683253975791449600841168373960 : Nat).testBit (tableIndex x)
     let move (c d : Circuit) := ∃ i p : Nat, ∃ g : Gate, c.gates[i]? = some g ∧
      g.op = .and ∧ g.inputs.length = 2 ∧ p ∈ g.inputs ∧ p < 7+i ∧
      d = PEqualNP.CircuitMoves.eraseGate 7 c i p
     let reach (c : Circuit) (t : (Fin 7 → Bool) → Bool) := ∃ a b : Nat, ∃ gs : List Gate,
      List.Forall₂ (fun g h => g.op = h.op ∧
        List.Forall₂ (fun u v => v = u+1 ∨ v = 0 ∧ (u=a ∨ u=b)) g.inputs h.inputs) c.gates gs ∧
      ∀ x, (⟨gs,c.output+1⟩ : Circuit).eval (true :: List.ofFn x) = t x
     ∀ c : Circuit, FanInTwo c → c.size = 11 → circuitFun 7 c = f →
       reach c (fun x => f x || x 0 || x 3) → ¬ (∃ d : Circuit, move c d ∧ circuitFun 7 d = fun x => f x || x 2)) →
    (let f (x : Fin 7 → Bool) := (340282366683253975791449600841168373960 : Nat).testBit (tableIndex x)
     let move (c d : Circuit) := ∃ i p : Nat, ∃ g : Gate, c.gates[i]? = some g ∧
      g.op = .and ∧ g.inputs.length = 2 ∧ p ∈ g.inputs ∧ p < 7+i ∧
      d = PEqualNP.CircuitMoves.eraseGate 7 c i p
     let reach (c : Circuit) (t : (Fin 7 → Bool) → Bool) := ∃ a b : Nat, ∃ gs : List Gate,
      List.Forall₂ (fun g h => g.op = h.op ∧
        List.Forall₂ (fun u v => v = u+1 ∨ v = 0 ∧ (u=a ∨ u=b)) g.inputs h.inputs) c.gates gs ∧
      ∀ x, (⟨gs,c.output+1⟩ : Circuit).eval (true :: List.ofFn x) = t x
     ∀ c : Circuit, FanInTwo c → c.size = 11 → circuitFun 7 c = f →
       reach c (fun x => f x || x 0 || x 3) → ¬ (Monotone2 c ∧ ∃ d e : Circuit, move c d ∧ move d e ∧ circuitFun 7 e = fun x => f x || x 2)) →
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  intro cycleLower normalization noOne noTwo
  dsimp only at normalization noOne noTwo
  intro graphOriginal
  rintro ⟨c, fan, size, base, branches⟩
  let graph (x : Fin 9 → Bool) :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let f (x : Fin 7 → Bool) := (340282366683253975791449600841168373960 : Nat).testBit (tableIndex x)
  have baseEq : ∀ x : Fin 7 → Bool,
      graph (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = f x := by decide
  have singletonEq : ∀ x : Fin 7 → Bool,
      graph (Fin.insertNth 0 false (Fin.insertNth 3 true x)) = (f x || x 2) := by decide
  have pairEq : ∀ x : Fin 7 → Bool,
      graph (Fin.insertNth 0 true (Fin.insertNth 3 false x)) = (f x || x 0 || x 3) := by decide
  have exactBase : circuitFun 7 c = f := by
    funext x
    exact (congrFun base x).trans (baseEq x)
  obtain ⟨a,b,d,out,ports,values⟩ := branches false
  obtain ⟨u,v,e,out',ports',values'⟩ := branches true
  have firstValues (x : Fin 7 → Bool) :
      (⟨d.gates,c.output+1⟩ : Circuit).eval (true :: List.ofFn x) = (f x || x 2) := by
    rw [← out]
    exact (values x).trans (singletonEq x)
  have secondValues (x : Fin 7 → Bool) :
      (⟨e.gates,c.output+1⟩ : Circuit).eval (true :: List.ofFn x) = (f x || x 0 || x 3) := by
    rw [← out']
    exact (values' x).trans (pairEq x)
  rcases normalization c fan size exactBase ⟨a,b,d.gates,ports,firstValues⟩ with ⟨D,targetD,moves⟩ | h
  · rcases moves with one | ⟨mono,E,first,last⟩
    · exact noOne c fan size exactBase ⟨u,v,e.gates,ports',secondValues⟩ ⟨D,one,targetD⟩
    · exact noTwo c fan size exactBase ⟨u,v,e.gates,ports',secondValues⟩ ⟨mono,E,D,first,last,targetD⟩
  · apply cycleLower
    have getD_snoc_eq (ws : List Bool) (x : Bool) :
        (ws ++ [x]).getD ws.length false = x := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    let wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
      if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m


    let relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
      ⟨g.op, g.inputs.map (wmap n m π)⟩


    let relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
      ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩


    let step (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]


    let Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
      n ≤ W.length ∧ W'.length + n = W.length + m ∧
        ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

    have rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
        (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
      obtain ⟨h1, h2, h3⟩ := h
      have hv : (relGate n m π g).op.eval
          ((relGate n m π g).inputs.map fun i => W'.getD i false)
          = g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [relGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact h3 a
      refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
      intro w
      simp only [step, hv]
      rcases Nat.lt_trichotomy w W.length with hw | hw | hw
      · have hlt : wmap n m π w < W'.length := by
          unfold wmap
          split
          · have := (π ⟨w, by assumption⟩).2; omega
          · omega
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
        exact h3 w
      · have he : wmap n m π w = W'.length := by
          unfold wmap
          split
          · omega
          · omega
        rw [he, hw, getD_snoc_eq, getD_snoc_eq]
      · have hge : W'.length + 1 ≤ wmap n m π w := by
          unfold wmap
          split
          · omega
          · omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

    have rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
        ∀ W W' : List Bool, Rel n m π W W' →
          Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
      induction gs with
      | nil => intro W W' h; exact h
      | cons g gs ih =>
        intro W W' h
        exact ih _ _ (rel_step n m π W W' g h)

    have rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
        Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
      refine ⟨by simp, by simp; omega, ?_⟩
      intro w
      unfold wmap
      split
      · rename_i hw
        rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
        simp
      · rename_i hw
        rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]


    have relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
        (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
      obtain ⟨C, ok, hsz, hev⟩ := hc
      refine ⟨relabel n m π C, ?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
      · change (C.gates.map (relGate n m π)).length ≤ s
        rw [List.length_map]
        exact hsz
      · intro x
        show _ = h (x ∘ π)
        rw [← hev (x ∘ π)]
        have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
        exact this

    let π : Fin 7 → Fin 6 := ![0,1,0,3,5,2,4]
    have routed := relabel_size π (fun x => f (Function.update x 2 false)) 7 h
    have eqf : (fun y : Fin 6 → Bool => f (Function.update (y ∘ π) 2 false)) =
        (fun x => decide (∃ i j : Fin 6, (i.val+1)%6 = j.val ∧ x i = true ∧ x j = true)) := by
      funext y
      exact (by decide : ∀ y : Fin 6 → Bool, f (Function.update (y ∘ π) 2 false) =
        decide (∃ i j : Fin 6, (i.val+1)%6 = j.val ∧ y i = true ∧ y j = true)) y
    rw [eqf] at routed
    exact routed
