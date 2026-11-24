import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3300_317
    (minSize : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
      (x 5 && x 7) || (x 7 && x 4)) 12)
    (boundedControl :
      let f := fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4)
      ∀ (C : Circuit) (k i : ℕ), FanInTwo C → C.size = 13 → C.output = 21 →
        5 ≤ k → k < 13 → 9 ≤ i → i < 9 + k →
        (∀ g ∈ C.gates.take k, 8 ∉ g.inputs) →
        (∀ g ∈ C.gates, ∀ j ∈ g.inputs, j ≤ 22) →
        let bit := fun x : Fin 8 → Bool => (C.wires (List.ofFn x ++ [false])).getD i false
        (∀ x, f x = false → (x 0 || x 3) = true → bit x = false) →
        (∀ x, C.eval (List.ofFn x ++ [bit x]) = f x) →
        (∀ x, C.eval (List.ofFn x ++ [true]) = (f x || x 0 || x 3)) →
        False) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (5 : ℕ) ≤ x2.size →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.false) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.true]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  intro f P T i hfP hfT hp hbudget hi hiL w u hsens hlo
  by_contra! hhi
  let L := 8 + P.size
  let emit := fun (xs : List Bool) (g : Gate) =>
    g.op.eval (g.inputs.map fun j => xs.getD j false)
  let run := fun (gs : List Gate) (xs : List Bool) =>
    gs.foldl (fun ws g => ws ++ [emit ws g]) xs
  let mapGate := fun (ρ : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map ρ)

  have runConcat : ∀ (gs : List Gate) (xs : List Bool),
      ∃ tail : List Bool, tail.length = gs.length ∧ run gs xs = xs ++ tail := by
    intro gs
    induction gs with
    | nil =>
      intro xs
      exact ⟨[], rfl, by simp [run]⟩
    | cons g gs ih =>
      intro xs
      obtain ⟨tail, hlen, he⟩ := ih (xs ++ [emit xs g])
      refine ⟨emit xs g :: tail, by simp [hlen], ?_⟩
      change run gs (xs ++ [emit xs g]) = _
      rw [he, List.append_assoc]
      rfl

  have sim : ∀ (gs : List Gate) (ρ : ℕ → ℕ) (a b : List Bool),
      (∀ r j, (a ++ r).getD j false = (b ++ r).getD (ρ j) false) →
      ∃ tail : List Bool, tail.length = gs.length ∧
        run gs a = a ++ tail ∧ run (gs.map (mapGate ρ)) b = b ++ tail := by
    intro gs
    induction gs with
    | nil =>
      intro ρ a b _
      exact ⟨[], rfl, by simp [run], by simp [run]⟩
    | cons g gs ih =>
      intro ρ a b hread
      let v := emit a g
      have hv : emit b (mapGate ρ g) = v := by
        change g.op.eval ((g.inputs.map ρ).map (fun j => b.getD j false)) =
          g.op.eval (g.inputs.map (fun j => a.getD j false))
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        simpa using (hread [] j).symm
      have hread' (r : List Bool) (j : ℕ) :
          ((a ++ [v]) ++ r).getD j false = ((b ++ [v]) ++ r).getD (ρ j) false := by
        rw [List.append_assoc, List.append_assoc]
        exact hread ([v] ++ r) j
      obtain ⟨tail, hlen, ha, hb⟩ := ih ρ (a ++ [v]) (b ++ [v]) hread'
      refine ⟨v :: tail, by simp [hlen], ?_, ?_⟩
      · change run gs (a ++ [v]) = _
        rw [ha, List.append_assoc]
        rfl
      · change run (gs.map (mapGate ρ)) (b ++ [emit b (mapGate ρ g)]) = _
        rw [hv, hb, List.append_assoc]
        rfl

  have mappedFan (ρ : ℕ → ℕ) (K : Circuit) (hK : FanInTwo K) :
      ∀ g ∈ K.gates.map (mapGate ρ), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
         g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using hK g0 hg0

  have hwlen (x : Fin 8 → Bool) : (w x).length = L := by
    obtain ⟨tail, hlen, he⟩ := runConcat P.gates (List.ofFn x)
    change (run P.gates (List.ofFn x)).length = L
    rw [he, List.length_append, hlen, List.length_ofFn]
    rfl

  -- On the low branch the extra slot is an alias of an already available wire.
  let erase := fun j : ℕ => if j < L then j else if j = L then i else j - 1
  have aliasRead (a : List Bool) (ha : a.length = L) (tail : List Bool) (j : ℕ) :
      ((a ++ [a.getD i false]) ++ tail).getD j false = (a ++ tail).getD (erase j) false := by
    rw [List.append_assoc]
    by_cases hj : j < L
    · rw [show erase j = j by simp [erase, hj]]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    by_cases hEq : j = L
    · subst j
      have hit : i < a.length := by rw [ha]; exact hiL
      rw [show erase L = i by simp [erase],
        List.getD_append_right a _ false L (by omega),
        List.getD_append a tail false i hit]
      simp [ha]
    rw [show erase j = j - 1 by simp [erase, hj, hEq],
      List.getD_append_right a ([a.getD i false] ++ tail) false j (by omega),
      List.getD_append_right a tail false (j - 1) (by omega)]
    have hn : j - a.length = (j - 1 - a.length) + 1 := by omega
    simp [hn]

  let lowCircuit : Circuit := ⟨P.gates ++ T.gates.map (mapGate erase), erase T.output⟩
  have lowFan : FanInTwo lowCircuit := by
    intro g hg
    change g ∈ P.gates ++ T.gates.map (mapGate erase) at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hfP g hg
    · exact mappedFan _ _ hfT _ hg
  have lowSize : lowCircuit.size = P.size + T.size := by
    change (P.gates ++ T.gates.map (mapGate erase)).length = P.gates.length + T.gates.length
    rw [List.length_append, List.length_map]
  have lowEval (x : Fin 8 → Bool) : lowCircuit.eval (List.ofFn x) = f x := by
    obtain ⟨tail, _, ha, hb⟩ := sim T.gates erase (w x ++ [u x]) (w x) (aliasRead _ (hwlen x))
    have he : lowCircuit.eval (List.ofFn x) = (w x ++ tail).getD (erase T.output) false := by
      change (run (P.gates ++ T.gates.map (mapGate erase)) (List.ofFn x)).getD _ false = _
      simp only [run, List.foldl_append] at hb ⊢
      change (List.foldl _ (w x) (T.gates.map (mapGate erase))).getD _ false = _
      rw [hb]
    rw [he, ← aliasRead _ (hwlen x) tail T.output, ← ha]
    exact hlo x
  have hsize13 : lowCircuit.size = 13 := by
    by_contra h
    exact minSize ⟨lowCircuit, lowFan, by omega, lowEval⟩

  have lastLow : lowCircuit.output = 20 := by
    have htrue : f (fun _ => true) = true := rfl
    have hwire (x : Fin 8 → Bool) : (lowCircuit.wires (List.ofFn x)).length = 21 := by
      obtain ⟨tail, hlen, he⟩ := runConcat lowCircuit.gates (List.ofFn x)
      change (run lowCircuit.gates (List.ofFn x)).length = _
      rw [he, List.length_append, hlen, List.length_ofFn]
      change 8 + lowCircuit.size = 21
      rw [hsize13]
    have hv : lowCircuit.output < 21 := by
      by_contra! h
      have hm := List.getD_eq_default (lowCircuit.wires (List.ofFn (fun _ => true))) false
        (by rw [hwire]; exact h : (lowCircuit.wires (List.ofFn (fun _ => true))).length ≤ lowCircuit.output)
      have ht := lowEval (fun _ => true)
      change (lowCircuit.wires (List.ofFn (fun _ => true))).getD lowCircuit.output false = _ at ht
      rw [hm, htrue] at ht
      contradiction
    by_contra hm
    have hlt : lowCircuit.output < 20 := by omega
    have hnonempty : lowCircuit.gates ≠ [] := by
      intro he
      have hl : lowCircuit.gates.length = 13 := hsize13
      simp [he] at hl
    let Q : Circuit := ⟨lowCircuit.gates.dropLast, lowCircuit.output⟩
    have hsplit := List.dropLast_concat_getLast hnonempty
    have hdrop : Q.size = 12 := by
      have hh := congrArg List.length hsplit
      have h0 : lowCircuit.gates.length = 13 := hsize13
      change lowCircuit.gates.dropLast.length = 12
      simp only [List.length_append, List.length_cons, List.length_nil] at hh
      omega
    have hfan : FanInTwo Q := by
      intro g hg
      apply lowFan g
      rw [← hsplit]
      exact List.mem_append.mpr (Or.inl hg)
    apply minSize
    refine ⟨Q, hfan, hdrop.le, fun x => ?_⟩
    have hQlen : (Q.wires (List.ofFn x)).length = 20 := by
      obtain ⟨tail, hlen, he⟩ := runConcat Q.gates (List.ofFn x)
      change (run Q.gates (List.ofFn x)).length = _
      rw [he, List.length_append, hlen, List.length_ofFn]
      change 8 + Q.size = 20
      rw [hdrop]
    have hkeep : lowCircuit.eval (List.ofFn x) = Q.eval (List.ofFn x) := by
      change (run lowCircuit.gates (List.ofFn x)).getD lowCircuit.output false =
        (Q.wires (List.ofFn x)).getD lowCircuit.output false
      rw [← hsplit]
      simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((Q.wires (List.ofFn x)) ++ [_]).getD lowCircuit.output false = _
      exact List.getD_append _ _ _ _ (by omega)
    rw [← hkeep]
    exact lowEval x

  have tOutput : L < T.output := by
    by_contra! hle
    rcases eq_or_lt_of_le hle with hEq | hLt
    · let x : Fin 8 → Bool := fun _ => false
      obtain ⟨tail, _, he⟩ := runConcat T.gates (w x ++ [true])
      have heval : T.eval (w x ++ [true]) = true := by
        change (run T.gates (w x ++ [true])).getD T.output false = true
        rw [he, hEq, List.append_assoc, List.getD_append_right _ _ _ _ (by rw [hwlen])]
        simp [hwlen]
      have h := hhi x
      rw [heval] at h
      change true = false at h
      contradiction
    · let x : Fin 8 → Bool := fun j => decide (j = 0)
      have hf : f x = false := rfl
      have hh : (f x || x 0 || x 3) = true := rfl
      obtain ⟨a, _, ha⟩ := runConcat T.gates (w x ++ [u x])
      obtain ⟨b, _, hb⟩ := runConcat T.gates (w x ++ [true])
      have hlow : T.eval (w x ++ [u x]) = (w x).getD T.output false := by
        change (run T.gates (w x ++ [u x])).getD _ false = _
        rw [ha, List.append_assoc, List.getD_append _ _ _ _ (by rw [hwlen]; exact hLt)]
      have hhigh : T.eval (w x ++ [true]) = (w x).getD T.output false := by
        change (run T.gates (w x ++ [true])).getD _ false = _
        rw [hb, List.append_assoc, List.getD_append _ _ _ _ (by rw [hwlen]; exact hLt)]
      have hclash := (hlo x).symm.trans (hlow.trans (hhigh.symm.trans (hhi x)))
      rw [hh, hf] at hclash
      contradiction
  have he20 : erase T.output = 20 := lastLow
  have ho21 : T.output = 21 := by
    simp only [erase, if_neg (by omega : ¬ T.output < L), if_neg (by omega : T.output ≠ L)] at he20
    omega

  -- Move the extra slot in front of the gate list and give it the fixed index eight.
  let shift := fun j : ℕ => if j < 8 then j else j + 1
  let rotate := fun j : ℕ => if j < L then shift j else if j = L then 8 else j
  let C : Circuit := ⟨P.gates.map (mapGate shift) ++ T.gates.map (mapGate rotate), rotate T.output⟩
  have hFan : FanInTwo C := by
    intro g hg
    change g ∈ P.gates.map (mapGate shift) ++ T.gates.map (mapGate rotate) at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact mappedFan _ _ hfP _ hg
    · exact mappedFan _ _ hfT _ hg
  have hCsize : C.size = 13 := by
    have h : C.size = P.size + T.size := by
      change (P.gates.map (mapGate shift) ++ T.gates.map (mapGate rotate)).length =
        P.gates.length + T.gates.length
      rw [List.length_append, List.length_map, List.length_map]
    rw [h, ← lowSize, hsize13]
  have hCout : C.output = 21 := by
    change rotate T.output = 21
    rw [show rotate T.output = T.output by simp [rotate, show ¬ T.output < L by omega,
      show T.output ≠ L by omega], ho21]
  have hPrefix :
      ∀ g ∈ C.gates.take P.size, 8 ∉ g.inputs := by
    intro g hg
    change g ∈ (P.gates.map (mapGate shift) ++ T.gates.map (mapGate rotate)).take P.size at hg
    have hl : (P.gates.map (mapGate shift)).length = P.size := List.length_map _
    rw [← hl, List.take_left] at hg
    obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
    change 8 ∉ g0.inputs.map shift
    intro hm
    obtain ⟨j, _, he⟩ := List.mem_map.mp hm
    dsimp [shift] at he
    split at he <;> omega

  have startRead (a : List Bool) (ha : a.length = 8) (b : Bool) (r : List Bool) (j : ℕ) :
      (a ++ r).getD j false = ((a ++ [b]) ++ r).getD (shift j) false := by
    rw [List.append_assoc]
    by_cases hj : j < 8
    · rw [show shift j = j by simp [shift, hj]]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    rw [show shift j = j + 1 by simp [shift, hj],
      List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    have hn : j + 1 - a.length = (j - a.length) + 1 := by omega
    simp [hn]

  have turnedRead (a s : List Bool) (ha : a.length = 8) (hs : s.length = P.size) (b : Bool)
      (r : List Bool) (j : ℕ) :
      ((a ++ s ++ [b]) ++ r).getD j false =
        ((a ++ [b] ++ s) ++ r).getD (rotate j) false := by
    simp only [List.append_assoc]
    by_cases hj0 : j < 8
    · rw [show rotate j = j by simp [rotate, shift, hj0, (show j < L by dsimp [L]; omega)]]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    by_cases hjL : j < L
    · rw [show rotate j = j + 1 by simp [rotate, shift, hj0, hjL],
        List.getD_append_right a (s ++ ([b] ++ r)) false j (by omega),
        List.getD_append_right a ([b] ++ (s ++ r)) false (j + 1) (by omega)]
      have hls : j - a.length < s.length := by dsimp [L] at hjL; omega
      rw [List.getD_append s _ false _ hls]
      have hn : j + 1 - a.length = (j - a.length) + 1 := by omega
      change s.getD (j - a.length) false = (b :: (s ++ r)).getD (j + 1 - a.length) false
      rw [hn, List.getD_cons_succ, List.getD_append s _ false _ hls]
    by_cases hjEq : j = L
    · subst j
      rw [show rotate L = 8 by simp [rotate],
        List.getD_append_right a (s ++ ([b] ++ r)) false L (by dsimp [L]; omega),
        List.getD_append_right a ([b] ++ (s ++ r)) false 8 (by omega),
        List.getD_append_right s ([b] ++ r) false (L - a.length) (by dsimp [L]; omega)]
      simp [ha, hs, L]
    rw [show rotate j = j by simp [rotate, hjL, hjEq],
      List.getD_append_right a (s ++ ([b] ++ r)) false j (by omega),
      List.getD_append_right a ([b] ++ (s ++ r)) false j (by omega),
      List.getD_append_right s ([b] ++ r) false (j - a.length) (by dsimp [L] at hjL; omega)]
    have hleft : j - a.length - s.length = (j - a.length - s.length - 1) + 1 := by
      dsimp [L] at hjL hjEq
      omega
    have hright : j - a.length = (j - a.length - 1) + 1 := by omega
    change (b :: r).getD _ false = (b :: (s ++ r)).getD _ false
    rw [hleft, hright, List.getD_cons_succ, List.getD_cons_succ]
    rw [List.getD_append_right s r false (j - a.length - 1) (by dsimp [L] at hjL hjEq; omega)]
    congr 1
    omega

  have model (x : Fin 8 → Bool) (b : Bool) :
      C.eval (List.ofFn x ++ [b]) = T.eval (w x ++ [b]) ∧
      (C.wires (List.ofFn x ++ [b])).getD (i + 1) false = u x := by
    let orig := List.ofFn x
    have hlen : orig.length = 8 := List.length_ofFn
    obtain ⟨p, hplen, ha, hb⟩ := sim P.gates shift orig (orig ++ [b]) (startRead _ hlen _)
    have hw : w x = orig ++ p := ha
    obtain ⟨t, _, hc, hd⟩ := sim T.gates rotate (orig ++ p ++ [b]) (orig ++ [b] ++ p)
      (turnedRead _ _ hlen hplen _)
    have hW : C.wires (orig ++ [b]) = (orig ++ [b] ++ p) ++ t := by
      change run (P.gates.map (mapGate shift) ++ T.gates.map (mapGate rotate)) (orig ++ [b]) = _
      simp only [run, List.foldl_append] at hb hd ⊢
      rw [hb, hd]
    constructor
    · change (C.wires (orig ++ [b])).getD (rotate T.output) false =
        (run T.gates (w x ++ [b])).getD T.output false
      rw [hW, hw, hc]
      exact (turnedRead _ _ hlen hplen _ t T.output).symm
    · change (C.wires (orig ++ [b])).getD (i + 1) false = (w x).getD i false
      have hi' : i + 1 < (orig ++ [b] ++ p).length := by
        simp only [List.length_append, List.length_cons, List.length_nil, hlen, hplen]
        change i < 8 + P.gates.length at hiL
        omega
      rw [hW, hw, List.getD_append _ _ _ _ hi', ← show shift i = i + 1 by simp [shift, show ¬ i < 8 by omega]]
      exact (startRead _ hlen _ p i).symm

  -- Bound missing wire addresses by one fixed index beyond the final wire.
  let cap := fun j : ℕ => min j 22
  let K : Circuit := ⟨C.gates.map (mapGate cap), C.output⟩
  have hKF : FanInTwo K := mappedFan cap C hFan
  have hKsz : K.size = 13 := by
    change (C.gates.map (mapGate cap)).length = 13
    rw [List.length_map]
    exact hCsize
  have hKout : K.output = 21 := hCout
  have hKRefs : ∀ g ∈ K.gates, ∀ j ∈ g.inputs, j ≤ 22 := by
    intro g hg j hj
    obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j0, _, rfl⟩ := List.mem_map.mp hj
    exact Nat.min_le_right _ _
  have hKPrefix : ∀ g ∈ K.gates.take P.size, 8 ∉ g.inputs := by
    intro g hg
    change g ∈ (C.gates.map (mapGate cap)).take P.size at hg
    rw [← List.map_take] at hg
    obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg
    intro hm
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    have he' : j = 8 := by
      change min j 22 = 8 at he
      omega
    exact (hPrefix g0 h0) (he' ▸ hj)
  have capSim : ∀ (gs : List Gate) (xs : List Bool),
      xs.length + gs.length ≤ 22 → run (gs.map (mapGate cap)) xs = run gs xs := by
    intro gs
    induction gs with
    | nil =>
      intro xs _
      rfl
    | cons g gs ih =>
      intro xs hend
      have hv : emit xs (mapGate cap g) = emit xs g := by
        change g.op.eval ((g.inputs.map cap).map (fun j => xs.getD j false)) =
          g.op.eval (g.inputs.map (fun j => xs.getD j false))
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        change xs.getD (cap j) false = xs.getD j false
        by_cases hj : j ≤ 22
        · rw [show cap j = j from Nat.min_eq_left hj]
        rw [show cap j = 22 from Nat.min_eq_right (by omega)]
        rw [List.getD_eq_default xs false (by omega : xs.length ≤ 22),
          List.getD_eq_default xs false (by omega : xs.length ≤ j)]
      change run (gs.map (mapGate cap)) (xs ++ [emit xs (mapGate cap g)]) =
        run gs (xs ++ [emit xs g])
      rw [hv]
      apply ih
      simp only [List.length_append, List.length_cons, List.length_nil] at hend ⊢
      omega
  have sameWires (x : Fin 8 → Bool) (b : Bool) :
      K.wires (List.ofFn x ++ [b]) = C.wires (List.ofFn x ++ [b]) := by
    apply capSim
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    exact congrArg (9 + ·) hCsize |>.le
  have sameEval (x : Fin 8 → Bool) (b : Bool) :
      K.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn x ++ [b]) := by
    change (K.wires _).getD C.output false = (C.wires _).getD C.output false
    rw [sameWires]

  let bit := fun x : Fin 8 → Bool => (K.wires (List.ofFn x ++ [false])).getD (i + 1) false
  have hbit (x : Fin 8 → Bool) : bit x = u x := by
    change (K.wires _).getD (i + 1) false = _
    rw [sameWires]
    exact (model x false).2
  apply boundedControl K P.size (i + 1) hKF hKsz hKout hp (by dsimp [L] at tOutput; omega)
    (by omega) (by omega) hKPrefix hKRefs
  · intro x hx ha
    change bit x = false
    rw [hbit]
    exact hsens x hx ha
  · intro x
    change K.eval (List.ofFn x ++ [bit x]) = f x
    rw [sameEval, (model x (bit x)).1, hbit]
    exact hlo x
  · exact fun x => (sameEval x true).trans ((model x true).1.trans (hhi x))
