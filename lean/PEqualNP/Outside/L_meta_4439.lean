import Mathlib
import PEqualNP.Defs

-- The second gate is an OR of at most two wires, each an input, the first gate x4 OR x6, or a
-- missing wire (false): it is the OR of a set of inputs. One of the four automorphisms of the
-- graph that fix {4, 6} moves that set to a listed one; relabeling the inputs of the remaining
-- gates by it gives the circuit on the eleven wires.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4439

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => by simp [run]
  | g :: gs, w => by rw [run_cons, run_len gs]; simp; omega

theorem run_pre : ∀ (gs : List Gate) (w : List Bool) (r : ℕ), r < w.length →
    (run gs w).getD r false = w.getD r false
  | [], _, _, _ => rfl
  | g :: gs, w, r, hr => by
    rw [run_cons, run_pre gs _ r (by simp; omega), List.getD_append _ _ _ _ hr]

-- Relabeling the reads by a map that fixes every wire from k on and keeps the first k wires
-- below k.
theorem remap_run (τ : ℕ → ℕ) : ∀ (gs : List Gate) (k : ℕ) (wo wn : List Bool),
    (∀ i, k ≤ i → τ i = i) → (∀ i < k, τ i < k) → wo.length = k → wn.length = k →
    (∀ i < k, wn.getD (τ i) false = wo.getD i false) →
    ∀ i, (run (gs.map fun g => ⟨g.op, g.inputs.map τ⟩) wn).getD (τ i) false =
      (run gs wo).getD i false
  | [], k, wo, wn, hfix, hlt, ho, hn, h => by
    intro i
    by_cases hi : i < k
    · exact h i hi
    · rw [hfix i (by omega)]
      simp only [run, List.map_nil, List.foldl_nil]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | g :: gs, k, wo, wn, hfix, hlt, ho, hn, h => by
    have hall : ∀ i, wn.getD (τ i) false = wo.getD i false := by
      intro i
      by_cases hi : i < k
      · exact h i hi
      · rw [hfix i (by omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
    have hval : ((g.inputs.map τ).map fun r => wn.getD r false) =
        g.inputs.map (fun r => wo.getD r false) := by
      rw [List.map_map]; exact List.map_congr_left (fun r _ => hall r)
    simp only [List.map_cons, run_cons]
    rw [hval]
    apply remap_run τ gs (k + 1)
    · intro i hi; exact hfix i (by omega)
    · intro i hi
      by_cases hik : i < k
      · have := hlt i hik; omega
      · rw [hfix i (by omega)]; exact hi
    · simp [ho]
    · simp [hn]
    · intro i hi
      by_cases hik : i < k
      · rw [List.getD_append _ _ _ _ (by rw [hn]; exact hlt i hik),
          List.getD_append _ _ _ _ (by rw [ho]; exact hik)]
        exact h i hik
      · have hie : i = k := by omega
        subst hie
        rw [hfix i le_rfl, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hn, ho]

-- The four automorphisms of the graph that fix the set {4, 6}.
def sig : Fin 4 → Fin 9 → Fin 9 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![1, 0, 5, 8, 6, 2, 4, 7, 3],
    ![3, 8, 5, 0, 4, 2, 6, 7, 1], ![8, 3, 2, 1, 6, 5, 4, 7, 0]]

def F (x1 : Fin 9 → Bool) : Bool :=
  [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ),
    (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) =>
      x1 (Fin.ofNat 9 (x2 / 10)) && x1 (Fin.ofNat 9 (x2 % 10))

theorem F_sig : ∀ (k : Fin 4) (z : Fin 9 → Bool), F (fun i => z (sig k i)) = F z := by
  decide +kernel

-- Kinds of a read wire of the second gate: an input, the first gate, or nothing (false).
def kind (i : ℕ) : Fin 11 := if h : i < 9 then ⟨i, by omega⟩ else if i = 9 then 9 else 10

def kval (k : Fin 11) (x : Fin 9 → Bool) : Bool :=
  if h : k.val < 9 then x ⟨k.val, h⟩ else if k.val = 9 then (x 4 || x 6) else false

def km (k : Fin 11) : ℕ := if k.val < 9 then 2 ^ k.val else if k.val = 9 then 80 else 0

theorem kval_km : ∀ (k : Fin 11) (x : Fin 9 → Bool),
    kval k x = decide (∃ v : Fin 9, (km k).testBit v = true ∧ x v = true) := by
  decide +kernel

def img (σ : Fin 9 → Fin 9) (m : ℕ) : ℕ :=
  (List.finRange 9).foldl (fun (acc : ℕ) (v : Fin 9) => if m.testBit v.val then acc ||| 2 ^ (σ v).val else acc) 0

def choice (a b : Fin 11) : Fin 4 :=
  if img (sig 0) (km a ||| km b) ∈ reps then 0
  else if img (sig 1) (km a ||| km b) ∈ reps then 1
  else if img (sig 2) (km a ||| km b) ∈ reps then 2 else 3
where reps : List ℕ := [0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144,
  81, 84, 208]

def rep (a b : Fin 11) : ℕ := img (sig (choice a b)) (km a ||| km b)

theorem rep_mem : ∀ a b : Fin 11, rep a b ∈ ([0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257,
    20, 36, 132, 144, 81, 84, 208] : List ℕ) := by decide +kernel

theorem rep_bit : ∀ (a b : Fin 11) (v : Fin 9),
    (rep a b).testBit (sig (choice a b) v) = (km a ||| km b).testBit v := by decide +kernel

theorem rep_low : ∀ (a b : Fin 11) (u : ℕ), 9 ≤ u → (rep a b).testBit u = false := by
  intro a b u hu
  have hlt : rep a b < 2 ^ 9 := by
    have : ∀ a b : Fin 11, rep a b < 512 := by decide +kernel
    exact this a b
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hu))

theorem sig_surj : ∀ (k : Fin 4) (u : Fin 9), ∃ v, sig k v = u := by decide

theorem sig46 : ∀ (k : Fin 4) (z : Fin 9 → Bool), (z (sig k 4) || z (sig k 6)) = (z 4 || z 6) := by
  decide +kernel

-- The value of the second gate under relabeling is the listed OR.
theorem rep_val (a b : Fin 11) (z : Fin 9 → Bool) :
    decide (∃ u : Fin 9, (rep a b).testBit u = true ∧ z u = true) =
      (kval a (fun i => z (sig (choice a b) i)) || kval b (fun i => z (sig (choice a b) i))) := by
  rw [kval_km, kval_km, ← Bool.decide_or]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨u, hu, hz⟩
    obtain ⟨v, rfl⟩ := sig_surj (choice a b) u
    rw [rep_bit, Nat.testBit_or] at hu
    rcases Bool.or_eq_true_iff.mp hu with h | h
    · exact Or.inl ⟨v, h, hz⟩
    · exact Or.inr ⟨v, h, hz⟩
  · rintro (⟨v, hv, hz⟩ | ⟨v, hv, hz⟩)
    · exact ⟨sig (choice a b) v, by rw [rep_bit, Nat.testBit_or, hv, Bool.true_or], hz⟩
    · exact ⟨sig (choice a b) v, by rw [rep_bit, Nat.testBit_or, hv, Bool.or_true], hz⟩

def kOf (l : List ℕ) (j : ℕ) : Fin 11 := match l[j]? with | some i => kind i | none => 10

theorem ofFn_snoc2 (z : Fin 9 → Bool) (a b : Bool) :
    List.ofFn (Fin.snoc (Fin.snoc z a) b : Fin 11 → Bool) = List.ofFn z ++ [a, b] := by
  rw [List.ofFn_succ', List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.append_assoc]
  rfl

theorem bget (x : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn x ++ [x 4 || x 6]).getD i false = kval (kind i) x := by
  unfold kind kval
  by_cases h9 : i < 9
  · rw [List.getD_append _ _ _ _ (by simpa using h9), List.getD_eq_getElem _ _ (by simpa using h9),
      List.getElem_ofFn]
    simp [h9]
  · by_cases he : i = 9
    · subst he; simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [h9, he]

theorem main (C : Circuit) (hfan : FanInTwo C)
    (hw9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6))
    (hf : circuitFun 9 C = F)
    (hop : Option.map (fun g : Gate => g.op) C.gates[1]? = some GateOp.or) (hsz : C.size ≤ 15) :
    ∃ x8 ∈ ([0, 1, 4, 16, 128, 80, 3, 5, 9, 17, 33, 65, 129, 257, 20, 36, 132, 144, 81, 84, 208] :
      List ℕ), ∃ x9 : Circuit, FanInTwo x9 ∧ x9.size ≤ 13 ∧ ∀ z : Fin 9 → Bool,
      circuitFun 11 x9 (Fin.snoc (Fin.snoc z (z 4 || z 6))
        (decide (∃ u : Fin 9, x8.testBit u = true ∧ z u = true))) = F z := by
  obtain ⟨gs, o⟩ := C
  match gs, hfan, hw9, hf, hop, hsz with
  | [], _, _, _, hop, _ => simp at hop
  | [_], _, _, _, hop, _ => simp at hop
  | g0 :: g1 :: rest, hfan, hw9, hf, hop, hsz =>
    have hg1 : g1.op = GateOp.or := by simpa using hop
    have hl1 : g1.inputs.length ≤ 2 := (hfan g1 (by simp)).2
    have hg0 : ∀ x : Fin 9 → Bool,
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
      intro x
      have h := hw9 x
      change (run (g0 :: g1 :: rest) (List.ofFn x)).getD 9 false = _ at h
      rw [run_cons, run_pre _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)] at h
      simpa using h
    let v1 : (Fin 9 → Bool) → Bool := fun x =>
      g1.op.eval (g1.inputs.map fun i => (List.ofFn x ++ [x 4 || x 6]).getD i false)
    have hrun : ∀ x : Fin 9 → Bool, run (g0 :: g1 :: rest) (List.ofFn x) =
        run rest ((List.ofFn x ++ [x 4 || x 6]) ++ [v1 x]) := by
      intro x; rw [run_cons, run_cons, hg0 x]
    set a := kOf g1.inputs 0 with ha
    set b := kOf g1.inputs 1 with hb
    have kv10 : ∀ x : Fin 9 → Bool, kval 10 x = false := fun x => by simp [kval]
    have hv1 : ∀ x : Fin 9 → Bool, v1 x = (kval a x || kval b x) := by
      intro x
      simp only [v1, hg1, ha, hb]
      match hins : g1.inputs, hl1 with
      | [], _ => simp only [List.map_nil, kOf, List.getElem?_nil, kv10]; rfl
      | [i], _ =>
        simp only [List.map_cons, List.map_nil, bget, kOf, List.getElem?_cons_zero,
          List.getElem?_cons_succ, List.getElem?_nil, kv10]
        simp [GateOp.eval]
      | [i, j], _ =>
        simp only [List.map_cons, List.map_nil, bget, kOf, List.getElem?_cons_zero,
          List.getElem?_cons_succ]
        simp [GateOp.eval]
      | _ :: _ :: _ :: _, h => simp at h
    let σ := sig (choice a b)
    let τ : ℕ → ℕ := fun i => if h : i < 9 then (σ ⟨i, h⟩).val else i
    refine ⟨rep a b, rep_mem a b, ⟨rest.map (fun g => ⟨g.op, g.inputs.map τ⟩), τ o⟩, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      obtain ⟨hop', hlen'⟩ := hfan g' (by simp [hg'])
      exact ⟨hop', by simpa using hlen'⟩
    · simp only [Circuit.size, List.length_map]
      simp only [Circuit.size, List.length_cons] at hsz
      omega
    · intro z
      let x : Fin 9 → Bool := fun i => z (σ i)
      let wo := (List.ofFn x ++ [x 4 || x 6]) ++ [v1 x]
      let wn := List.ofFn z ++ [z 4 || z 6, decide (∃ u : Fin 9, (rep a b).testBit u = true ∧ z u = true)]
      have hwo : wo.length = 11 := by simp [wo]
      have hwn : wn.length = 11 := by simp [wn]
      have hcorr : ∀ i < 11, wn.getD (τ i) false = wo.getD i false := by
        intro i hi
        by_cases h9 : i < 9
        · have hτ : τ i = (σ ⟨i, h9⟩).val := by simp [τ, h9]
          rw [hτ]
          have hs := (σ ⟨i, h9⟩).isLt
          rw [List.getD_append _ _ _ _ (by simpa using hs), List.getD_eq_getElem _ _ (by simpa using hs),
            List.getElem_ofFn]
          rw [List.getD_append _ _ _ _ (by simp; omega), bget]
          simp [kind, kval, h9, x]
        · have hτ : τ i = i := by simp [τ, h9]
          rw [hτ]
          by_cases he : i = 9
          · subst he
            simp only [wn, wo]
            rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp),
              List.getD_append_right _ _ _ _ (by simp)]
            simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
            exact (sig46 (choice a b) z).symm
          · have h10 : i = 10 := by omega
            subst h10
            simp only [wn, wo]
            rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
            simp only [List.length_ofFn, List.length_append, List.length_singleton]
            show decide _ = v1 x
            rw [hv1 x]
            exact rep_val a b z
      have key := remap_run τ rest 11 wo wn
        (fun i hi => by simp [τ]; omega)
        (fun i hi => by
          by_cases h9 : i < 9
          · simp only [τ, h9, dite_true]; have := (σ ⟨i, h9⟩).isLt; omega
          · simp only [τ, h9, dite_false]; exact hi)
        hwo hwn hcorr o
      change (run (rest.map fun g => ⟨g.op, g.inputs.map τ⟩)
        (List.ofFn (Fin.snoc (Fin.snoc z (z 4 || z 6))
          (decide (∃ u : Fin 9, (rep a b).testBit u = true ∧ z u = true))))).getD (τ o) false = F z
      rw [ofFn_snoc2]
      change (run (rest.map fun g => ⟨g.op, g.inputs.map τ⟩) wn).getD (τ o) false = F z
      rw [key]
      have hx : (run rest wo).getD o false = circuitFun 9 ⟨g0 :: g1 :: rest, o⟩ x := by
        show _ = (run (g0 :: g1 :: rest) (List.ofFn x)).getD o false
        rw [hrun x]
      rw [hx, hf]
      exact F_sig (choice a b) z

end PEqualNP.Outside.L_meta_4439

theorem PEqualNP.Outside.L_meta_4439 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → x2.size ≤ (15 : ℕ) → ∃ x8 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (16 : ℕ), (128 : ℕ), (80 : ℕ), (3 : ℕ), (5 : ℕ), (9 : ℕ), (17 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (20 : ℕ), (36 : ℕ), (132 : ℕ), (144 : ℕ), (81 : ℕ), (84 : ℕ), (208 : ℕ)], ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size ≤ (13 : ℕ) ∧ ∀ (x10 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x9 (Fin.snoc (Fin.snoc x10 (x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x11 : Fin (9 : ℕ)), x8.testBit ↑x11 = Bool.true ∧ x10 x11 = Bool.true))) = x1 x10 := by
  intro f C hfan hw9 hf hop hsz
  exact PEqualNP.Outside.L_meta_4439.main C hfan hw9 hf hop hsz
