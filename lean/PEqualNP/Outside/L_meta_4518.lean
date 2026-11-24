import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4518

def gateVal (V : ℕ → Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map V)

def valStepAt (q : ℕ) (V : ℕ → Bool) (g : Gate) : ℕ → Bool :=
  fun i => if i = q then gateVal V g else V i

def valFold : ℕ → (ℕ → Bool) → List Gate → (ℕ → Bool)
  | _, V, [] => V
  | q, V, g :: gs => valFold (q + 1) (valStepAt q V g) gs

def mapGate (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

def shiftA : ℕ → ℕ := fun i => if i < 9 then i else i + 1

def shiftB (m : ℕ) : ℕ → ℕ :=
  fun i => if i < 9 then i else if i < 9 + m then i + 1 else if i = 9 + m then 9 else i

def newGates (m : ℕ) (A B : List Gate) (g4 : Gate) : List Gate :=
  g4 :: (A.map (mapGate shiftA) ++ B.map (mapGate (shiftB m)))

lemma ofFn_length9 (x : Fin 9 → Bool) : (List.ofFn x).length = 9 := by simp

lemma getD_length_le (w : List Bool) (j : ℕ) (h : w.length ≤ j) : w.getD j false = false := by
  induction w generalizing j with
  | nil => rfl
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.length_cons] at h
      omega
    | succ m =>
      have h' : xs.length ≤ m := by
        simp only [List.length_cons] at h
        omega
      exact ih m h'

lemma getD_concat (w : List Bool) (b : Bool) (j : ℕ) :
    (w ++ [b]).getD j false = if j = w.length then b else w.getD j false := by
  rcases Nat.lt_trichotomy j w.length with h | h | h
  · rw [show (w ++ [b]).getD j false = w.getD j false from List.getD_append w [b] false j h,
      ite_eq_right (by omega)]
  · subst h
    rw [ite_eq_left rfl,
      show (w ++ [b]).getD w.length false = [b].getD (w.length - w.length) false from
        List.getD_append_right w [b] false w.length (le_refl w.length),
      Nat.sub_self]
    rfl
  · rw [ite_eq_right (by omega),
      show (w ++ [b]).getD j false = [b].getD (j - w.length) false from
        List.getD_append_right w [b] false j (by omega),
      getD_length_le w j (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, j - w.length = m + 1 := ⟨j - w.length - 1, by omega⟩
    rw [hm]
    rfl

lemma valFold_cons (q : ℕ) (V : ℕ → Bool) (g : Gate) (gs : List Gate) :
    valFold q V (g :: gs) = valFold (q + 1) (valStepAt q V g) gs := by
  simp only [valFold]

lemma valFold_append (q : ℕ) (V : ℕ → Bool) (gs hs : List Gate) :
    valFold q V (gs ++ hs) = valFold (q + gs.length) (valFold q V gs) hs := by
  induction gs generalizing q V hs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.cons_append, List.length_cons, valFold_cons, valFold_cons]
    rw [ih (q + 1) (valStepAt q V g) hs]
    rw [show q + 1 + gs.length = q + (gs.length + 1) from by omega]

lemma valFold_below (q : ℕ) (V : ℕ → Bool) (gs : List Gate) :
    ∀ i, i < q → valFold q V gs i = V i := by
  induction gs generalizing q V with
  | nil => intro i hi; rfl
  | cons g gs ih =>
    intro i hi
    rw [valFold_cons]
    rw [ih (q + 1) (valStepAt q V g) i (by omega)]
    simp only [valStepAt]
    rw [ite_eq_right (by omega)]

lemma valFold_beyond (q : ℕ) (V : ℕ → Bool) (gs : List Gate) :
    ∀ i, q + gs.length ≤ i → valFold q V gs i = V i := by
  induction gs generalizing q V with
  | nil => intro i hi; rfl
  | cons g gs ih =>
    intro i hi
    rw [valFold_cons]
    simp only [List.length_cons] at hi
    rw [ih (q + 1) (valStepAt q V g) i (by omega)]
    simp only [valStepAt]
    rw [ite_eq_right (by omega)]

lemma valFold_snoc (q : ℕ) (V : ℕ → Bool) (gs : List Gate) (g : Gate) :
    valFold q V (gs ++ [g]) = valStepAt (q + gs.length) (valFold q V gs) g := by
  rw [valFold_append]
  simp only [valFold]

lemma valFold_head (q : ℕ) (V : ℕ → Bool) (g : Gate) (gs : List Gate) (i : ℕ) (h : i = q) :
    valFold q V (g :: gs) i = gateVal V g := by
  rw [h, valFold_cons]
  rw [show valFold (q + 1) (valStepAt q V g) gs q = valStepAt q V g q from
    valFold_below (q + 1) (valStepAt q V g) gs q (by omega)]
  simp [valStepAt]

lemma valFold_getD (gs : List Gate) (w : List Bool) (V : ℕ → Bool)
    (hV : ∀ i, V i = w.getD i false) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = valFold w.length V gs i := by
  induction gs generalizing w V with
  | nil => intro i; exact (hV i).symm
  | cons g gs ih =>
    intro i
    have hb : gateVal V g = gateVal (fun j => w.getD j false) g := by
      simp only [gateVal]
      congr 1
      exact List.map_congr_left (fun j _ => hV j)
    have hV' : ∀ j, valStepAt w.length V g j
        = (w ++ [gateVal (fun j => w.getD j false) g]).getD j false := by
      intro j
      simp only [valStepAt]
      rw [getD_concat, hb]
      by_cases hj : j = w.length
      · rw [ite_eq_left hj, ite_eq_left hj]
      · rw [ite_eq_right hj, ite_eq_right hj]
        exact hV j
    have hrec := ih (w ++ [gateVal (fun j => w.getD j false) g]) (valStepAt w.length V g) hV' i
    rw [show (w ++ [gateVal (fun j => w.getD j false) g]).length = w.length + 1 from by simp] at hrec
    rw [List.foldl_cons, valFold_cons]
    exact hrec

lemma map_map_eta (l : List ℕ) (V : ℕ → Bool) (s : ℕ → ℕ) :
    (l.map s).map V = l.map (fun i => V (s i)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]

lemma gateVal_mapGate (V : ℕ → Bool) (s : ℕ → ℕ) (g : Gate) :
    gateVal V (mapGate s g) = gateVal (fun i => V (s i)) g := by
  simp only [gateVal, mapGate]
  rw [map_map_eta]

lemma valStepAt_congr {σ : ℕ → ℕ} (hinj : Function.Injective σ) {W V : ℕ → Bool}
    (h : ∀ i, W (σ i) = V i) (q : ℕ) (hq : σ q = q) (g : Gate) :
    ∀ i, valStepAt q W (mapGate σ g) (σ i) = valStepAt q V g i := by
  intro i
  have hgv : gateVal W (mapGate σ g) = gateVal V g := by
    rw [gateVal_mapGate]
    simp only [gateVal]
    congr 1
    exact List.map_congr_left (fun j _ => h j)
  simp only [valStepAt]
  by_cases hi : i = q
  · subst hi
    rw [ite_eq_left hq, ite_eq_left rfl]
    exact hgv
  · have hsi : ¬ σ i = q := by
      intro hs
      exact hi (hinj (by rw [hs, hq]))
    rw [ite_eq_right hsi, ite_eq_right hi]
    exact h i

lemma valFold_map {σ : ℕ → ℕ} (hinj : Function.Injective σ) :
    ∀ (gs : List Gate) (q : ℕ) (W V : ℕ → Bool), (∀ i, W (σ i) = V i) →
      (∀ i, q ≤ i → σ i = i) →
      ∀ i, valFold q W (gs.map (mapGate σ)) (σ i) = valFold q V gs i := by
  intro gs
  induction gs with
  | nil =>
    intro q W V h hq i
    simp only [List.map_nil, valFold]
    exact h i
  | cons g gs ih =>
    intro q W V h hq i
    have hstep := valStepAt_congr hinj h q (hq q (le_refl q)) g
    rw [List.map_cons, valFold_cons, valFold_cons]
    exact ih (q + 1) (valStepAt q W (mapGate σ g)) (valStepAt q V g) hstep
      (fun j hj => hq j (by omega)) i

lemma shiftA_lt (i : ℕ) (h : i < 9) : shiftA i = i := by
  simp only [shiftA]
  rw [ite_eq_left h]

lemma shiftA_ge (i : ℕ) (h : 9 ≤ i) : shiftA i = i + 1 := by
  simp only [shiftA]
  rw [ite_eq_right (by omega)]

lemma shiftB_lt (m i : ℕ) (h : i < 9) : shiftB m i = i := by
  simp only [shiftB]
  rw [ite_eq_left h]

lemma shiftB_mid (m i : ℕ) (h1 : 9 ≤ i) (h2 : i < 9 + m) : shiftB m i = i + 1 := by
  simp only [shiftB]
  rw [ite_eq_right (by omega), ite_eq_left h2]

lemma shiftB_top (m : ℕ) : shiftB m (9 + m) = 9 := by
  simp only [shiftB]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp

lemma shiftB_hi (m i : ℕ) (h : 9 + m < i) : shiftB m i = i := by
  simp only [shiftB]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

lemma shiftB_le (m i k : ℕ) (h : i < 9 + k) (hk : k ≤ m) : shiftB m i ≤ 9 + k := by
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · rw [shiftB_lt m i h9]
    omega
  · rcases Nat.lt_or_ge i (9 + m) with hm | hm
    · rw [shiftB_mid m i h9 hm]
      omega
    · rcases Nat.lt_or_ge (9 + m) i with hi | hi
      · rw [shiftB_hi m i hi]
        omega
      · have he : i = 9 + m := by omega
        rw [he, shiftB_top]
        omega

lemma shiftB_inj (m : ℕ) : Function.Injective (shiftB m) := by
  intro a b hab
  simp only [shiftB] at hab
  split_ifs at hab <;> omega

lemma shiftA_eq_shiftB (m i : ℕ) (h : i < 9 + m) : shiftA i = shiftB m i := by
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · rw [shiftA_lt i h9, shiftB_lt m i h9]
  · rw [shiftA_ge i h9, shiftB_mid m i h9 h]

lemma phase1_step (m : ℕ) (g4 : Gate) (V0 VN0 : ℕ → Bool) (P : List Gate) (g : Gate)
    (hk : P.length < m)
    (hV0 : ∀ i, 9 ≤ i → V0 i = false) (hVN0 : ∀ x, 10 ≤ x → VN0 x = false)
    (hInv : ∀ i, i < 9 + P.length →
      valFold 10 VN0 (P.map (mapGate shiftA)) (shiftB m i) = valFold 9 V0 P i) :
    ∀ i, i < 9 + (P ++ [g]).length →
      valFold 10 VN0 ((P ++ [g]).map (mapGate shiftA)) (shiftB m i) = valFold 9 V0 (P ++ [g]) i := by
  intro i hi
  rw [List.map_append, List.map_cons, List.map_nil]
  rw [valFold_snoc, valFold_snoc]
  simp only [List.length_map, List.length_append, List.length_singleton] at hi ⊢
  simp only [valStepAt]
  by_cases hic : i = 9 + P.length
  · have hσ : shiftB m i = 10 + P.length := by
      rw [shiftB_mid m i (by omega) (by omega), hic]
      omega
    rw [ite_eq_left hσ, ite_eq_left hic]
    rw [gateVal_mapGate]
    simp only [gateVal]
    congr 1
    refine List.map_congr_left ?_
    intro j hj
    rcases Nat.lt_or_ge j (9 + P.length) with hj' | hj'
    · rw [shiftA_eq_shiftB m j (by omega)]
      exact hInv j hj'
    · have h1 : valFold 9 V0 P j = false := by
        rw [valFold_beyond 9 V0 P j (by omega), hV0 j (by omega)]
      have h2 : valFold 10 VN0 (P.map (mapGate shiftA)) (shiftA j) = false := by
        rw [shiftA_ge j (by omega)]
        rw [show valFold 10 VN0 (P.map (mapGate shiftA)) (j + 1) = VN0 (j + 1) from
          valFold_beyond 10 VN0 (P.map (mapGate shiftA)) (j + 1) (by simp only [List.length_map]; omega)]
        exact hVN0 (j + 1) (by omega)
      rw [h1, h2]
  · have hi' : i < 9 + P.length := by omega
    have hσ : shiftB m i ≤ 9 + P.length := shiftB_le m i P.length (by omega) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right hic]
    exact hInv i hi'

lemma phase1_all (m : ℕ) (g4 : Gate) (V0 VN0 : ℕ → Bool)
    (hV0 : ∀ i, 9 ≤ i → V0 i = false) (hVN0 : ∀ x, 10 ≤ x → VN0 x = false)
    (hVN0in : ∀ i, i < 9 → VN0 i = V0 i) (R : List Gate) :
    ∀ (P : List Gate), P.length + R.length = m →
      (∀ i, i < 9 + P.length →
        valFold 10 VN0 (P.map (mapGate shiftA)) (shiftB m i) = valFold 9 V0 P i) →
      ∀ i, i < 9 + (P ++ R).length →
        valFold 10 VN0 ((P ++ R).map (mapGate shiftA)) (shiftB m i) = valFold 9 V0 (P ++ R) i := by
  induction R with
  | nil =>
    intro P hP hInv i hi
    simpa using hInv i (by simpa using hi)
  | cons g R ih =>
    intro P hP hInv i hi
    have hR : (g :: R).length = R.length + 1 := by simp
    have hlast : (P ++ [g]).length = P.length + 1 := by simp
    have hk : P.length < m := by omega
    have hstep : ∀ i, i < 9 + (P ++ [g]).length →
        valFold 10 VN0 ((P ++ [g]).map (mapGate shiftA)) (shiftB m i) = valFold 9 V0 (P ++ [g]) i :=
      phase1_step m g4 V0 VN0 P g hk hV0 hVN0 hInv
    have hP' : (P ++ [g]).length + R.length = m := by omega
    have hlen : ((P ++ [g]) ++ R).length = (P ++ g :: R).length := by simp
    have hnext := ih (P ++ [g]) hP' hstep i (by rw [hlen]; exact hi)
    simpa only [List.append_assoc, List.singleton_append] using hnext

lemma phase2_start (m : ℕ) (g4 : Gate) (V0 : ℕ → Bool) (A : List Gate)
    (hA : A.length = m) (_hV0 : ∀ i, 9 ≤ i → V0 i = false) (h4 : ∀ i ∈ g4.inputs, i < 9)
    (hInv : ∀ i, i < 9 + m →
      valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) (shiftB m i) = valFold 9 V0 A i) :
    ∀ i, valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) (shiftB m i)
      = valStepAt (9 + m) (valFold 9 V0 A) g4 i := by
  intro i
  rcases Nat.lt_trichotomy i (9 + m) with hlt | heq | hgt
  · rw [show valStepAt (9 + m) (valFold 9 V0 A) g4 i = valFold 9 V0 A i from by
      simp only [valStepAt]
      rw [ite_eq_right (by omega)]]
    exact hInv i hlt
  · rw [heq, shiftB_top]
    rw [show valStepAt (9 + m) (valFold 9 V0 A) g4 (9 + m) = gateVal (valFold 9 V0 A) g4 from by
      simp [valStepAt]]
    rw [show valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) 9 = valStepAt 9 V0 g4 9 from
      valFold_below 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) 9 (by omega)]
    rw [show valStepAt 9 V0 g4 9 = gateVal V0 g4 from by simp [valStepAt]]
    simp only [gateVal]
    congr 1
    refine List.map_congr_left ?_
    intro j hj
    rw [show valFold 9 V0 A j = V0 j from valFold_below 9 V0 A j (h4 j hj)]
  · rw [shiftB_hi m i hgt]
    rw [show valStepAt (9 + m) (valFold 9 V0 A) g4 i = valFold 9 V0 A i from by
      simp only [valStepAt]
      rw [ite_eq_right (by omega)]]
    rw [show valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) i = valStepAt 9 V0 g4 i from
      valFold_beyond 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) i
        (by simp only [List.length_map]; omega)]
    rw [show valStepAt 9 V0 g4 i = V0 i from by
      simp only [valStepAt]
      rw [ite_eq_right (by omega)]]
    rw [show valFold 9 V0 A i = V0 i from
      valFold_beyond 9 V0 A i (by omega)]

lemma reorder (m : ℕ) (A B : List Gate) (g4 : Gate) (V0 : ℕ → Bool)
    (hA : A.length = m) (hV0 : ∀ i, 9 ≤ i → V0 i = false) (h4 : ∀ i ∈ g4.inputs, i < 9) :
    ∀ i, valFold 9 V0 (newGates m A B g4) (shiftB m i) = valFold 9 V0 (A ++ g4 :: B) i := by
  have hVN0in : ∀ j, j < 9 → valStepAt 9 V0 g4 j = V0 j := by
    intro j hj
    simp only [valStepAt]
    rw [ite_eq_right (by omega)]
  have hVN0f : ∀ x, 10 ≤ x → valStepAt 9 V0 g4 x = false := by
    intro x hx
    simp only [valStepAt]
    rw [ite_eq_right (by omega), hV0 x (by omega)]
  have hInv0 : ∀ j, j < 9 + ([] : List Gate).length →
      valFold 10 (valStepAt 9 V0 g4) (([] : List Gate).map (mapGate shiftA)) (shiftB m j)
        = valFold 9 V0 ([] : List Gate) j := by
    intro j hj
    simp only [List.map_nil, List.length_nil, Nat.add_zero, valFold] at hj ⊢
    rw [shiftB_lt m j hj, hVN0in j hj]
  have hInvA := phase1_all m g4 V0 (valStepAt 9 V0 g4) hV0 hVN0f hVN0in A ([] : List Gate)
    (by rw [List.length_nil, Nat.zero_add]; exact hA) hInv0
  have hInvA' : ∀ j, j < 9 + m →
      valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)) (shiftB m j) = valFold 9 V0 A j := by
    intro j hj
    have h1 := hInvA j (by rw [List.nil_append, hA]; exact hj)
    simpa using h1
  have hJ := phase2_start m g4 V0 A hA hV0 h4 hInvA'
  have hmap := valFold_map (shiftB_inj m) B (10 + m)
    (valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)))
    (valStepAt (9 + m) (valFold 9 V0 A) g4) hJ (fun j hj => shiftB_hi m j (by omega))
  intro i
  have hL : valFold 9 V0 (newGates m A B g4) (shiftB m i)
      = valFold (10 + m) (valFold 10 (valStepAt 9 V0 g4) (A.map (mapGate shiftA)))
          (B.map (mapGate (shiftB m))) (shiftB m i) := by
    simp only [newGates]
    rw [valFold_cons, valFold_append]
    simp only [List.length_map, hA]
  have hR : valFold 9 V0 (A ++ g4 :: B) i
      = valFold (10 + m) (valStepAt (9 + m) (valFold 9 V0 A) g4) B i := by
    rw [valFold_append]
    simp only [hA]
    rw [valFold_cons]
    rw [show 9 + m + 1 = 10 + m from by omega]
  rw [hL, hR]
  exact hmap i

end PEqualNP.Outside.L_meta_4518

open PEqualNP.Outside.L_meta_4518

theorem PEqualNP.Outside.L_meta_4518 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates = x2 ++ x4 :: x3 → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x7 ∈ x4.inputs, x7 < (9 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = x1.size ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ∧ ∀ (x9 : Fin (9 : ℕ) → Bool), (x8.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = x4.op.eval (List.map (fun (x10 : ℕ) => (List.ofFn x9).getD x10 Bool.false) x4.inputs) := by
  intro x1 x2 x3 x4 hgates hfan h4
  refine ⟨⟨newGates x2.length x2 x3 x4, shiftB x2.length x1.output⟩, ?_, ?_, ?_, ?_⟩
  · intro gg hgg
    have hgg' : gg ∈ newGates x2.length x2 x3 x4 := hgg
    rw [show newGates x2.length x2 x3 x4
        = x4 :: (x2.map (mapGate shiftA) ++ x3.map (mapGate (shiftB x2.length))) from rfl] at hgg'
    rw [List.mem_cons] at hgg'
    rcases hgg' with h1 | h1
    · rw [h1]
      exact hfan x4 (by rw [hgates]; simp)
    · rw [List.mem_append] at h1
      rcases h1 with h2 | h2
      · rw [List.mem_map] at h2
        obtain ⟨g0, hg0, hg1⟩ := h2
        rw [← hg1]
        exact ⟨(hfan g0 (by rw [hgates]; simp [hg0])).1,
          by simpa [mapGate] using (hfan g0 (by rw [hgates]; simp [hg0])).2⟩
      · rw [List.mem_map] at h2
        obtain ⟨g0, hg0, hg1⟩ := h2
        rw [← hg1]
        exact ⟨(hfan g0 (by rw [hgates]; simp [hg0])).1,
          by simpa [mapGate] using (hfan g0 (by rw [hgates]; simp [hg0])).2⟩
  · show (newGates x2.length x2 x3 x4).length = x1.gates.length
    rw [hgates]
    simp only [newGates, List.length_cons, List.length_append, List.length_map]
    omega
  · funext x9
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires]
    rw [hgates]
    rw [valFold_getD (newGates x2.length x2 x3 x4) (List.ofFn x9)
      (fun j => (List.ofFn x9).getD j false) (fun j => rfl) (shiftB x2.length x1.output)]
    rw [valFold_getD (x2 ++ x4 :: x3) (List.ofFn x9)
      (fun j => (List.ofFn x9).getD j false) (fun j => rfl) x1.output]
    rw [ofFn_length9 x9]
    exact reorder x2.length x2 x3 x4 (fun j => (List.ofFn x9).getD j false) rfl
      (fun j hj => getD_length_le (List.ofFn x9) j (by rw [ofFn_length9 x9]; exact hj)) h4 x1.output
  · intro x9
    have hw : (⟨newGates x2.length x2 x3 x4, shiftB x2.length x1.output⟩ : Circuit).wires (List.ofFn x9)
        = (newGates x2.length x2 x3 x4).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x9) := rfl
    rw [hw, valFold_getD (newGates x2.length x2 x3 x4) (List.ofFn x9)
      (fun j => (List.ofFn x9).getD j false) (fun j => rfl) 9]
    rw [ofFn_length9 x9]
    rw [show newGates x2.length x2 x3 x4
        = x4 :: (x2.map (mapGate shiftA) ++ x3.map (mapGate (shiftB x2.length))) from rfl]
    rw [show valFold 9 (fun j => (List.ofFn x9).getD j false)
        (x4 :: (x2.map (mapGate shiftA) ++ x3.map (mapGate (shiftB x2.length)))) 9
        = gateVal (fun j => (List.ofFn x9).getD j false) x4 from
      valFold_head 9 (fun j => (List.ofFn x9).getD j false) x4
        (x2.map (mapGate shiftA) ++ x3.map (mapGate (shiftB x2.length))) 9 rfl]
    simp only [gateVal]
