import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3604

open PEqualNP.CircuitLowerBounds

private def fG (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

private def inVec (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 2]

private lemma inVec_len (x : Fin 9 → Bool) : (inVec x).length = 10 := by
  simp [inVec]

private lemma inVec_getD_lt9 (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (inVec x).getD i false = x ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn x).length := by simp [hi]
  rw [inVec, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen,
    List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn]

private lemma inVec_getD_9 (x : Fin 9 → Bool) :
    (inVec x).getD 9 false = (x 0 || x 2) := by
  simp [inVec, List.getD_eq_getElem?_getD]

private lemma inVec_getD_ge10 (x : Fin 9 → Bool) (i : ℕ) (hi : 10 ≤ i) :
    (inVec x).getD i false = false := by
  have hlen : (inVec x).length ≤ i := by rw [inVec_len]; exact hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma stepWire_getD_eq (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold stepWire
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

private lemma foldl_step_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl stepWire acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire acc g).length := by simp [stepWire]; omega
    rw [ih (stepWire acc g) hi', stepWire_getD_lt acc g i hi]

private lemma foldl_congr_avoid1 (gs : List Gate) (v : ℕ)
    (hv : v ∉ gs.flatMap Gate.inputs) (a b : List Bool)
    (hlen : a.length = b.length)
    (hagree : ∀ i, i ≠ v → a.getD i false = b.getD i false) :
    (gs.foldl stepWire a).length = (gs.foldl stepWire b).length ∧
    ∀ i, i ≠ v → (gs.foldl stepWire a).getD i false = (gs.foldl stepWire b).getD i false := by
  induction gs generalizing a b with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hv
    have hmap : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hagree i
      intro heq
      subst heq
      exact hv.1 hi
    have hbit : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      rw [hmap]
    simp only [List.foldl_cons]
    apply ih hv.2 (stepWire a g) (stepWire b g)
    · simp [stepWire, hlen]
    · intro i hi
      by_cases hilt : i < a.length
      · have hiltb : i < b.length := hlen ▸ hilt
        rw [stepWire_getD_lt a g i hilt, stepWire_getD_lt b g i hiltb]
        exact hagree i hi
      · by_cases hieq : i = a.length
        · subst hieq
          rw [stepWire_getD_eq, hlen, stepWire_getD_eq, hbit]
        · have hge1 : (stepWire a g).length ≤ i := by simp [stepWire]; omega
          have hge2 : (stepWire b g).length ≤ i := by simp [stepWire]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

private lemma foldl_congr_avoid2 (gs : List Gate) (u v : ℕ)
    (hu : u ∉ gs.flatMap Gate.inputs) (hv : v ∉ gs.flatMap Gate.inputs) (a b : List Bool)
    (hlen : a.length = b.length)
    (hagree : ∀ i, i ≠ u → i ≠ v → a.getD i false = b.getD i false) :
    (gs.foldl stepWire a).length = (gs.foldl stepWire b).length ∧
    ∀ i, i ≠ u → i ≠ v →
      (gs.foldl stepWire a).getD i false = (gs.foldl stepWire b).getD i false := by
  induction gs generalizing a b with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at hu hv
    have hmap : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hagree i
      · intro heq; subst heq; exact hu.1 hi
      · intro heq; subst heq; exact hv.1 hi
    have hbit : g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
      rw [hmap]
    simp only [List.foldl_cons]
    apply ih hu.2 hv.2 (stepWire a g) (stepWire b g)
    · simp [stepWire, hlen]
    · intro i hiu hiv
      by_cases hilt : i < a.length
      · have hiltb : i < b.length := hlen ▸ hilt
        rw [stepWire_getD_lt a g i hilt, stepWire_getD_lt b g i hiltb]
        exact hagree i hiu hiv
      · by_cases hieq : i = a.length
        · subst hieq
          rw [stepWire_getD_eq, hlen, stepWire_getD_eq, hbit]
        · have hge1 : (stepWire a g).length ≤ i := by simp [stepWire]; omega
          have hge2 : (stepWire b g).length ≤ i := by simp [stepWire]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

private def bitVec (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i.val

private def flipMask : Fin 9 → ℕ
  | ⟨0, _⟩ => 20
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 4
  | ⟨8, _⟩ => 8

private lemma flipMask_sep :
    ∀ v : Fin 9,
      let x := bitVec (flipMask v)
      let y : Fin 9 → Bool := fun i => if i = v then !x i else x i
      (x 0 || x 2) = (y 0 || y 2) ∧ fG x ≠ fG y := by
  decide

private def swapMaskOrd (a b : ℕ) : ℕ :=
  match a, b with
  | 0, 1 => 5
  | 0, 2 => 9
  | 0, 3 => 5
  | 0, 4 => 37
  | 0, 5 => 21
  | 0, 6 => 21
  | 0, 7 => 5
  | 0, 8 => 21
  | 1, 2 => 3
  | 1, 3 => 3
  | 1, 4 => 6
  | 1, 5 => 6
  | 1, 6 => 3
  | 1, 7 => 3
  | 1, 8 => 3
  | 2, 3 => 133
  | 2, 4 => 5
  | 2, 5 => 5
  | 2, 6 => 13
  | 2, 7 => 13
  | 2, 8 => 69
  | 3, 4 => 9
  | 3, 5 => 9
  | 3, 6 => 10
  | 3, 7 => 24
  | 3, 8 => 12
  | 4, 5 => 24
  | 4, 6 => 17
  | 4, 7 => 17
  | 4, 8 => 17
  | 5, 6 => 33
  | 5, 7 => 33
  | 5, 8 => 33
  | 6, 7 => 66
  | 6, 8 => 66
  | 7, 8 => 132
  | _, _ => 0

private def swapMask (u v : Fin 9) : ℕ :=
  if u.val < v.val then swapMaskOrd u.val v.val else swapMaskOrd v.val u.val

private lemma swapMask_sep :
    ∀ u v : Fin 9, u ≠ v →
      let x := bitVec (swapMask u v)
      let y : Fin 9 → Bool := fun i => if i = u then x v else if i = v then x u else x i
      (x 0 || x 2) = (y 0 || y 2) ∧ fG x ≠ fG y := by
  decide

end PEqualNP.Outside.L_meta_3604

theorem PEqualNP.Outside.L_meta_3604 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (10 : ℕ) ≤ x1.output →     (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) x3) →       have x4 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;       (∀ (x5 : Fin (9 : ℕ)), ↑x5 ∈ x4) ∧ ∀ x5 ∈ x1.gates, ∀ (x7 x8 : Fin (9 : ℕ)), x7 ≠ x8 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5.inputs = [↑x7, ↑x8] → (2 : ℕ) ≤ List.count (↑x7) x4 ∨ (2 : ℕ) ≤ List.count (↑x8) x4 := by
  intro x1 hout heval
  dsimp only
  constructor
  · intro v
    by_contra hv
    obtain ⟨hw9, hfne⟩ := PEqualNP.Outside.L_meta_3604.flipMask_sep v
    let x := PEqualNP.Outside.L_meta_3604.bitVec (PEqualNP.Outside.L_meta_3604.flipMask v)
    let y : Fin 9 → Bool := fun i => if i = v then !x i else x i
    have hagree : ∀ i, i ≠ v.val →
        (PEqualNP.Outside.L_meta_3604.inVec x).getD i false =
        (PEqualNP.Outside.L_meta_3604.inVec y).getD i false := by
      intro i hi
      by_cases hi9 : i < 9
      · rw [PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 x i hi9,
          PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 y i hi9]
        have hne : (⟨i, hi9⟩ : Fin 9) ≠ v := fun h => hi (congrArg Fin.val h)
        simp [y, hne]
      · by_cases hi9eq : i = 9
        · subst hi9eq
          rw [PEqualNP.Outside.L_meta_3604.inVec_getD_9, PEqualNP.Outside.L_meta_3604.inVec_getD_9]
          exact hw9
        · rw [PEqualNP.Outside.L_meta_3604.inVec_getD_ge10 x i (by omega),
            PEqualNP.Outside.L_meta_3604.inVec_getD_ge10 y i (by omega)]
    have hcongr := (PEqualNP.Outside.L_meta_3604.foldl_congr_avoid1 x1.gates v.val hv
      (PEqualNP.Outside.L_meta_3604.inVec x) (PEqualNP.Outside.L_meta_3604.inVec y)
      (by rw [PEqualNP.Outside.L_meta_3604.inVec_len, PEqualNP.Outside.L_meta_3604.inVec_len])
      hagree).2 x1.output (by omega)
    have hEvalEq : x1.eval (PEqualNP.Outside.L_meta_3604.inVec x) =
        x1.eval (PEqualNP.Outside.L_meta_3604.inVec y) := hcongr
    have hx := heval x
    have hy := heval y
    change x1.eval (PEqualNP.Outside.L_meta_3604.inVec x) = PEqualNP.Outside.L_meta_3604.fG x at hx
    change x1.eval (PEqualNP.Outside.L_meta_3604.inVec y) = PEqualNP.Outside.L_meta_3604.fG y at hy
    rw [hx, hy] at hEvalEq
    exact hfne hEvalEq
  · intro g0 hg0 u v huv hop hinp
    by_contra hlt
    push Not at hlt
    rcases hlt with ⟨hu_lt, hv_lt⟩
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hg0
    have hflat : x1.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs =
        l1.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs ++ [u.val, v.val] ++
        l2.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs := by
      rw [hsplit, List.flatMap_append, List.flatMap_cons, hinp, List.append_assoc]
    have huv_ne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    have hcu : (x1.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count u.val =
        (l1.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count u.val + 1 +
        (l2.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count u.val := by
      rw [hflat, List.count_append, List.count_append]
      simp [huv_ne]
    have hcv : (x1.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val =
        (l1.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val + 1 +
        (l2.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val := by
      rw [hflat, List.count_append, List.count_append]
      simp [huv_ne]
    have hu1 : u.val ∉ l1.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs :=
      List.count_eq_zero.mp (by omega)
    have hu2 : u.val ∉ l2.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs :=
      List.count_eq_zero.mp (by omega)
    have hv1 : v.val ∉ l1.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs :=
      List.count_eq_zero.mp (by omega)
    have hv2 : v.val ∉ l2.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs :=
      List.count_eq_zero.mp (by omega)
    obtain ⟨hw9, hfne⟩ := PEqualNP.Outside.L_meta_3604.swapMask_sep u v huv
    let x := PEqualNP.Outside.L_meta_3604.bitVec (PEqualNP.Outside.L_meta_3604.swapMask u v)
    let y : Fin 9 → Bool := fun i => if i = u then x v else if i = v then x u else x i
    let a := PEqualNP.Outside.L_meta_3604.inVec x
    let b := PEqualNP.Outside.L_meta_3604.inVec y
    have hagree0 : ∀ i, i ≠ u.val → i ≠ v.val → a.getD i false = b.getD i false := by
      intro i hiu hiv
      by_cases hi9 : i < 9
      · rw [PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 x i hi9,
          PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 y i hi9]
        have hneu : (⟨i, hi9⟩ : Fin 9) ≠ u := fun h => hiu (congrArg Fin.val h)
        have hnev : (⟨i, hi9⟩ : Fin 9) ≠ v := fun h => hiv (congrArg Fin.val h)
        simp [y, hneu, hnev]
      · by_cases hi9eq : i = 9
        · subst hi9eq
          rw [PEqualNP.Outside.L_meta_3604.inVec_getD_9, PEqualNP.Outside.L_meta_3604.inVec_getD_9]
          exact hw9
        · rw [PEqualNP.Outside.L_meta_3604.inVec_getD_ge10 x i (by omega),
            PEqualNP.Outside.L_meta_3604.inVec_getD_ge10 y i (by omega)]
    have h1 := PEqualNP.Outside.L_meta_3604.foldl_congr_avoid2 l1 u.val v.val hu1 hv1 a b
      (by rw [PEqualNP.Outside.L_meta_3604.inVec_len, PEqualNP.Outside.L_meta_3604.inVec_len])
      hagree0
    let w1a := l1.foldl PEqualNP.Outside.L_meta_3604.stepWire a
    let w1b := l1.foldl PEqualNP.Outside.L_meta_3604.stepWire b
    have hwu : w1a.getD u.val false = w1b.getD v.val false := by
      rw [PEqualNP.Outside.L_meta_3604.foldl_step_getD_lt l1 a u.val
          (by rw [PEqualNP.Outside.L_meta_3604.inVec_len]; omega),
        PEqualNP.Outside.L_meta_3604.foldl_step_getD_lt l1 b v.val
          (by rw [PEqualNP.Outside.L_meta_3604.inVec_len]; omega),
        PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 x u.val u.isLt,
        PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 y v.val v.isLt]
      simp [y, huv.symm]
    have hwv : w1a.getD v.val false = w1b.getD u.val false := by
      rw [PEqualNP.Outside.L_meta_3604.foldl_step_getD_lt l1 a v.val
          (by rw [PEqualNP.Outside.L_meta_3604.inVec_len]; omega),
        PEqualNP.Outside.L_meta_3604.foldl_step_getD_lt l1 b u.val
          (by rw [PEqualNP.Outside.L_meta_3604.inVec_len]; omega),
        PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 x v.val v.isLt,
        PEqualNP.Outside.L_meta_3604.inVec_getD_lt9 y u.val u.isLt]
      simp [y]
    have hg0_bit : g0.op.eval (g0.inputs.map fun i => w1a.getD i false) =
        g0.op.eval (g0.inputs.map fun i => w1b.getD i false) := by
      rw [hinp, List.map_cons, List.map_cons, List.map_nil, hwu, hwv]
      rcases hop with hand | hor
      · rw [hand]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_comm]
      · rw [hor]
        simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.or_comm]
    have hwlen : w1a.length = w1b.length := h1.1
    have hstep_agree : ∀ i, i ≠ u.val → i ≠ v.val →
        (PEqualNP.Outside.L_meta_3604.stepWire w1a g0).getD i false =
        (PEqualNP.Outside.L_meta_3604.stepWire w1b g0).getD i false := by
      intro i hiu hiv
      by_cases hilt : i < w1a.length
      · have hiltb : i < w1b.length := hwlen ▸ hilt
        rw [PEqualNP.Outside.L_meta_3604.stepWire_getD_lt w1a g0 i hilt,
          PEqualNP.Outside.L_meta_3604.stepWire_getD_lt w1b g0 i hiltb]
        exact h1.2 i hiu hiv
      · by_cases hieq : i = w1a.length
        · subst hieq
          rw [PEqualNP.Outside.L_meta_3604.stepWire_getD_eq, hwlen,
            PEqualNP.Outside.L_meta_3604.stepWire_getD_eq, hg0_bit]
        · have hge1 : (PEqualNP.Outside.L_meta_3604.stepWire w1a g0).length ≤ i := by
            simp [PEqualNP.Outside.L_meta_3604.stepWire]; omega
          have hge2 : (PEqualNP.Outside.L_meta_3604.stepWire w1b g0).length ≤ i := by
            simp [PEqualNP.Outside.L_meta_3604.stepWire]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    have h2 := PEqualNP.Outside.L_meta_3604.foldl_congr_avoid2 l2 u.val v.val hu2 hv2
      (PEqualNP.Outside.L_meta_3604.stepWire w1a g0) (PEqualNP.Outside.L_meta_3604.stepWire w1b g0)
      (by simp [PEqualNP.Outside.L_meta_3604.stepWire, hwlen]) hstep_agree
    have hEvalEq : x1.eval a = x1.eval b := by
      dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval]
      rw [PEqualNP.Outside.L_meta_3604.wires_eq_foldl, PEqualNP.Outside.L_meta_3604.wires_eq_foldl,
        hsplit, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
      exact h2.2 x1.output (by omega) (by omega)
    have hx := heval x
    have hy := heval y
    change x1.eval a = PEqualNP.Outside.L_meta_3604.fG x at hx
    change x1.eval b = PEqualNP.Outside.L_meta_3604.fG y at hy
    rw [hx, hy] at hEvalEq
    exact hfne hEvalEq
