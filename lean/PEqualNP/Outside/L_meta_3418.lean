import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3418

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def mkBVShift (p : ℕ → Bool) (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * mkBVShift p (lo + 1) n + if p lo then 1 else 0

def mkBV (p : ℕ → Bool) : BitVec 24 :=
  BitVec.ofNat 24 (mkBVShift p 0 24)

lemma testBit_mkBVShift (n : ℕ) : ∀ (lo i : ℕ) (p : ℕ → Bool), i < n →
    (mkBVShift p lo n).testBit i = p (lo + i) := by
  induction n with
  | zero => intro lo i p hi; omega
  | succ n ih =>
    intro lo i p hi
    cases i with
    | zero =>
      simp only [mkBVShift, Nat.add_zero]
      cases p lo <;> simp
    | succ i =>
      simp only [mkBVShift]
      have hbit : (2 * mkBVShift p (lo + 1) n + if p lo then 1 else 0).testBit (i + 1) =
          (mkBVShift p (lo + 1) n).testBit i := by
        cases p lo <;> simp [Nat.testBit_succ, Nat.mul_add_div]
      rw [hbit, ih (lo + 1) i p (by omega)]
      congr 1
      omega

lemma getElem_mkBV (p : ℕ → Bool) (i : ℕ) (hi : i < 24) :
    (mkBV p)[i] = p i := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  simpa using testBit_mkBVShift 24 0 i p hi

lemma mkBV_congr {p q : ℕ → Bool} (h : ∀ i < 24, p i = q i) : mkBV p = mkBV q := by
  ext i hi
  rw [getElem_mkBV p i hi, getElem_mkBV q i hi, h i hi]

lemma mkBV_and (p q : ℕ → Bool) : mkBV (fun i => p i && q i) = mkBV p &&& mkBV q := by
  ext i hi
  rw [getElem_mkBV _ i hi, BitVec.getElem_and, getElem_mkBV p i hi, getElem_mkBV q i hi]

lemma mkBV_or (p q : ℕ → Bool) : mkBV (fun i => p i || q i) = mkBV p ||| mkBV q := by
  ext i hi
  rw [getElem_mkBV _ i hi, BitVec.getElem_or, getElem_mkBV p i hi, getElem_mkBV q i hi]

lemma mkBV_false : mkBV (fun _ => false) = (0 : BitVec 24) := by decide

lemma mkBV_true : mkBV (fun _ => true) = (16777215 : BitVec 24) := by decide

lemma bv_zero_and (x : BitVec 24) : (0 : BitVec 24) &&& x = 0 := by ext i hi; simp

lemma bv_and_zero (x : BitVec 24) : x &&& (0 : BitVec 24) = 0 := by ext i hi; simp

lemma bv_zero_or (x : BitVec 24) : (0 : BitVec 24) ||| x = x := by ext i hi; simp

lemma bv_or_zero (x : BitVec 24) : x ||| (0 : BitVec 24) = x := by ext i hi; simp

def masks : List ℕ :=
  [3, 6, 12, 24, 17, 33, 66, 132, 264, 160, 320, 288,
   42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]

def testInput (b : ℕ) : Fin 9 → Bool :=
  fun v => (masks.getD b 0).testBit v.val

def edgeFun (x : Fin 9 → Bool) : Bool :=
  x (0 : Fin 9) && x (1 : Fin 9) || x (1 : Fin 9) && x (2 : Fin 9) ||
  x (2 : Fin 9) && x (3 : Fin 9) || x (3 : Fin 9) && x (4 : Fin 9) ||
  x (4 : Fin 9) && x (0 : Fin 9) || x (0 : Fin 9) && x (5 : Fin 9) ||
  x (1 : Fin 9) && x (6 : Fin 9) || x (2 : Fin 9) && x (7 : Fin 9) ||
  x (3 : Fin 9) && x (8 : Fin 9) || x (5 : Fin 9) && x (7 : Fin 9) ||
  x (6 : Fin 9) && x (8 : Fin 9) || x (8 : Fin 9) && x (5 : Fin 9)

def prefix10 : List (BitVec 24) :=
  [5521457, 8532035, 3227782, 430348, 11083800,
   113184, 902208, 13501056, 15731968, 5689661]

def padPool : List (BitVec 24) :=
  [14053491, 7684279, 16605241, 5634609, 6145137, 14566065, 16010545,
   11759815, 8827215, 11219035, 8632931, 9434179, 13513411]

def padPairs : List (ℕ × ℕ) :=
  [(0,1),(0,2),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7)]

lemma mkBV_testInput (i : Fin 9) :
    mkBV (fun b => testInput b i) = prefix10.getD i.val 0 := by
  fin_cases i <;> decide

lemma bv_gate0_val :
    (5521457 : BitVec 24) ||| (430348 : BitVec 24) = (5689661 : BitVec 24) := by
  decide

lemma mkBV_edgeFun : mkBV (fun b => edgeFun (testInput b)) = (4095 : BitVec 24) := by
  decide

lemma prefix10_ext_nodup :
    ((0 : BitVec 24) :: (4095 : BitVec 24) :: prefix10).Nodup := by
  decide

lemma padPool_nodup : padPool.Nodup := by decide

lemma padPool_len : padPool.length = 13 := by decide

lemma prefix10_len : prefix10.length = 10 := by decide

lemma padPool_disjoint_bool :
    (padPool.all fun x => !((0 : BitVec 24) :: (4095 : BitVec 24) :: prefix10).contains x) = true := by
  decide

lemma padPool_disjoint :
    ∀ x ∈ padPool, x ∉ ((0 : BitVec 24) :: (4095 : BitVec 24) :: prefix10) := by
  intro x hx hmem
  have h1 := List.all_eq_true.mp padPool_disjoint_bool x hx
  have h2 : ((0 : BitVec 24) :: (4095 : BitVec 24) :: prefix10).contains x = true :=
    List.contains_iff_mem.mpr hmem
  rw [h2] at h1
  contradiction

lemma padPool_eq_map :
    padPool = padPairs.map (fun p => prefix10.getD p.1 0 ||| prefix10.getD p.2 0) := by
  decide

lemma padPairs_lt : ∀ p ∈ padPairs, p.1 < 10 ∧ p.2 < 10 := by
  decide

lemma padPool_valid :
    ∀ x ∈ padPool, ∃ u ∈ prefix10, ∃ y ∈ prefix10, x = u ||| y := by
  intro x hx
  rw [padPool_eq_map, List.mem_map] at hx
  rcases hx with ⟨p, hp, rfl⟩
  obtain ⟨h1, h2⟩ := padPairs_lt p hp
  have hp1 : p.1 < prefix10.length := by rw [prefix10_len]; exact h1
  have hp2 : p.2 < prefix10.length := by rw [prefix10_len]; exact h2
  refine ⟨prefix10.getD p.1 0, ?_, prefix10.getD p.2 0, ?_, rfl⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp1, Option.getD_some]
    exact List.getElem_mem hp1
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp2, Option.getD_some]
    exact List.getElem_mem hp2

lemma zero_ne_target : (0 : BitVec 24) ≠ (4095 : BitVec 24) := by decide

lemma allOnes_ne_target : (16777215 : BitVec 24) ≠ (4095 : BitVec 24) := by decide

lemma graph_any_eq (x : Fin 9 → Bool) :
    ([(1 : ℕ), 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77].any fun k =>
      x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 (k % 9))) = edgeFun x := by
  simp only [edgeFun, List.any_cons, List.any_nil]
  change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 ||
    (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 ||
    (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = _
  simp only [Bool.or_false, Bool.or_assoc]

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_singleton {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

lemma getD_of_length_le {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_wireStep_length (gs : List Gate) (init : List Bool) :
    (gs.foldl wireStep init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [wireStep, List.length_append, List.length_singleton]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (init : List Bool) (i : ℕ) (hi : i < init.length) :
    (gs.foldl wireStep init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (wireStep init g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [ih (wireStep init g) hi']
    exact getD_append_left init [g.op.eval (g.inputs.map fun k => init.getD k false)] i false hi

lemma foldl_wireStep_split :
    ∀ (j : ℕ) (gs : List Gate) (init : List Bool) (hj : j < gs.length),
      gs.foldl wireStep init =
        (gs.drop (j + 1)).foldl wireStep (wireStep ((gs.take j).foldl wireStep init) gs[j]) := by
  intro j
  induction j with
  | zero =>
    intro gs init hj
    cases gs with
    | nil => simp at hj
    | cons g gs => rfl
  | succ j ih =>
    intro gs init hj
    cases gs with
    | nil => simp at hj
    | cons g gs =>
      have hj' : j < gs.length := by simp at hj; omega
      simpa only [List.take_succ_cons, List.drop_succ_cons, List.foldl_cons, List.getElem_cons_succ]
        using ih gs (wireStep init g) hj'

lemma circuit_wires_length (C : Circuit) (x : Fin 9 → Bool) :
    (C.wires (List.ofFn x)).length = 9 + C.gates.length := by
  change (C.gates.foldl wireStep (List.ofFn x)).length = 9 + C.gates.length
  rw [foldl_wireStep_length, List.length_ofFn]

lemma circuit_wires_input (C : Circuit) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  change (C.gates.foldl wireStep (List.ofFn x)).getD i false = x ⟨i, hi⟩
  have hil : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hi
  rw [foldl_wireStep_prefix C.gates (List.ofFn x) i hil]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]

lemma circuit_wires_gate (C : Circuit)
    (hlen : C.gates.length = 15)
    (hread : ∀ j (hj : j < C.gates.length), ∀ a ∈ C.gates[j].inputs, a < 9 + j ∨ a = 24)
    (j : ℕ) (hj : j < 15) (x : Fin 9 → Bool) :
    (C.wires (List.ofFn x)).getD (9 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hjg : j < C.gates.length := by omega
  let W := (C.gates.take j).foldl wireStep (List.ofFn x)
  have hWlen : W.length = 9 + j := by
    dsimp only [W]
    rw [foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hmap : C.gates[j].inputs.map (fun i => W.getD i false) =
      C.gates[j].inputs.map (fun i => (C.wires (List.ofFn x)).getD i false) := by
    apply List.map_inj_left.mpr
    intro a ha
    rcases hread j hjg a ha with ha_lt | rfl
    · have hdecomp : C.wires (List.ofFn x) = (C.gates.drop j).foldl wireStep W := by
        change C.gates.foldl wireStep (List.ofFn x) = (C.gates.drop j).foldl wireStep W
        dsimp only [W]
        rw [← List.foldl_append, List.take_append_drop]
      have haW : a < W.length := by omega
      rw [hdecomp, foldl_wireStep_prefix (C.gates.drop j) W a haW]
    · have hwlen : (C.wires (List.ofFn x)).length = 24 := by
        rw [circuit_wires_length, hlen]
      rw [getD_of_length_le W 24 false (by omega),
          getD_of_length_le (C.wires (List.ofFn x)) 24 false (by omega)]
  have hsplit : C.wires (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl wireStep (wireStep W C.gates[j]) :=
    foldl_wireStep_split j C.gates (List.ofFn x) hjg
  have hlt1 : 9 + j < (wireStep W C.gates[j]).length := by
    simp only [wireStep, List.length_append, List.length_singleton]
    omega
  have hstep : (wireStep W C.gates[j]).getD (9 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => W.getD i false) := by
    dsimp only [wireStep]
    rw [← hWlen]
    exact getD_append_right_singleton W _ false
  have hlhs : (C.wires (List.ofFn x)).getD (9 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => W.getD i false) := by
    rw [hsplit, foldl_wireStep_prefix (C.gates.drop (j + 1)) (wireStep W C.gates[j]) (9 + j) hlt1]
    exact hstep
  rw [hlhs, hmap]

def wireBV (C : Circuit) (w : ℕ) : BitVec 24 :=
  mkBV fun b => (C.wires (List.ofFn (testInput b))).getD w false

lemma wireBV_input (C : Circuit) (i : ℕ) (hi : i < 9) :
    wireBV C i = prefix10.getD i 0 := by
  unfold wireBV
  rw [mkBV_congr fun b _ => circuit_wires_input C (testInput b) i hi]
  exact mkBV_testInput ⟨i, hi⟩

lemma wireBV_oob (C : Circuit) (hlen : C.gates.length = 15) :
    wireBV C 24 = 0 := by
  unfold wireBV
  rw [mkBV_congr (q := fun _ => false) fun b _ =>
    getD_of_length_le _ 24 false (by rw [circuit_wires_length, hlen])]
  exact mkBV_false

lemma wireBV_gate0 (C : Circuit) (hlen : C.gates.length = 15)
    (h0 : C.gates[(0 : ℕ)]? = Option.some { op := GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : Gate })
    (hread : ∀ j (hj : j < C.gates.length), ∀ a ∈ C.gates[j].inputs, a < 9 + j ∨ a = 24) :
    wireBV C 9 = 5689661 := by
  have hg0 : C.gates[0] = { op := GateOp.or, inputs := [0, 3] } := by
    have hq : C.gates[0]? = some { op := GateOp.or, inputs := [0, 3] } := h0
    rw [List.getElem?_eq_getElem (by omega)] at hq
    exact Option.some.inj hq
  have hfn : ∀ b < 24, (C.wires (List.ofFn (testInput b))).getD 9 false =
      ((C.wires (List.ofFn (testInput b))).getD 0 false ||
        (C.wires (List.ofFn (testInput b))).getD 3 false) := by
    intro b _
    have hc := circuit_wires_gate C hlen hread 0 (by omega) (testInput b)
    rw [hg0] at hc
    simpa [GateOp.eval] using hc
  calc
    wireBV C 9 = mkBV fun b => (C.wires (List.ofFn (testInput b))).getD 0 false ||
        (C.wires (List.ofFn (testInput b))).getD 3 false := mkBV_congr hfn
    _ = wireBV C 0 ||| wireBV C 3 := mkBV_or _ _
    _ = (5521457 : BitVec 24) ||| (430348 : BitVec 24) := by
      rw [wireBV_input C 0 (by omega), wireBV_input C 3 (by omega)]
      decide
    _ = 5689661 := bv_gate0_val

lemma wireBV_output (C : Circuit) (hout : C.output = 23)
    (hfun : circuitFun 9 C = fun x : Fin 9 → Bool =>
      [(1 : ℕ), 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77].any fun k =>
        x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 (k % 9))) :
    wireBV C 23 = 4095 := by
  have hfn : ∀ b < 24, (C.wires (List.ofFn (testInput b))).getD 23 false = edgeFun (testInput b) := by
    intro b _
    have heval : (C.wires (List.ofFn (testInput b))).getD 23 false = circuitFun 9 C (testInput b) := by
      rw [← hout]
      rfl
    rw [heval, hfun]
    exact graph_any_eq (testInput b)
  unfold wireBV
  rw [mkBV_congr hfn]
  exact mkBV_edgeFun

lemma wireBV_gate (C : Circuit) (hlen : C.gates.length = 15) (hmono : Monotone2 C)
    (hread : ∀ j (hj : j < C.gates.length), ∀ a ∈ C.gates[j].inputs, a < 9 + j ∨ a = 24)
    (j : ℕ) (hj : j < 15) :
    wireBV C (9 + j) = 0 ∨ wireBV C (9 + j) = 16777215 ∨
      (∃ a < 9 + j, wireBV C (9 + j) = wireBV C a) ∨
      (∃ a < 9 + j, ∃ b < 9 + j,
        wireBV C (9 + j) = wireBV C a &&& wireBV C b ∨
        wireBV C (9 + j) = wireBV C a ||| wireBV C b) := by
  have hjg : j < C.gates.length := by omega
  have hgate := hmono C.gates[j] (List.getElem_mem hjg)
  rcases hgate with ⟨hop, hilen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hbase : ∀ b < 24, (C.wires (List.ofFn (testInput b))).getD (9 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        (C.wires (List.ofFn (testInput b))).getD i false) :=
    fun b _ => circuit_wires_gate C hlen hread j hj (testInput b)
  rcases hin : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · rcases hop with hop | hop
    · right; left
      unfold wireBV
      rw [mkBV_congr (q := fun _ => true) fun k _ => by rw [hbase k (by omega), hop, hin]; rfl]
      exact mkBV_true
    · left
      unfold wireBV
      rw [mkBV_congr (q := fun _ => false) fun k _ => by rw [hbase k (by omega), hop, hin]; rfl]
      exact mkBV_false
  · have hsame : wireBV C (9 + j) = wireBV C a := by
      unfold wireBV
      apply mkBV_congr
      intro k _
      rw [hbase k (by omega), hin]
      rcases hop with hop | hop <;> simp [hop, GateOp.eval]
    have ha_read : a ∈ C.gates[j].inputs := by simp [hin]
    rcases hread j hjg a ha_read with ha | rfl
    · right; right; left; exact ⟨a, ha, hsame⟩
    · left; rw [hsame, wireBV_oob C hlen]
  · have ha_read : a ∈ C.gates[j].inputs := by simp [hin]
    have hb_read : b ∈ C.gates[j].inputs := by simp [hin]
    rcases hop with hop | hop
    · have hand : wireBV C (9 + j) = wireBV C a &&& wireBV C b := by
        unfold wireBV
        rw [← mkBV_and]
        apply mkBV_congr
        intro k _
        rw [hbase k (by omega), hop, hin]
        simp [GateOp.eval]
      rcases hread j hjg a ha_read with ha | rfl
      · rcases hread j hjg b hb_read with hb | rfl
        · right; right; right; exact ⟨a, ha, b, hb, Or.inl hand⟩
        · left; rw [hand, wireBV_oob C hlen, bv_and_zero]
      · left; rw [hand, wireBV_oob C hlen, bv_zero_and]
    · have hor : wireBV C (9 + j) = wireBV C a ||| wireBV C b := by
        unfold wireBV
        rw [← mkBV_or]
        apply mkBV_congr
        intro k _
        rw [hbase k (by omega), hop, hin]
        simp [GateOp.eval]
      rcases hread j hjg a ha_read with ha | rfl
      · rcases hread j hjg b hb_read with hb | rfl
        · right; right; right; exact ⟨a, ha, b, hb, Or.inr hor⟩
        · right; right; left; refine ⟨a, ha, ?_⟩; rw [hor, wireBV_oob C hlen, bv_or_zero]
      · rcases hread j hjg b hb_read with hb | rfl
        · right; right; left; refine ⟨b, hb, ?_⟩; rw [hor, wireBV_oob C hlen, bv_zero_or]
        · left; rw [hor, wireBV_oob C hlen, bv_zero_or]
  · simp [hin] at hilen

def findK (v : ℕ → BitVec 24) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if findK v n = 0 then (if v (9 + (n + 1)) = 4095 then n + 1 else 0) else findK v n

lemma findK_spec (v : ℕ → BitVec 24) : ∀ n : ℕ,
    (findK v n = 0 → ∀ k, 0 < k → k ≤ n → v (9 + k) ≠ 4095) ∧
    (findK v n ≠ 0 → 0 < findK v n ∧ findK v n ≤ n ∧ v (9 + findK v n) = 4095 ∧
      ∀ k, 0 < k → k < findK v n → v (9 + k) ≠ 4095) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro _ k hk0 hk; omega
    · intro hne; exfalso; exact hne rfl
  | succ n ih =>
    rcases ih with ⟨ih0, ihpos⟩
    by_cases hp : findK v n = 0
    · by_cases hhit : v (9 + (n + 1)) = 4095
      · have hfk_eq : findK v (n + 1) = n + 1 := by simp [findK, hp, hhit]
        rw [hfk_eq]
        refine ⟨fun h0 => by omega, fun _ => ⟨by omega, le_refl _, hhit, ?_⟩⟩
        intro k hk0 hklt
        exact ih0 hp k hk0 (by omega)
      · have hfk_eq : findK v (n + 1) = 0 := by simp only [findK, hp, hhit, ↓reduceIte]
        rw [hfk_eq]
        refine ⟨?_, fun h0 => (h0 rfl).elim⟩
        intro _ k hk0 hk
        by_cases hkn : k ≤ n
        · exact ih0 hp k hk0 hkn
        · have hkeq : k = n + 1 := by omega
          rw [hkeq]
          exact hhit
    · have hfk_eq : findK v (n + 1) = findK v n := by simp [findK, hp]
      rw [hfk_eq]
      obtain ⟨hpos, hle, heq, hmin⟩ := ihpos hp
      refine ⟨fun h0 => (hp h0).elim, fun _ => ⟨hpos, by omega, heq, hmin⟩⟩

def pushFresh (acc : List (BitVec 24)) (x : BitVec 24) : List (BitVec 24) :=
  if x = 0 ∨ x ∈ acc then acc else acc ++ [x]

def collectBase (v : ℕ → BitVec 24) : ℕ → List (BitVec 24)
  | 0 => prefix10
  | r + 1 => pushFresh (collectBase v r) (v (10 + r))

lemma collectBase_props (v : ℕ → BitVec 24) (k0 : ℕ)
    (hk0_le : k0 ≤ 14)
    (hinit : ∀ a < 10, v a = prefix10.getD a 0)
    (hmin : ∀ a < 9 + k0, v a ≠ 4095)
    (hstep : ∀ j < 15, v (9 + j) = 0 ∨ v (9 + j) = 16777215 ∨
      (∃ a < 9 + j, v (9 + j) = v a) ∨
      (∃ a < 9 + j, ∃ b < 9 + j, v (9 + j) = v a &&& v b ∨ v (9 + j) = v a ||| v b)) :
    ∀ r ≤ k0 - 1,
      let acc := collectBase v r
      acc.length ≤ 10 + r ∧
      acc.take 10 = prefix10 ∧
      ((0 : BitVec 24) :: (4095 : BitVec 24) :: acc).Nodup ∧
      (∀ a < 10 + r, v a ≠ 0 → v a ∈ acc) ∧
      (∀ m, 10 ≤ m → (hm : m < acc.length) →
        acc[m] = 16777215 ∨ ∃ u ∈ acc.take m, ∃ y ∈ acc.take m, acc[m] = u &&& y ∨ acc[m] = u ||| y) := by
  intro r hr
  induction r with
  | zero =>
    dsimp only [collectBase]
    refine ⟨by rw [prefix10_len], by rw [← prefix10_len, List.take_length], prefix10_ext_nodup, ?_, ?_⟩
    · intro a ha _
      rw [hinit a ha]
      have hlen10 : a < prefix10.length := by rw [prefix10_len]; exact ha
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen10, Option.getD_some]
      exact List.getElem_mem hlen10
    · intro m hm10 hm
      rw [prefix10_len] at hm
      omega
  | succ r ih =>
    have hr_prev : r ≤ k0 - 1 := by omega
    obtain ⟨ih_len, ih_take, ih_nodup, ih_cov, ih_gate⟩ := ih hr_prev
    set acc := collectBase v r
    set x := v (10 + r)
    have hj_lt15 : 1 + r < 15 := by omega
    have h10r_lt : 10 + r < 9 + k0 := by omega
    have h91r : 9 + (1 + r) = 10 + r := by omega
    by_cases hskip : x = 0 ∨ x ∈ acc
    · have heq : collectBase v (r + 1) = acc := by
        change (if x = 0 ∨ x ∈ acc then acc else acc ++ [x]) = acc
        simp only [hskip, ↓reduceIte]
      rw [heq]
      refine ⟨by omega, ih_take, ih_nodup, ?_, ih_gate⟩
      intro a ha hane
      by_cases halt : a < 10 + r
      · exact ih_cov a halt hane
      · have haeq : a = 10 + r := by omega
        subst haeq
        rcases hskip with h0 | hmem
        · exact (hane h0).elim
        · exact hmem
    · have hne0 : x ≠ 0 := fun h => hskip (Or.inl h)
      have hnotin : x ∉ acc := fun h => hskip (Or.inr h)
      have hne4095 : x ≠ 4095 := hmin (10 + r) h10r_lt
      have heq : collectBase v (r + 1) = acc ++ [x] := by
        change (if x = 0 ∨ x ∈ acc then acc else acc ++ [x]) = acc ++ [x]
        simp only [hskip, ↓reduceIte]
      rw [heq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · have h10le : 10 ≤ acc.length := by
          have := congrArg List.length ih_take
          rw [List.length_take, prefix10_len] at this
          omega
        rw [List.take_append_of_le_length h10le, ih_take]
      · have hnot0 : (0 : BitVec 24) ≠ x := hne0.symm
        have hnot4095 : (4095 : BitVec 24) ≠ x := hne4095.symm
        change ((0 :: 4095 :: acc) ++ [x]).Nodup
        rw [List.nodup_append]
        refine ⟨ih_nodup, List.nodup_singleton x, ?_⟩
        intro z hz1 z2 hz2
        simp only [List.mem_singleton] at hz2
        rw [hz2]
        intro hzx
        rw [hzx] at hz1
        simp only [List.mem_cons] at hz1
        rcases hz1 with h | h | hzacc
        · exact hnot0 h.symm
        · exact hnot4095 h.symm
        · exact hnotin hzacc
      · intro a ha hane
        simp only [List.mem_append, List.mem_singleton]
        by_cases halt : a < 10 + r
        · exact Or.inl (ih_cov a halt hane)
        · have haeq : a = 10 + r := by omega
          subst haeq
          exact Or.inr rfl
      · intro m hm10 hm
        simp only [List.length_append, List.length_singleton] at hm
        by_cases hm_lt : m < acc.length
        · rw [List.getElem_append_left hm_lt, List.take_append_of_le_length (by omega)]
          exact ih_gate m hm10 hm_lt
        · have hmeq : m = acc.length := by omega
          subst hmeq
          rw [List.getElem_append_right (le_refl acc.length)]
          simp only [Nat.sub_self, List.getElem_singleton]
          rw [List.take_append_of_le_length (le_refl acc.length), List.take_length]
          have hst := hstep (1 + r) hj_lt15
          rw [h91r] at hst
          rcases hst with h0 | hones | ⟨a, ha, heqa⟩ | ⟨a, ha, b, hb, hbin⟩
          · exact (hne0 h0).elim
          · exact Or.inl hones
          · have hane : v a ≠ 0 := by rw [← heqa]; exact hne0
            have hmem := ih_cov a ha hane
            rw [← heqa] at hmem
            exact (hnotin hmem).elim
          · right
            rcases hbin with hband | hbor
            · have ha0 : v a ≠ 0 := by
                intro h
                rw [h, bv_zero_and] at hband
                exact hne0 hband
              have hb0 : v b ≠ 0 := by
                intro h
                rw [h, bv_and_zero] at hband
                exact hne0 hband
              exact ⟨v a, ih_cov a ha ha0, v b, ih_cov b hb hb0, Or.inl hband⟩
            · have ha0 : v a ≠ 0 := by
                intro h
                rw [h, bv_zero_or] at hbor
                have hmem := ih_cov b hb (by rw [← hbor]; exact hne0)
                rw [← hbor] at hmem
                exact hnotin hmem
              have hb0 : v b ≠ 0 := by
                intro h
                rw [h, bv_or_zero] at hbor
                have hmem := ih_cov a ha (by rw [← hbor]; exact hne0)
                rw [← hbor] at hmem
                exact hnotin hmem
              exact ⟨v a, ih_cov a ha ha0, v b, ih_cov b hb hb0, Or.inr hbor⟩

lemma filter_not_contains_len (xs : List (BitVec 24)) : ∀ ys : List (BitVec 24), xs.Nodup →
    xs.length ≤ (xs.filter (fun x => !ys.contains x)).length + ys.length := by
  induction xs with
  | nil => intro ys _; simp
  | cons x xs ih =>
    intro ys hnd
    obtain ⟨hxnotin, hxs_nd⟩ := List.nodup_cons.mp hnd
    by_cases hmem : x ∈ ys
    · have hcongr : xs.filter (fun z => !ys.contains z) =
          xs.filter (fun z => !(ys.erase x).contains z) := by
        apply List.filter_congr
        intro z _
        have hzx : z ≠ x := fun h => hxnotin (by rwa [← h])
        simp [List.mem_erase_of_ne hzx]
      have hys_len : (ys.erase x).length + 1 = ys.length := by
        rw [List.length_erase_of_mem hmem]
        have hpos : 0 < ys.length := List.length_pos_of_mem hmem
        omega
      have ih_res := ih (ys.erase x) hxs_nd
      rw [← hcongr] at ih_res
      have hc : ys.contains x = true := List.contains_iff_mem.mpr hmem
      simp only [List.length_cons, List.filter_cons, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hc : ys.contains x = false := by
        cases h : ys.contains x
        · rfl
        · exact (hmem (List.contains_iff_mem.mp h)).elim
      have ih_res := ih ys hxs_nd
      simp only [List.length_cons, List.filter_cons, hc, Bool.not_false, ↓reduceIte]
      omega

lemma solve (C : Circuit)
    (hlen : C.gates.length = 15)
    (hout : C.output = 23)
    (h0 : C.gates[(0 : ℕ)]? = Option.some { op := GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : Gate })
    (hmono : Monotone2 C)
    (hread : ∀ j (hj : j < C.gates.length), ∀ a ∈ C.gates[j].inputs, a < 9 + j ∨ a = 24)
    (hfun : circuitFun 9 C = fun x : Fin 9 → Bool =>
      [(1 : ℕ), 11, 21, 31, 36, 5, 15, 25, 35, 52, 62, 77].any fun k =>
        x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 (k % 9))) :
    ∃ w : List (BitVec 24),
      w.length = 24 ∧
      w.take 10 = prefix10 ∧
      w.getD 23 0 = 4095 ∧
      ((0 : BitVec 24) :: w).Nodup ∧
      ∀ j : ℕ, 0 < j → j < 15 →
        have t : BitVec 24 := w.getD (9 + j) 0
        t = 16777215 ∨ ∃ u v : BitVec 24,
          u ∈ w.take (9 + j) ∧ v ∈ w.take (9 + j) ∧ (t = u &&& v ∨ t = u ||| v) := by
  let v := wireBV C
  have hv9 : v 9 = 5689661 := wireBV_gate0 C hlen h0 hread
  have hv23 : v 23 = 4095 := wireBV_output C hout hfun
  have hinit : ∀ a < 10, v a = prefix10.getD a 0 := by
    intro a ha
    by_cases ha9 : a < 9
    · exact wireBV_input C a ha9
    · have haeq : a = 9 := by omega
      subst haeq
      rw [hv9]
      decide
  let k0 := findK v 14
  have hfk := findK_spec v 14
  have hk0_ne0 : k0 ≠ 0 := by
    intro hz
    exact (hfk.1 hz 14 (by decide) (by decide)) hv23
  obtain ⟨hk0_pos, hk0_le, hv_k0, hk0_min⟩ := hfk.2 hk0_ne0
  have hmin : ∀ a < 9 + k0, v a ≠ 4095 := by
    intro a ha
    by_cases ha10 : a < 10
    · rw [hinit a ha10]
      have hlen10 : a < prefix10.length := by rw [prefix10_len]; exact ha10
      intro heq
      have hmem : (4095 : BitVec 24) ∈ prefix10 := by
        rw [← heq]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen10, Option.getD_some]
        exact List.getElem_mem hlen10
      exact (by decide : (4095 : BitVec 24) ∉ prefix10) hmem
    · have hlt : a - 9 < k0 := by omega
      have hne := hk0_min (a - 9) (by omega) hlt
      simpa [show 9 + (a - 9) = a by omega] using hne
  have hprops := collectBase_props v k0 hk0_le hinit hmin (wireBV_gate C hlen hmono hread)
    (k0 - 1) (le_refl (k0 - 1))
  dsimp only at hprops
  set base := collectBase v (k0 - 1)
  obtain ⟨hbase_len, hbase_take, hbase_nodup, hbase_cov, hbase_gate⟩ := hprops
  have hbase_ge10 : 10 ≤ base.length := by
    have := congrArg List.length hbase_take
    rw [List.length_take, prefix10_len] at this
    omega
  have hbase_le23 : base.length ≤ 23 := by omega
  have hcov_k0 : ∀ a < 9 + k0, v a ≠ 0 → v a ∈ base := by
    intro a ha
    exact hbase_cov a (by omega)
  have htarget_step : ∃ u ∈ base, ∃ y ∈ base, (4095 : BitVec 24) = u &&& y ∨ (4095 : BitVec 24) = u ||| y := by
    have hgk0 := wireBV_gate C hlen hmono hread k0 (by omega)
    change v (9 + k0) = 0 ∨ v (9 + k0) = 16777215 ∨ (∃ a < 9 + k0, v (9 + k0) = v a) ∨
      (∃ a < 9 + k0, ∃ b < 9 + k0, v (9 + k0) = v a &&& v b ∨ v (9 + k0) = v a ||| v b) at hgk0
    rw [hv_k0] at hgk0
    rcases hgk0 with h0' | hones' | ⟨a, ha, heqa⟩ | ⟨a, ha, b, hb, hbin⟩
    · exact (zero_ne_target h0'.symm).elim
    · exact (allOnes_ne_target hones'.symm).elim
    · exact (hmin a ha heqa.symm).elim
    · rcases hbin with hband | hbor
      · have ha0 : v a ≠ 0 := by
          intro h
          rw [h, bv_zero_and] at hband
          exact zero_ne_target hband.symm
        have hb0 : v b ≠ 0 := by
          intro h
          rw [h, bv_and_zero] at hband
          exact zero_ne_target hband.symm
        exact ⟨v a, hcov_k0 a ha ha0, v b, hcov_k0 b hb hb0, Or.inl hband⟩
      · have ha0 : v a ≠ 0 := by
          intro h
          rw [h, bv_zero_or] at hbor
          exact hmin b hb hbor.symm
        have hb0 : v b ≠ 0 := by
          intro h
          rw [h, bv_or_zero] at hbor
          exact hmin a ha hbor.symm
        exact ⟨v a, hcov_k0 a ha ha0, v b, hcov_k0 b hb hb0, Or.inr hbor⟩
  let mid := base.drop 10
  have hbase_eq : base = prefix10 ++ mid := by
    have h := List.take_append_drop 10 base
    rw [hbase_take] at h
    exact h.symm
  have hmid_len : mid.length = base.length - 10 := List.length_drop
  let avail := padPool.filter (fun x => !base.contains x)
  have havail_eq : avail = padPool.filter (fun x => !mid.contains x) := by
    dsimp only [avail]
    apply List.filter_congr
    intro x hx
    have hnp : x ∉ prefix10 := by
      have hd := padPool_disjoint x hx
      simp only [List.mem_cons] at hd
      intro hmem
      exact hd (Or.inr (Or.inr hmem))
    rw [hbase_eq]
    simp [hnp]
  have havail_len : 23 - base.length ≤ avail.length := by
    rw [havail_eq]
    have hfl := filter_not_contains_len padPool mid padPool_nodup
    rw [padPool_len, hmid_len] at hfl
    omega
  let pad := avail.take (23 - base.length)
  have hpad_len : pad.length = 23 - base.length := by
    dsimp only [pad]
    rw [List.length_take]
    omega
  have hpad_nodup : pad.Nodup :=
    (padPool_nodup.filter _).take
  have hpad_mem_avail : ∀ x ∈ pad, x ∈ avail :=
    fun x hx => List.mem_of_mem_take hx
  have hpad_mem_pool : ∀ x ∈ pad, x ∈ padPool :=
    fun x hx => (List.mem_filter.mp (hpad_mem_avail x hx)).1
  have hpad_notin_base : ∀ x ∈ pad, x ∉ base := by
    intro x hx hxb
    have hm := (List.mem_filter.mp (hpad_mem_avail x hx)).2
    have hc : base.contains x = true := List.contains_iff_mem.mpr hxb
    rw [hc] at hm
    simp at hm
  let w := base ++ pad ++ [4095]
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [w]
    simp only [List.length_append, List.length_singleton]
    omega
  · dsimp only [w]
    rw [List.append_assoc, List.take_append_of_le_length hbase_ge10, hbase_take]
  · dsimp only [w]
    have hbp_len : (base ++ pad).length = 23 := by
      rw [List.length_append]
      omega
    rw [← hbp_len]
    exact getD_append_right_singleton (base ++ pad) 4095 0
  · have hnodup_bp : ((0 : BitVec 24) :: (4095 : BitVec 24) :: (base ++ pad)).Nodup := by
      change (((0 : BitVec 24) :: (4095 : BitVec 24) :: base) ++ pad).Nodup
      rw [List.nodup_append]
      refine ⟨hbase_nodup, hpad_nodup, ?_⟩
      intro x hx1 y hy2 heq
      subst heq
      simp only [List.mem_cons] at hx1
      have hxp := hpad_mem_pool x hy2
      have hdisj := padPool_disjoint x hxp
      simp only [List.mem_cons] at hdisj
      rcases hx1 with rfl | rfl | hxb
      · exact hdisj (Or.inl rfl)
      · exact hdisj (Or.inr (Or.inl rfl))
      · exact hpad_notin_base x hy2 hxb
    have h0bp : ((0 : BitVec 24) :: (base ++ pad)).Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, (List.nodup_cons.mp hnodup_bp.of_cons).2⟩
      exact fun hm => (List.nodup_cons.mp hnodup_bp).1 (List.mem_cons_of_mem 4095 hm)
    change (((0 : BitVec 24) :: (base ++ pad)) ++ [4095]).Nodup
    rw [List.nodup_append]
    refine ⟨h0bp, List.nodup_singleton 4095, ?_⟩
    intro x hx1 y hy2
    simp only [List.mem_singleton] at hy2
    rw [hy2]
    intro heq
    rw [heq] at hx1
    have h4095 := List.nodup_cons.mp hnodup_bp.of_cons
    simp only [List.mem_cons] at hx1
    rcases hx1 with heq0 | hxmem
    · exact zero_ne_target heq0.symm
    · exact h4095.1 hxmem
  · intro j hj0 hj15
    dsimp only
    let m := 9 + j
    have hm10 : 10 ≤ m := by omega
    have hm23 : m ≤ 23 := by omega
    by_cases hm_base : m < base.length
    · have hwm : w.getD m 0 = base[m] := by
        dsimp only [w]
        rw [List.append_assoc, getD_append_left base (pad ++ [4095]) m 0 hm_base]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_base, Option.getD_some]
      have hwtake : w.take m = base.take m := by
        dsimp only [w]
        rw [List.append_assoc, List.take_append_of_le_length (le_of_lt hm_base)]
      rw [hwm, hwtake]
      rcases hbase_gate m hm10 hm_base with hones | ⟨u, hu, y, hy, heq⟩
      · exact Or.inl hones
      · exact Or.inr ⟨u, y, hu, hy, heq⟩
    · by_cases hm_eq23 : m = 23
      · have hj23 : 9 + j = 23 := hm_eq23
        have hwm : w.getD (9 + j) 0 = 4095 := by
          rw [hj23]
          dsimp only [w]
          have hbp_len : (base ++ pad).length = 23 := by rw [List.length_append]; omega
          rw [← hbp_len]
          exact getD_append_right_singleton (base ++ pad) 4095 0
        have hwtake23 : w.take 23 = base ++ pad := by
          dsimp only [w]
          have hbp_len : (base ++ pad).length = 23 := by rw [List.length_append]; omega
          rw [← hbp_len, List.take_left]
        rw [hwm, hj23, hwtake23]
        right
        rcases htarget_step with ⟨u, hu, y, hy, heq⟩
        exact ⟨u, y, List.mem_append_left pad hu, List.mem_append_left pad hy, heq⟩
      · have hm_lt23 : m < 23 := by omega
        have hidx_pad : m - base.length < pad.length := by omega
        have hwm : w.getD m 0 = pad[m - base.length] := by
          dsimp only [w]
          have hge : base.length ≤ m := by omega
          have hbp : m < (base ++ pad).length := by rw [List.length_append]; omega
          rw [getD_append_left (base ++ pad) [4095] m 0 hbp]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbp, Option.getD_some]
          rw [List.getElem_append_right hge]
        have hxpad : pad[m - base.length] ∈ pad := List.getElem_mem hidx_pad
        have hxpool : pad[m - base.length] ∈ padPool := hpad_mem_pool _ hxpad
        rcases padPool_valid _ hxpool with ⟨u, hu, y, hy, heq⟩
        have hwtake10 : w.take 10 = prefix10 := by
          dsimp only [w]
          rw [List.append_assoc, List.take_append_of_le_length hbase_ge10, hbase_take]
        have hu_w : u ∈ w.take m := by
          have hsub : w.take 10 ⊆ w.take m := by
            intro z hz
            have heq_t : (w.take m).take 10 = w.take 10 := by
              rw [List.take_take, Nat.min_eq_left hm10]
            rw [← heq_t] at hz
            exact List.mem_of_mem_take hz
          apply hsub
          rw [hwtake10]
          exact hu
        have hy_w : y ∈ w.take m := by
          have hsub : w.take 10 ⊆ w.take m := by
            intro z hz
            have heq_t : (w.take m).take 10 = w.take 10 := by
              rw [List.take_take, Nat.min_eq_left hm10]
            rw [← heq_t] at hz
            exact List.mem_of_mem_take hz
          apply hsub
          rw [hwtake10]
          exact hy
        change w.getD m 0 = 16777215 ∨ ∃ u v : BitVec 24,
          u ∈ w.take m ∧ v ∈ w.take m ∧ (w.getD m 0 = u &&& v ∨ w.getD m 0 = u ||| v)
        rw [hwm]
        right
        exact ⟨u, y, hu_w, hy_w, Or.inr heq⟩

end PEqualNP.Outside.L_meta_3418

theorem PEqualNP.Outside.L_meta_3418 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.gates.length = (15 : ℕ) →     x1.output = (23 : ℕ) →       x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →         PEqualNP.MetaComplexity.Monotone2 x1 →           (∀ (x6 : ℕ) (x7 : x6 < x1.gates.length), ∀ x8 ∈ x1.gates[x6].inputs, x8 < (9 : ℕ) + x6 ∨ x8 = (24 : ℕ)) →             (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (9 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (9 : ℕ)))) →               ∃ (x8 : List (BitVec (24 : ℕ))),                 x8.length = (24 : ℕ) ∧                   List.take (10 : ℕ) x8 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧                     x8.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧                       ((0 : BitVec (24 : ℕ)) :: x8).Nodup ∧                         ∀ (x9 : ℕ),                           (0 : ℕ) < x9 →                             x9 < (15 : ℕ) →                               have x12 : BitVec (24 : ℕ) := x8.getD ((9 : ℕ) + x9) (0 : BitVec (24 : ℕ));                               x12 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x13 : BitVec (24 : ℕ)) (x14 : BitVec (24 : ℕ)), x13 ∈ List.take ((9 : ℕ) + x9) x8 ∧ x14 ∈ List.take ((9 : ℕ) + x9) x8 ∧ (x12 = x13 &&& x14 ∨ x12 = x13 ||| x14) := by
  exact PEqualNP.Outside.L_meta_3418.solve
