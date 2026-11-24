import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2573

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def newGates (N o k : ℕ) : List Gate :=
  [⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [N, 20]⟩, ⟨GateOp.or, [N + 1, 24]⟩,
   ⟨GateOp.and, [0, N + 2]⟩,
   ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.or, [N + 4, 22]⟩, ⟨GateOp.or, [N + 5, 23]⟩,
   ⟨GateOp.and, [2, N + 6]⟩,
   ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [N + 8, 17]⟩, ⟨GateOp.or, [N + 9, 19]⟩,
   ⟨GateOp.and, [8, N + 10]⟩,
   ⟨GateOp.or, [N + 3, N + 7]⟩, ⟨GateOp.or, [N + 12, N + 11]⟩,
   ⟨GateOp.or, [o, N + 13]⟩, ⟨GateOp.or, [k, 12]⟩]

def ext (C : Circuit) (k : ℕ) : Circuit :=
  ⟨C.gates ++ newGates (25 + C.gates.length) C.output k, 25 + C.gates.length + 14⟩

def bigE (v : ℕ → Bool) : Bool :=
  ((v 0 && (((v 12 || v 14) || v 20) || v 24)) || (v 2 && (((v 12 || v 18) || v 22) || v 23)))
    || (v 8 && (((v 12 || v 16) || v 17) || v 19))

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma fold_pre (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ _ (by simp [stepW]; omega)]
    simp only [stepW]
    rw [List.getD_append _ _ _ _ hi]

lemma gA (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := List.getD_append _ _ _ _ h

lemma gR (l l' : List Bool) (j : ℕ) : (l ++ l').getD (l.length + j) false = l'.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma gR0 (l l' : List Bool) : (l ++ l').getD l.length false = l'.getD 0 false := by
  simpa using gR l l' 0

lemma tail (W : List Bool) (o k : ℕ) (h25 : 25 ≤ W.length) (ho : o < W.length)
    (hk : k < W.length) :
    let R := (newGates W.length o k).foldl stepW W
    R.getD (W.length + 14) false = (W.getD o false || bigE fun i => W.getD i false) ∧
    R.getD (W.length + 15) false = (W.getD k false || W.getD 12 false) := by
  simp only [newGates, List.foldl_cons, List.foldl_nil, stepW, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append]
  simp (disch := omega) only [gA, gR, gR0, List.getD_cons_succ, List.getD_cons_zero, GateOp.eval,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]
  refine ⟨?_, trivial⟩
  simp only [bigE]

lemma oget (x : Fin 25 → Bool) (n : ℕ) (h : n < 25) : (List.ofFn x).getD n false = x ⟨n, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

lemma ogetF (x : Fin 25 → Bool) (i : Fin 25) : (List.ofFn x).getD i.val false = x i :=
  oget x i.val i.isLt

lemma bigE_mono (w v : ℕ → Bool) (h : ∀ i, w i = true → v i = true) (hw : bigE w = true) :
    bigE v = true := by
  simp only [bigE, Bool.or_eq_true, Bool.and_eq_true] at hw ⊢
  rcases hw with ((⟨h1, (((h2 | h2) | h2) | h2)⟩ | ⟨h1, (((h2 | h2) | h2) | h2)⟩) |
      ⟨h1, (((h2 | h2) | h2) | h2)⟩)
  all_goals (have e1 := h _ h1; have e2 := h _ h2; simp [e1, e2])

lemma pairs : ∀ a b : Fin 25, a.val < 12 → 12 ≤ b.val →
    (a.val + b.val + 2) % 13 ∈ [0, 1, 3, 9] → a.val ∈ [0, 2, 8] →
    bigE (fun i => decide (i = a.val) || decide (i = b.val)) = true := by
  decide

lemma eiff (x : Fin 25 → Bool) :
    bigE (fun i => (List.ofFn x).getD i false) = true ↔
      ∃ (a b : Fin 25), a.val < 12 ∧ 12 ≤ b.val ∧ (a.val + b.val + 2) % 13 ∈ [0, 1, 3, 9] ∧
        a.val ∈ [0, 2, 8] ∧ x a = true ∧ x b = true := by
  constructor
  · intro h
    simp (disch := omega) only [bigE, oget, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((⟨h1, (((h2 | h2) | h2) | h2)⟩ | ⟨h1, (((h2 | h2) | h2) | h2)⟩) |
      ⟨h1, (((h2 | h2) | h2) | h2)⟩)
    all_goals (refine ⟨_, _, ?_, ?_, ?_, ?_, h1, h2⟩ <;> decide)
  · rintro ⟨a, b, h1, h2, h3, h4, ha, hb⟩
    refine bigE_mono _ _ ?_ (pairs a b h1 h2 h3 h4)
    intro i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · rw [ogetF]; exact ha
    · rw [ogetF]; exact hb

lemma mono (C : Circuit) (k : ℕ) (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (ext C k) := by
  intro g hg
  unfold ext newGates at hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | hg
  · exact h g hg
  · rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp

lemma vals (C : Circuit) (k : ℕ) (x : Fin 25 → Bool) (ho : C.output < 25 + C.gates.length)
    (hk : k < 25 + C.gates.length) :
    ((ext C k).wires (List.ofFn x)).getD (25 + C.gates.length + 14) false
        = (C.eval (List.ofFn x) || bigE fun i => (List.ofFn x).getD i false) ∧
    ((ext C k).wires (List.ofFn x)).getD (25 + C.gates.length + 15) false
        = ((C.wires (List.ofFn x)).getD k false || x 12) := by
  have hlen : (C.gates.foldl stepW (List.ofFn x)).length = 25 + C.gates.length := by
    rw [fold_len]; simp
  have hpre : ∀ i, i < 25 → (C.gates.foldl stepW (List.ofFn x)).getD i false
      = (List.ofFn x).getD i false := fun i hi =>
    fold_pre _ _ _ (by simp; omega)
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  unfold ext
  simp only
  rw [List.foldl_append]
  generalize C.gates.foldl stepW (List.ofFn x) = W at hlen hpre ⊢
  rw [← hlen]
  obtain ⟨t1, t2⟩ := tail W C.output k (by omega) (by omega) (by omega)
  have hE : (bigE fun i => W.getD i false) = bigE fun i => (List.ofFn x).getD i false := by
    simp only [bigE, hpre 0 (by norm_num), hpre 2 (by norm_num), hpre 8 (by norm_num),
      hpre 12 (by norm_num), hpre 14 (by norm_num), hpre 16 (by norm_num), hpre 17 (by norm_num),
      hpre 18 (by norm_num), hpre 19 (by norm_num), hpre 20 (by norm_num), hpre 22 (by norm_num),
      hpre 23 (by norm_num), hpre 24 (by norm_num)]
  refine ⟨?_, ?_⟩
  · rw [t1, hE]
  · rw [t2, hpre 12 (by norm_num), oget x 12 (by norm_num)]
    rfl

end PEqualNP.Outside.L_meta_2573

theorem PEqualNP.Outside.L_meta_2573 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (16 : ℕ) ∧ x6.output < (25 : ℕ) + x6.size ∧ x7 < (25 : ℕ) + x6.size ∧ ∀ (x8 : Fin (25 : ℕ) → Bool), (x6.eval (List.ofFn x8) = Bool.true ↔ x1.eval (List.ofFn x8) = Bool.true ∨ ∃ (x9 : Fin (25 : ℕ)) (x10 : Fin (25 : ℕ)), ↑x9 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x10 ∧ (↑x9 + ↑x10 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x9 ∈ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) ∧ (x6.wires (List.ofFn x8)).getD x7 Bool.false = ((x1.wires (List.ofFn x8)).getD x2 Bool.false || x8 (12 : Fin (25 : ℕ))) := by
  intro C k hC ho hk
  refine ⟨PEqualNP.Outside.L_meta_2573.ext C k, 25 + C.gates.length + 15,
    PEqualNP.Outside.L_meta_2573.mono C k hC, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2573.ext,
      PEqualNP.Outside.L_meta_2573.newGates]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2573.ext,
      PEqualNP.Outside.L_meta_2573.newGates]
    omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2573.ext,
      PEqualNP.Outside.L_meta_2573.newGates]
    omega
  · intro x
    have hs : C.size = C.gates.length := rfl
    rw [hs] at ho hk
    obtain ⟨w1, w2⟩ := PEqualNP.Outside.L_meta_2573.vals C k x ho hk
    refine ⟨?_, w2⟩
    have he : (PEqualNP.Outside.L_meta_2573.ext C k).eval (List.ofFn x)
        = ((PEqualNP.Outside.L_meta_2573.ext C k).wires (List.ofFn x)).getD
          (25 + C.gates.length + 14) false := rfl
    rw [he, w1, Bool.or_eq_true, PEqualNP.Outside.L_meta_2573.eiff]
