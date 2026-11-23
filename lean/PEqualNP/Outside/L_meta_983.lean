import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_983

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_append (gs1 gs2 : List Gate) (w : List Bool) :
    (gs1 ++ gs2).foldl step w = gs2.foldl step (gs1.foldl step w) :=
  List.foldl_append

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step_length]
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a (List.mem_cons_self ..)]
    congr 1
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

lemma foldl_getD_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
    exact getD_append_left w _ i false hi

lemma step_and_eval (w : List Bool) (a b : ℕ) :
    (step w ⟨GateOp.and, [a, b]⟩).getD w.length false = (w.getD a false && w.getD b false) := by
  simp [step, GateOp.eval]

lemma step_or_eval (w : List Bool) (a b : ℕ) :
    (step w ⟨GateOp.or, [a, b]⟩).getD w.length false = (w.getD a false || w.getD b false) := by
  simp [step, GateOp.eval]

def addOrChain (base : ℕ) : ℕ → List ℕ → List Gate × ℕ
  | cur, [] => ([], cur)
  | cur, v :: vs =>
    let g : Gate := ⟨GateOp.or, [cur, v]⟩
    let res := addOrChain (base + 1) base vs
    (g :: res.1, res.2)

lemma addOrChain_mono (base cur : ℕ) (vs : List ℕ) :
    ∀ g ∈ (addOrChain base cur vs).1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction vs generalizing base cur with
  | nil => intro g hg; simp [addOrChain] at hg
  | cons v vs ih =>
    intro g hg
    simp only [addOrChain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨by simp, by simp⟩
    · exact ih (base + 1) base g hg

lemma addOrChain_spec (w : List Bool) (cur : ℕ) (vs : List ℕ)
    (hcur : cur < w.length) (hvs : ∀ v ∈ vs, v < w.length) :
    let res := addOrChain w.length cur vs
    res.2 < (res.1.foldl step w).length ∧
    (res.1.foldl step w).getD res.2 false = (w.getD cur false || vs.any (fun v => w.getD v false)) := by
  induction vs generalizing w cur with
  | nil =>
    simp [addOrChain, hcur]
  | cons v vs ih =>
    simp only [addOrChain, List.foldl_cons, List.any_cons]
    set w' := step w ⟨GateOp.or, [cur, v]⟩
    have hw'_len : w'.length = w.length + 1 := step_length w _
    have hvs' : ∀ u ∈ vs, u < w'.length := fun u hu => by
      have := hvs u (List.mem_cons_of_mem v hu); omega
    have hbase : w.length < w'.length := by omega
    have hrec := ih w' w.length hbase hvs'
    rw [hw'_len] at hrec
    refine ⟨hrec.1, ?_⟩
    rw [hrec.2]
    have hhead : w'.getD w.length false = (w.getD cur false || w.getD v false) := step_or_eval w cur v
    have htail : vs.any (fun u => w'.getD u false) = vs.any (fun u => w.getD u false) :=
      list_any_congr vs _ _ (fun u hu => getD_append_left w _ u false (hvs u (List.mem_cons_of_mem v hu)))
    rw [hhead, htail, Bool.or_assoc]

def addBlocks (base : ℕ) : List (ℕ × ℕ × List ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | (u, v0, vs) :: rest =>
    let orRes := addOrChain base v0 vs
    let base1 := base + orRes.1.length
    let andGate : Gate := ⟨GateOp.and, [u, orRes.2]⟩
    let restRes := addBlocks (base1 + 1) rest
    (orRes.1 ++ [andGate] ++ restRes.1, base1 :: restRes.2)

lemma addBlocks_mono (base : ℕ) (bs : List (ℕ × ℕ × List ℕ)) :
    ∀ g ∈ (addBlocks base bs).1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction bs generalizing base with
  | nil => intro g hg; simp [addBlocks] at hg
  | cons b bs ih =>
    rcases b with ⟨u, v0, vs⟩
    intro g hg
    simp only [addBlocks, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | rfl) | hg
    · exact addOrChain_mono base v0 vs g hg
    · exact ⟨by simp, by simp⟩
    · exact ih _ g hg

lemma addBlocks_spec (w : List Bool) (bs : List (ℕ × ℕ × List ℕ))
    (hbs : ∀ b ∈ bs, b.1 < w.length ∧ b.2.1 < w.length ∧ ∀ v ∈ b.2.2, v < w.length) :
    let res := addBlocks w.length bs
    (∀ t ∈ res.2, t < (res.1.foldl step w).length) ∧
    res.2.any (fun t => (res.1.foldl step w).getD t false) =
      bs.any (fun b => w.getD b.1 false && (w.getD b.2.1 false || b.2.2.any (fun v => w.getD v false))) := by
  induction bs generalizing w with
  | nil => simp [addBlocks]
  | cons b bs ih =>
    rcases b with ⟨u, v0, vs⟩
    have hb0 := hbs (u, v0, vs) (List.mem_cons_self ..)
    simp only [addBlocks, List.any_cons]
    set orRes := addOrChain w.length v0 vs
    set w1 := orRes.1.foldl step w
    have hw1_len : w1.length = w.length + orRes.1.length := foldl_length _ _
    set andGate : Gate := ⟨GateOp.and, [u, orRes.2]⟩
    set w2 := step w1 andGate
    have hw2_len : w2.length = w1.length + 1 := step_length _ _
    have hOr := addOrChain_spec w v0 vs hb0.2.1 hb0.2.2
    have hAnd : w2.getD w1.length false = (w.getD u false && (w.getD v0 false || vs.any (fun v => w.getD v false))) := by
      have h1 := step_and_eval w1 u orRes.2
      rw [h1, foldl_getD_old orRes.1 w u hb0.1, hOr.2]
    have hbs' : ∀ b' ∈ bs, b'.1 < w2.length ∧ b'.2.1 < w2.length ∧ ∀ v ∈ b'.2.2, v < w2.length := by
      intro b' hb'
      have h' := hbs b' (List.mem_cons_of_mem _ hb')
      refine ⟨by omega, by omega, fun v hv => by have := h'.2.2 v hv; omega⟩
    have hrec := ih w2 hbs'
    have hfold : (orRes.1 ++ [andGate] ++ (addBlocks (w.length + orRes.1.length + 1) bs).1).foldl step w =
        (addBlocks w2.length bs).1.foldl step w2 := by
      rw [hw2_len, hw1_len, foldl_append, foldl_append]
      rfl
    rw [hfold]
    have hw1_lt : w.length + orRes.1.length < ((addBlocks w2.length bs).1.foldl step w2).length := by
      rw [foldl_length]; omega
    constructor
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact hw1_lt
      · rw [← hw1_len, ← hw2_len] at ht
        exact hrec.1 t ht
    · have hhead : ((addBlocks w2.length bs).1.foldl step w2).getD (w.length + orRes.1.length) false =
          w2.getD w1.length false := by
        rw [← hw1_len]
        exact foldl_getD_old _ w2 w1.length (by omega)
      rw [← hw1_len, ← hw2_len]
      rw [hw1_len, hhead, hAnd, hrec.2]
      congr 1
      have hget : ∀ z < w.length, w2.getD z false = w.getD z false := fun z hz => by
        show (step w1 andGate).getD z false = w.getD z false
        rw [step, getD_append_left w1 _ z false (by omega)]
        exact foldl_getD_old orRes.1 w z hz
      exact list_any_congr bs _ _ fun b' hb' => by
        have h' := hbs b' (List.mem_cons_of_mem _ hb')
        rw [hget b'.1 h'.1, hget b'.2.1 h'.2.1]
        congr 2
        exact list_any_congr b'.2.2 _ _ (fun v hv => hget v (h'.2.2 v hv))

def buildCover (n : ℕ) (bs : List (ℕ × ℕ × List ℕ)) : Circuit :=
  let bRes := addBlocks n bs
  match bRes.2 with
  | [] => ⟨[], n⟩
  | t0 :: ts =>
    let oRes := addOrChain (n + bRes.1.length) t0 ts
    ⟨bRes.1 ++ oRes.1, oRes.2⟩

lemma buildCover_mono (n : ℕ) (bs : List (ℕ × ℕ × List ℕ)) : Monotone2 (buildCover n bs) := by
  unfold buildCover Monotone2
  dsimp only
  cases h : (addBlocks n bs).2 with
  | nil => intro g hg; simp at hg
  | cons t0 ts =>
    intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact addBlocks_mono n bs g hg
    · exact addOrChain_mono _ t0 ts g hg

lemma buildCover_eval (n : ℕ) (bs : List (ℕ × ℕ × List ℕ))
    (hbs : ∀ b ∈ bs, b.1 < n ∧ b.2.1 < n ∧ ∀ v ∈ b.2.2, v < n)
    (x : Fin n → Bool) :
    (buildCover n bs).eval (List.ofFn x) =
      bs.any (fun b => (List.ofFn x).getD b.1 false &&
        ((List.ofFn x).getD b.2.1 false || b.2.2.any (fun v => (List.ofFn x).getD v false))) := by
  set w := List.ofFn x
  have hw_len : w.length = n := List.length_ofFn
  have hbsw : ∀ b ∈ bs, b.1 < w.length ∧ b.2.1 < w.length ∧ ∀ v ∈ b.2.2, v < w.length := by
    rw [hw_len]; exact hbs
  have hB := addBlocks_spec w bs hbsw
  dsimp only at hB
  rw [hw_len] at hB
  unfold buildCover Circuit.eval Circuit.wires
  dsimp only
  cases h : (addBlocks n bs).2 with
  | nil =>
    rw [h] at hB
    simp only [List.foldl_nil, List.getD, List.any_nil] at hB ⊢
    rw [List.getElem?_eq_none (by omega)]
    exact hB.2
  | cons t0 ts =>
    rw [h] at hB
    set bG := (addBlocks n bs).1
    set w1 := bG.foldl step w
    have hw1_len : w1.length = n + bG.length := by rw [foldl_length, hw_len]
    have ht0 : t0 < w1.length := hB.1 t0 (List.mem_cons_self ..)
    have hts : ∀ t ∈ ts, t < w1.length := fun t ht => hB.1 t (List.mem_cons_of_mem t0 ht)
    have hO := addOrChain_spec w1 t0 ts ht0 hts
    dsimp only at hO
    rw [hw1_len] at hO
    have hfold : (bG ++ (addOrChain (n + bG.length) t0 ts).1).foldl step w =
        (addOrChain (n + bG.length) t0 ts).1.foldl step w1 := foldl_append _ _ _
    change ((bG ++ (addOrChain (n + bG.length) t0 ts).1).foldl step w).getD (addOrChain (n + bG.length) t0 ts).2 false = _
    rw [hfold, hO.2]
    exact hB.2


def bs0 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, []), (3, 4, [5]), (4, 5, [])]

lemma conj0 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x := by
  refine ⟨buildCover 6 bs0, buildCover_mono 6 bs0, by decide, fun x => ?_⟩
  rw [buildCover_eval 6 bs0 (by decide) x]
  simp only [bs0, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs1 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, []), (3, 4, []), (5, 6, [])]

lemma conj1 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs1, buildCover_mono 7 bs1, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs1 (by decide) x]
  simp only [bs1, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs2 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, []), (3, 5, []), (4, 6, [])]

lemma conj2 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨buildCover 7 bs2, buildCover_mono 7 bs2, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs2 (by decide) x]
  simp only [bs2, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs3 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (3, 5, []), (4, 6, [])]

lemma conj3 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨buildCover 7 bs3, buildCover_mono 7 bs3, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs3 (by decide) x]
  simp only [bs3, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs4 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, []), (3, 4, [5]), (4, 6, [])]

lemma conj4 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x := by
  refine ⟨buildCover 7 bs4, buildCover_mono 7 bs4, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs4 (by decide) x]
  simp only [bs4, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs5 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, []), (3, 4, []), (5, 4, [6])]

lemma conj5 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs5, buildCover_mono 7 bs5, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs5 (by decide) x]
  simp only [bs5, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs6 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, []), (4, 5, [6]), (5, 6, [])]

lemma conj6 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs6, buildCover_mono 7 bs6, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs6 (by decide) x]
  simp only [bs6, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs7 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (2, 5, []), (3, 6, []), (4, 1, [5])]

lemma conj7 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x := by
  refine ⟨buildCover 7 bs7, buildCover_mono 7 bs7, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs7 (by decide) x]
  simp only [bs7, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs8 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2]), (1, 3, []), (4, 2, [6]), (5, 3, [6])]

lemma conj8 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs8, buildCover_mono 7 bs8, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs8 (by decide) x]
  simp only [bs8, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs9 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4, 5, 6]), (1, 2, []), (3, 4, [])]

lemma conj9 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x := by
  refine ⟨buildCover 7 bs9, buildCover_mono 7 bs9, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs9 (by decide) x]
  simp only [bs9, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs10 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4, 5]), (1, 2, [6]), (3, 4, [])]

lemma conj10 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x := by
  refine ⟨buildCover 7 bs10, buildCover_mono 7 bs10, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs10 (by decide) x]
  simp only [bs10, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs11 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4, 5]), (1, 2, []), (3, 4, []), (5, 6, [])]

lemma conj11 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs11, buildCover_mono 7 bs11, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs11 (by decide) x]
  simp only [bs11, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs12 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5, 6]), (3, 4, [])]

lemma conj12 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x := by
  refine ⟨buildCover 7 bs12, buildCover_mono 7 bs12, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs12 (by decide) x]
  simp only [bs12, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs13 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5]), (2, 6, []), (3, 4, [])]

lemma conj13 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x := by
  refine ⟨buildCover 7 bs13, buildCover_mono 7 bs13, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs13 (by decide) x]
  simp only [bs13, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs14 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5]), (3, 4, [6])]

lemma conj14 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x := by
  refine ⟨buildCover 7 bs14, buildCover_mono 7 bs14, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs14 (by decide) x]
  simp only [bs14, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs15 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5]), (3, 4, []), (5, 6, [])]

lemma conj15 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs15, buildCover_mono 7 bs15, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs15 (by decide) x]
  simp only [bs15, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs16 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5]), (6, 3, [5])]

lemma conj16 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs16, buildCover_mono 7 bs16, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs16 (by decide) x]
  simp only [bs16, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs17 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, []), (3, 5, [6]), (5, 6, [])]

lemma conj17 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs17, buildCover_mono 7 bs17, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs17 (by decide) x]
  simp only [bs17, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs18 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, []), (4, 6, []), (5, 3, [6])]

lemma conj18 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs18, buildCover_mono 7 bs18, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs18 (by decide) x]
  simp only [bs18, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs19 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (2, 1, [5]), (3, 6, []), (4, 1, [6])]

lemma conj19 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x := by
  refine ⟨buildCover 7 bs19, buildCover_mono 7 bs19, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs19 (by decide) x]
  simp only [bs19, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs20 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (3, 5, [6]), (4, 5, [])]

lemma conj20 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x := by
  refine ⟨buildCover 7 bs20, buildCover_mono 7 bs20, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs20 (by decide) x]
  simp only [bs20, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs21 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (3, 5, [6]), (5, 6, [])]

lemma conj21 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs21, buildCover_mono 7 bs21, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs21 (by decide) x]
  simp only [bs21, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs22 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (5, 3, [4, 6])]

lemma conj22 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs22, buildCover_mono 7 bs22, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs22 (by decide) x]
  simp only [bs22, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs23 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (4, 6, []), (5, 3, [6])]

lemma conj23 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs23, buildCover_mono 7 bs23, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs23 (by decide) x]
  simp only [bs23, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs24 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, []), (4, 3, [5, 6]), (5, 6, [])]

lemma conj24 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs24, buildCover_mono 7 bs24, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs24 (by decide) x]
  simp only [bs24, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs25 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (2, 5, []), (3, 6, []), (4, 1, [5, 6])]

lemma conj25 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x := by
  refine ⟨buildCover 7 bs25, buildCover_mono 7 bs25, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs25 (by decide) x]
  simp only [bs25, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs26 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4, 5, 6]), (1, 2, []), (3, 4, []), (5, 6, [])]

lemma conj26 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs26, buildCover_mono 7 bs26, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs26 (by decide) x]
  simp only [bs26, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs27 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5, 6]), (3, 4, []), (5, 6, [])]

lemma conj27 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs27, buildCover_mono 7 bs27, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs27 (by decide) x]
  simp only [bs27, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs28 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3, 4]), (1, 2, [5]), (3, 4, [6]), (5, 6, [])]

lemma conj28 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs28, buildCover_mono 7 bs28, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs28 (by decide) x]
  simp only [bs28, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs29 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (2, 5, []), (6, 3, [4, 5])]

lemma conj29 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs29, buildCover_mono 7 bs29, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs29 (by decide) x]
  simp only [bs29, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

def bs30 : List (ℕ × ℕ × List ℕ) := [(0, 1, [2, 3]), (1, 2, [4]), (3, 5, [6]), (5, 4, [6])]

lemma conj30 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x := by
  refine ⟨buildCover 7 bs30, buildCover_mono 7 bs30, by decide, fun x => ?_⟩
  rw [buildCover_eval 7 bs30 (by decide) x]
  simp only [bs30, List.any_cons, List.any_nil, Bool.or_false, List.getD, List.getElem?_ofFn]
  simp only [Bool.and_or_distrib_left, Bool.or_assoc]
  ac_rfl

end PEqualNP.Outside.L_meta_983

theorem PEqualNP.Outside.L_meta_983 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) ∧ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) :=
  ⟨PEqualNP.Outside.L_meta_983.conj0, PEqualNP.Outside.L_meta_983.conj1, PEqualNP.Outside.L_meta_983.conj2, PEqualNP.Outside.L_meta_983.conj3, PEqualNP.Outside.L_meta_983.conj4, PEqualNP.Outside.L_meta_983.conj5, PEqualNP.Outside.L_meta_983.conj6, PEqualNP.Outside.L_meta_983.conj7, PEqualNP.Outside.L_meta_983.conj8, PEqualNP.Outside.L_meta_983.conj9, PEqualNP.Outside.L_meta_983.conj10, PEqualNP.Outside.L_meta_983.conj11, PEqualNP.Outside.L_meta_983.conj12, PEqualNP.Outside.L_meta_983.conj13, PEqualNP.Outside.L_meta_983.conj14, PEqualNP.Outside.L_meta_983.conj15, PEqualNP.Outside.L_meta_983.conj16, PEqualNP.Outside.L_meta_983.conj17, PEqualNP.Outside.L_meta_983.conj18, PEqualNP.Outside.L_meta_983.conj19, PEqualNP.Outside.L_meta_983.conj20, PEqualNP.Outside.L_meta_983.conj21, PEqualNP.Outside.L_meta_983.conj22, PEqualNP.Outside.L_meta_983.conj23, PEqualNP.Outside.L_meta_983.conj24, PEqualNP.Outside.L_meta_983.conj25, PEqualNP.Outside.L_meta_983.conj26, PEqualNP.Outside.L_meta_983.conj27, PEqualNP.Outside.L_meta_983.conj28, PEqualNP.Outside.L_meta_983.conj29, PEqualNP.Outside.L_meta_983.conj30⟩
