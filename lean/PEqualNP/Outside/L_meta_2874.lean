import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2874

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def evalWires (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

lemma list_any_congr_mem {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

lemma evalWires_nil (xs : List Bool) : evalWires [] xs = xs := rfl

lemma evalWires_append (gs1 gs2 : List Gate) (xs : List Bool) :
    evalWires (gs1 ++ gs2) xs = evalWires gs2 (evalWires gs1 xs) := by
  simp [evalWires, List.foldl_append]

lemma evalWires_singleton (g : Gate) (xs : List Bool) :
    evalWires [g] xs = xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)] := rfl

lemma evalWires_length (gs : List Gate) (xs : List Bool) :
    (evalWires gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma evalWires_getD_prefix (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (evalWires gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    have hlt : i < (xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)]).length := by
      simp; omega
    rw [ih _ hlt, getD_append_left _ _ _ _ hi]

lemma evalWires_append_getD_left (gs1 gs2 : List Gate) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length + gs1.length) :
    (evalWires (gs1 ++ gs2) xs).getD i false = (evalWires gs1 xs).getD i false := by
  rw [evalWires_append]
  apply evalWires_getD_prefix
  rw [evalWires_length]
  exact hi

lemma evalWires_snoc_last (gs : List Gate) (g : Gate) (xs : List Bool) :
    (evalWires (gs ++ [g]) xs).getD (xs.length + gs.length) false =
      g.op.eval (g.inputs.map fun k => (evalWires gs xs).getD k false) := by
  rw [evalWires_append, evalWires_singleton]
  have hlen : (evalWires gs xs).length = xs.length + gs.length := evalWires_length gs xs
  rw [getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

def Good (x1 x2 : ℕ) (gs : List Gate) (S : Bool → Finset ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
      ∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ u v b, (gs.getD j ⟨GateOp.or, []⟩).inputs = [u, v] ∧ u ∈ S b ∧ v ∈ S !b)

lemma Good.mem_lt {x1 x2 : ℕ} {gs : List Gate} {S : Bool → Finset ℕ}
    (hG : Good x1 x2 gs S) {b : Bool} {w : ℕ} (hw : w ∈ S b) :
    w < x1 + x2 + gs.length := by
  rcases hG.2.2.1 b w hw with ⟨hlt, _⟩ | ⟨j, hj, rfl, _, _⟩ <;> omega

def initS (x1 x2 : ℕ) : Bool → Finset ℕ
  | false => Finset.range x1
  | true => (Finset.range x2).image (fun i => x1 + i)

lemma good_init (x1 x2 : ℕ) : Good x1 x2 [] (initS x1 x2) := by
  refine ⟨by simp, by simp, ?_, by simp⟩
  intro b w hw
  left
  cases b with
  | false =>
    simp only [initS, Finset.mem_range] at hw
    refine ⟨by omega, ?_⟩
    simp [Nat.not_le.mpr hw]
  | true =>
    simp only [initS, Finset.mem_image, Finset.mem_range] at hw
    rcases hw with ⟨i, hi, rfl⟩
    refine ⟨by omega, ?_⟩
    simp

lemma mem_initS_false {x1 x2 : ℕ} (p : Fin x1) : p.val ∈ initS x1 x2 false := by
  simp [initS, p.isLt]

lemma mem_initS_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.val ∈ initS x1 x2 true := by
  simp only [initS, Finset.mem_image, Finset.mem_range]
  exact ⟨l.val, l.isLt, rfl⟩

lemma good_append_or_plain {x1 x2 : ℕ} {gs : List Gate} {S : Bool → Finset ℕ}
    (hG : Good x1 x2 gs S) {u v : ℕ}
    (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 (gs ++ [⟨GateOp.or, [u, v]⟩]) S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hG.1 g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hi
      exact hG.2.1 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
  · intro b w hw
    rcases hG.2.2.1 b w hw with h | ⟨j, hj, rfl, hop, hin⟩
    · exact Or.inl h
    · right
      refine ⟨j, by simp; omega, rfl, ?_, ?_⟩
      · rw [getD_append_left _ _ _ _ hj]; exact hop
      · rw [getD_append_left _ _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hop ⊢
      exact hG.2.2.2 j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_right _ _ _ _ le_rfl] at hop
      simp at hop

lemma good_append_or_side {x1 x2 : ℕ} {gs : List Gate} {S : Bool → Finset ℕ}
    (hG : Good x1 x2 gs S) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    Good x1 x2 (gs ++ [⟨GateOp.or, [u, v]⟩])
      (fun c => if c = b then insert (x1 + x2 + gs.length) (S c) else S c) := by
  have hu' : u < x1 + x2 + gs.length := hG.mem_lt hu
  have hv' : v < x1 + x2 + gs.length := hG.mem_lt hv
  have hplain := good_append_or_plain hG hu' hv'
  refine ⟨hplain.1, hplain.2.1, ?_, ?_⟩
  · intro c w hw
    by_cases hcb : c = b
    · subst hcb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [getD_append_right _ _ _ _ le_rfl]; simp
        · rw [getD_append_right _ _ _ _ le_rfl]
          simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false]
          intro z hz
          simp only [ite_true, Finset.mem_insert]
          rcases hz with rfl | rfl
          · exact Or.inr hu
          · exact Or.inr hv
      · rcases hplain.2.2.1 c w hw with h | ⟨j, hj, rfl, hop, hin⟩
        · exact Or.inl h
        · right
          refine ⟨j, hj, rfl, hop, ?_⟩
          intro z hz
          simp only [ite_true, Finset.mem_insert]
          exact Or.inr (hin z hz)
    · simp only [hcb, ite_false] at hw
      rcases hplain.2.2.1 c w hw with h | ⟨j, hj, rfl, hop, hin⟩
      · exact Or.inl h
      · right
        refine ⟨j, hj, rfl, hop, ?_⟩
        intro z hz
        simp only [hcb, ite_false]
        exact hin z hz
  · intro j hj hop
    rcases hplain.2.2.2 j hj hop with ⟨a, d, c, hinputs, ha, hd⟩
    refine ⟨a, d, c, hinputs, ?_, ?_⟩
    · by_cases hcb : c = b
      · rw [hcb] at ha; simp [hcb, ha]
      · simp [hcb, ha]
    · by_cases hcb : (!c) = b
      · rw [hcb] at hd; simp [hcb, hd]
      · simp [hcb, hd]

lemma good_append_and {x1 x2 : ℕ} {gs : List Gate} {S : Bool → Finset ℕ}
    (hG : Good x1 x2 gs S) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S !b) :
    Good x1 x2 (gs ++ [⟨GateOp.and, [u, v]⟩]) S := by
  have hu' : u < x1 + x2 + gs.length := hG.mem_lt hu
  have hv' : v < x1 + x2 + gs.length := hG.mem_lt hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hG.1 g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hi
      exact hG.2.1 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
  · intro c w hw
    rcases hG.2.2.1 c w hw with h | ⟨j, hj, rfl, hop, hin⟩
    · exact Or.inl h
    · right
      refine ⟨j, by simp; omega, rfl, ?_, ?_⟩
      · rw [getD_append_left _ _ _ _ hj]; exact hop
      · rw [getD_append_left _ _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hop ⊢
      exact hG.2.2.2 j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_right _ _ _ _ le_rfl]
      exact ⟨u, v, b, by simp, hu, hv⟩

def orChainSide (x1 x2 : ℕ) (b : Bool) (gs : List Gate) (S : Bool → Finset ℕ)
    (w : ℕ) : List ℕ → List Gate × (Bool → Finset ℕ) × ℕ
  | [] => (gs, S, w)
  | w2 :: ws =>
    let w' := x1 + x2 + gs.length
    let gs' := gs ++ [⟨GateOp.or, [w, w2]⟩]
    let S' := fun c => if c = b then insert w' (S c) else S c
    orChainSide x1 x2 b gs' S' w' ws

lemma orChainSide_spec (x1 x2 : ℕ) (b : Bool) (gs : List Gate) (S : Bool → Finset ℕ)
    (w : ℕ) (ws : List ℕ)
    (hG : Good x1 x2 gs S) (hw : w ∈ S b) (hws : ∀ z ∈ ws, z ∈ S b) :
    let res := orChainSide x1 x2 b gs S w ws
    Good x1 x2 res.1 res.2.1 ∧
    (∃ gsAdd, res.1 = gs ++ gsAdd ∧ gsAdd.length = ws.length) ∧
    (∀ c, S c ⊆ res.2.1 c) ∧
    res.2.2 ∈ res.2.1 b ∧
    ∀ (xs : List Bool), xs.length = x1 + x2 →
      (evalWires res.1 xs).getD res.2.2 false =
        ((evalWires gs xs).getD w false || ws.any (fun z => (evalWires gs xs).getD z false)) := by
  induction ws generalizing gs S w with
  | nil =>
    refine ⟨hG, ⟨[], by simp [orChainSide], rfl⟩, fun _ => Finset.Subset.rfl, hw, ?_⟩
    intro xs _
    simp [orChainSide]
  | cons w2 ws ih =>
    have hw2 : w2 ∈ S b := hws w2 (by simp)
    have hws' : ∀ z ∈ ws, z ∈ S b := fun z hz => hws z (by simp [hz])
    let w' := x1 + x2 + gs.length
    let gs1 := gs ++ [⟨GateOp.or, [w, w2]⟩]
    let S1 := fun c => if c = b then insert w' (S c) else S c
    have hG1 : Good x1 x2 gs1 S1 := good_append_or_side hG b hw hw2
    have hsub1 : ∀ c, S c ⊆ S1 c := by
      intro c z hz
      by_cases hcb : c = b
      · rw [hcb] at hz; simp [S1, hcb, hz]
      · simp [S1, hcb, hz]
    have hw' : w' ∈ S1 b := by simp [S1]
    have hws1 : ∀ z ∈ ws, z ∈ S1 b := fun z hz => hsub1 b (hws' z hz)
    have hih := ih gs1 S1 w' hG1 hw' hws1
    rcases hih with ⟨hG2, ⟨gsAdd, hgs2, hlen2⟩, hsub2, hout2, heval2⟩
    refine ⟨hG2, ⟨⟨GateOp.or, [w, w2]⟩ :: gsAdd, ?_, ?_⟩, ?_, hout2, ?_⟩
    · dsimp only [orChainSide]
      change (orChainSide x1 x2 b gs1 S1 w' ws).1 = _
      rw [hgs2]
      simp [gs1]
    · simp [hlen2]
    · intro c
      exact Finset.Subset.trans (hsub1 c) (hsub2 c)
    · intro xs hxs
      have h1 := heval2 xs hxs
      change (evalWires (orChainSide x1 x2 b gs1 S1 w' ws).1 xs).getD
        (orChainSide x1 x2 b gs1 S1 w' ws).2.2 false = _
      rw [h1]
      have hw'_eval : (evalWires gs1 xs).getD w' false =
          ((evalWires gs xs).getD w false || (evalWires gs xs).getD w2 false) := by
        have hlast := evalWires_snoc_last gs ⟨GateOp.or, [w, w2]⟩ xs
        rw [hxs] at hlast
        simpa [gs1, w', GateOp.eval] using hlast
      have hws_eval : ws.any (fun z => (evalWires gs1 xs).getD z false) =
          ws.any (fun z => (evalWires gs xs).getD z false) := by
        apply list_any_congr_mem
        intro z hz
        have hzlt : z < xs.length + gs.length := by
          rw [hxs]; exact hG.mem_lt (hws' z hz)
        rw [evalWires_append_getD_left gs [⟨GateOp.or, [w, w2]⟩] xs z hzlt]
      rw [hw'_eval, hws_eval]
      simp [Bool.or_assoc]

def orChainPlain (x1 x2 : ℕ) (gs : List Gate) (w : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, w)
  | w2 :: ws =>
    let w' := x1 + x2 + gs.length
    let gs' := gs ++ [⟨GateOp.or, [w, w2]⟩]
    orChainPlain x1 x2 gs' w' ws

lemma orChainPlain_spec (x1 x2 : ℕ) (gs : List Gate) (S : Bool → Finset ℕ)
    (w : ℕ) (ws : List ℕ)
    (hG : Good x1 x2 gs S) (hw : w < x1 + x2 + gs.length)
    (hws : ∀ z ∈ ws, z < x1 + x2 + gs.length) :
    let res := orChainPlain x1 x2 gs w ws
    Good x1 x2 res.1 S ∧
    (∃ gsAdd, res.1 = gs ++ gsAdd ∧ gsAdd.length = ws.length) ∧
    res.2 < x1 + x2 + res.1.length ∧
    ∀ (xs : List Bool), xs.length = x1 + x2 →
      (evalWires res.1 xs).getD res.2 false =
        ((evalWires gs xs).getD w false || ws.any (fun z => (evalWires gs xs).getD z false)) := by
  induction ws generalizing gs w with
  | nil =>
    refine ⟨hG, ⟨[], by simp [orChainPlain], rfl⟩, hw, ?_⟩
    intro xs _
    simp [orChainPlain]
  | cons w2 ws ih =>
    have hw2 : w2 < x1 + x2 + gs.length := hws w2 (by simp)
    have hws' : ∀ z ∈ ws, z < x1 + x2 + gs.length := fun z hz => hws z (by simp [hz])
    let w' := x1 + x2 + gs.length
    let gs1 := gs ++ [⟨GateOp.or, [w, w2]⟩]
    have hG1 : Good x1 x2 gs1 S := good_append_or_plain hG hw hw2
    have hw' : w' < x1 + x2 + gs1.length := by simp [w', gs1]
    have hws1 : ∀ z ∈ ws, z < x1 + x2 + gs1.length := by
      intro z hz
      have := hws' z hz
      simp [gs1]; omega
    have hih := ih gs1 w' hG1 hw' hws1
    rcases hih with ⟨hG2, ⟨gsAdd, hgs2, hlen2⟩, hout2, heval2⟩
    refine ⟨hG2, ⟨⟨GateOp.or, [w, w2]⟩ :: gsAdd, ?_, ?_⟩, hout2, ?_⟩
    · dsimp only [orChainPlain]
      change (orChainPlain x1 x2 gs1 w' ws).1 = _
      rw [hgs2]
      simp [gs1]
    · simp [hlen2]
    · intro xs hxs
      have h1 := heval2 xs hxs
      change (evalWires (orChainPlain x1 x2 gs1 w' ws).1 xs).getD
        (orChainPlain x1 x2 gs1 w' ws).2 false = _
      rw [h1]
      have hw'_eval : (evalWires gs1 xs).getD w' false =
          ((evalWires gs xs).getD w false || (evalWires gs xs).getD w2 false) := by
        have hlast := evalWires_snoc_last gs ⟨GateOp.or, [w, w2]⟩ xs
        rw [hxs] at hlast
        simpa [gs1, w', GateOp.eval] using hlast
      have hws_eval : ws.any (fun z => (evalWires gs1 xs).getD z false) =
          ws.any (fun z => (evalWires gs xs).getD z false) := by
        apply list_any_congr_mem
        intro z hz
        have hzlt : z < xs.length + gs.length := by rw [hxs]; exact hws' z hz
        rw [evalWires_append_getD_left gs [⟨GateOp.or, [w, w2]⟩] xs z hzlt]
      rw [hw'_eval, hws_eval]
      simp [Bool.or_assoc]

def buildStars (x1 x2 : ℕ) (gs : List Gate) (S : Bool → Finset ℕ) :
    List (Bool × ℕ × List ℕ) → List Gate × (Bool → Finset ℕ) × List ℕ
  | [] => (gs, S, [])
  | (b, c, leaves) :: rest =>
    match leaves with
    | [] => buildStars x1 x2 gs S rest
    | l0 :: ls =>
      let r1 := orChainSide x1 x2 b gs S l0 ls
      let wAnd := x1 + x2 + r1.1.length
      let gs2 := r1.1 ++ [⟨GateOp.and, [c, r1.2.2]⟩]
      let r2 := buildStars x1 x2 gs2 r1.2.1 rest
      (r2.1, r2.2.1, wAnd :: r2.2.2)

lemma buildStars_spec (x1 x2 : ℕ) (gs : List Gate) (S : Bool → Finset ℕ)
    (stars : List (Bool × ℕ × List ℕ))
    (hG : Good x1 x2 gs S)
    (hstars : ∀ s ∈ stars, s.2.2 ≠ [] ∧ s.2.1 ∈ S !s.1 ∧ ∀ z ∈ s.2.2, z ∈ S s.1) :
    let res := buildStars x1 x2 gs S stars
    Good x1 x2 res.1 res.2.1 ∧
    (∃ gsAdd, res.1 = gs ++ gsAdd ∧ gsAdd.length = (stars.map fun s => s.2.2.length).sum) ∧
    (∀ c, S c ⊆ res.2.1 c) ∧
    res.2.2.length = stars.length ∧
    (∀ w ∈ res.2.2, w < x1 + x2 + res.1.length) ∧
    ∀ (xs : List Bool), xs.length = x1 + x2 →
      res.2.2.any (fun w => (evalWires res.1 xs).getD w false) =
        stars.any (fun s =>
          (evalWires gs xs).getD s.2.1 false &&
            s.2.2.any (fun z => (evalWires gs xs).getD z false)) := by
  induction stars generalizing gs S with
  | nil =>
    refine ⟨hG, ⟨[], by simp [buildStars], rfl⟩, fun _ => Finset.Subset.rfl, rfl, by simp [buildStars], ?_⟩
    intro xs _
    simp [buildStars]
  | cons s rest ih =>
    rcases s with ⟨b, c, leaves⟩
    have hs := hstars (b, c, leaves) (by simp)
    have hrest : ∀ t ∈ rest, t.2.2 ≠ [] ∧ t.2.1 ∈ S !t.1 ∧ ∀ z ∈ t.2.2, z ∈ S t.1 :=
      fun t ht => hstars t (by simp [ht])
    cases leaves with
    | nil => exact False.elim (hs.1 rfl)
    | cons l0 ls =>
      have hc : c ∈ S !b := hs.2.1
      have hl0 : l0 ∈ S b := hs.2.2 l0 (by simp)
      have hls : ∀ z ∈ ls, z ∈ S b := fun z hz => hs.2.2 z (by simp [hz])
      let r1 := orChainSide x1 x2 b gs S l0 ls
      have hr1 := orChainSide_spec x1 x2 b gs S l0 ls hG hl0 hls
      rcases hr1 with ⟨hG1, ⟨gsAdd1, hgs1, hlen1⟩, hsub1, hout1, heval1⟩
      let wAnd := x1 + x2 + r1.1.length
      let gs2 := r1.1 ++ [⟨GateOp.and, [c, r1.2.2]⟩]
      have hc1 : c ∈ r1.2.1 !b := hsub1 (!b) hc
      have hG2 : Good x1 x2 gs2 r1.2.1 := by
        have h := good_append_and hG1 (!b) hc1 (by simpa using hout1)
        exact h
      have hrest1 : ∀ t ∈ rest, t.2.2 ≠ [] ∧ t.2.1 ∈ r1.2.1 !t.1 ∧ ∀ z ∈ t.2.2, z ∈ r1.2.1 t.1 := by
        intro t ht
        have h := hrest t ht
        exact ⟨h.1, hsub1 (!t.1) h.2.1, fun z hz => hsub1 t.1 (h.2.2 z hz)⟩
      have hih := ih gs2 r1.2.1 hG2 hrest1
      rcases hih with ⟨hG3, ⟨gsAdd2, hgs3, hlen3⟩, hsub3, houtsLen, houtsLt, heval3⟩
      refine ⟨hG3, ⟨gsAdd1 ++ [⟨GateOp.and, [c, r1.2.2]⟩] ++ gsAdd2, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · change (buildStars x1 x2 gs2 r1.2.1 rest).1 = _
        rw [hgs3]
        dsimp only [gs2, r1]
        rw [hgs1]
        simp [List.append_assoc]
      · simp [hlen1, hlen3]
        omega
      · intro d
        exact Finset.Subset.trans (hsub1 d) (hsub3 d)
      · change (wAnd :: (buildStars x1 x2 gs2 r1.2.1 rest).2.2).length = (rest.length + 1)
        simp [houtsLen]
      · intro w hw
        change w ∈ wAnd :: (buildStars x1 x2 gs2 r1.2.1 rest).2.2 at hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · change wAnd < x1 + x2 + (buildStars x1 x2 gs2 r1.2.1 rest).1.length
          rw [hgs3]
          simp only [wAnd, gs2, List.length_append, List.length_singleton]
          omega
        · exact houtsLt w hw
      · intro xs hxs
        simp only [buildStars, List.any_cons]
        have hwand_lt : wAnd < xs.length + gs2.length := by
          rw [hxs]; simp [wAnd, gs2]
        have hwand_eval : (evalWires (buildStars x1 x2 gs2 r1.2.1 rest).1 xs).getD wAnd false =
            ((evalWires gs xs).getD c false &&
              ((evalWires gs xs).getD l0 false || ls.any (fun z => (evalWires gs xs).getD z false))) := by
          rw [hgs3, evalWires_append_getD_left gs2 gsAdd2 xs wAnd hwand_lt]
          have hlast := evalWires_snoc_last r1.1 ⟨GateOp.and, [c, r1.2.2]⟩ xs
          rw [hxs] at hlast
          have hlast' : (evalWires gs2 xs).getD wAnd false =
              ((evalWires r1.1 xs).getD c false && (evalWires r1.1 xs).getD r1.2.2 false) := by
            simpa [gs2, wAnd, GateOp.eval] using hlast
          rw [hlast', heval1 xs hxs]
          have hc_lt : c < xs.length + gs.length := by rw [hxs]; exact hG.mem_lt hc
          rw [hgs1, evalWires_append_getD_left gs gsAdd1 xs c hc_lt]
        have hrest_eval : (buildStars x1 x2 gs2 r1.2.1 rest).2.2.any
              (fun w => (evalWires (buildStars x1 x2 gs2 r1.2.1 rest).1 xs).getD w false) =
            rest.any (fun t =>
              (evalWires gs xs).getD t.2.1 false &&
                t.2.2.any (fun z => (evalWires gs xs).getD z false)) := by
          rw [heval3 xs hxs]
          apply list_any_congr_mem
          intro t ht
          have h := hrest t ht
          have ht1_lt : t.2.1 < xs.length + gs.length := by rw [hxs]; exact hG.mem_lt h.2.1
          have hgs2_eq : gs2 = gs ++ (gsAdd1 ++ [⟨GateOp.and, [c, r1.2.2]⟩]) := by
            dsimp only [gs2, r1]
            rw [hgs1, List.append_assoc]
          rw [hgs2_eq, evalWires_append_getD_left gs _ xs t.2.1 ht1_lt]
          congr 1
          apply list_any_congr_mem
          intro z hz
          have hz_lt : z < xs.length + gs.length := by rw [hxs]; exact hG.mem_lt (h.2.2 z hz)
          rw [evalWires_append_getD_left gs _ xs z hz_lt]
        rw [hwand_eval, hrest_eval]

lemma getD_ofFn_castAdd {x1 x2 : ℕ} (f : Fin (x1 + x2) → Bool) (p : Fin x1) :
    (List.ofFn f).getD p.val false = f (Fin.castAdd x2 p) := by
  have hlt : p.val < (List.ofFn f).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [List.getElem_ofFn]
  rfl

lemma getD_ofFn_natAdd {x1 x2 : ℕ} (f : Fin (x1 + x2) → Bool) (l : Fin x2) :
    (List.ofFn f).getD (x1 + l.val) false = f (Fin.natAdd x1 l) := by
  have hlt : x1 + l.val < (List.ofFn f).length := by simp
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [List.getElem_ofFn]
  rfl

lemma list_map_toList_sum {α : Type*} (s : Finset α) (f : α → ℕ) :
    (s.toList.map f).sum = ∑ a ∈ s, f a := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rfl

lemma card_filter_eq_sum_image_snd {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2))
    (x4 : Finset (Fin x1)) :
    (x3.filter fun e => e.1 ∈ x4).card =
      ∑ p ∈ x4, ((x3.filter fun e => e.1 = p).image Prod.snd).card := by
  have hpart : ∀ p : Fin x1,
      ((x3.filter fun e => e.1 = p).image Prod.snd).card =
        (x3.filter fun e => e.1 = p).card := by
    intro p
    apply Finset.card_image_of_injOn
    intro e1 he1 e2 he2 hsnd
    simp only [Finset.mem_coe, Finset.mem_filter] at he1 he2
    exact Prod.ext (he1.2.trans he2.2.symm) hsnd
  simp_rw [hpart]
  rw [← Finset.card_biUnion]
  · congr 1
    ext e
    simp [and_comm]
  · intro p1 _ p2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    exact hne (he1.2.symm.trans he2.2)

lemma card_filter_eq_sum_image_fst {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2))
    (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2))
    (hcov : ∀ e ∈ x3, e.1 ∈ x4 ∨ e.2 ∈ x5) :
    (x3.filter fun e => e.1 ∉ x4).card =
      ∑ l ∈ x5, ((x3.filter fun e => e.2 = l ∧ e.1 ∉ x4).image Prod.fst).card := by
  have hpart : ∀ l : Fin x2,
      ((x3.filter fun e => e.2 = l ∧ e.1 ∉ x4).image Prod.fst).card =
        (x3.filter fun e => e.2 = l ∧ e.1 ∉ x4).card := by
    intro l
    apply Finset.card_image_of_injOn
    intro e1 he1 e2 he2 hfst
    simp only [Finset.mem_coe, Finset.mem_filter] at he1 he2
    exact Prod.ext hfst (he1.2.1.trans he2.2.1.symm)
  simp_rw [hpart]
  rw [← Finset.card_biUnion]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro ⟨he3, he4⟩
      rcases hcov e he3 with h | h
      · exact False.elim (he4 h)
      · exact ⟨e.2, h, he3, rfl, he4⟩
    · rintro ⟨l, _, he3, _, he4⟩
      exact ⟨he3, he4⟩
  · intro l1 _ l2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    exact hne (he1.2.1.symm.trans he2.2.1)

lemma good_to_goal {x1 x2 : ℕ} {gs : List Gate} {S : Bool → Finset ℕ} {out : ℕ}
    (hG : Good x1 x2 gs S) :
    IsAO2 (x1 + x2) ⟨gs, out⟩ ∧
    (have x9 : ℕ → Gate := gateAt ⟨gs, out⟩;
      (∀ (x10 : Bool), ∀ x11 ∈ S x10,
        x11 < x1 + x2 ∧ decide (x1 ≤ x11) = x10 ∨
        ∃ x13 < (⟨gs, out⟩ : Circuit).size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = GateOp.or ∧
          ∀ x14 ∈ (x9 x13).inputs, x14 ∈ S x10) ∧
      ∀ x10 < (⟨gs, out⟩ : Circuit).size, (x9 x10).op = GateOp.and →
        ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool),
          (x9 x10).inputs = [x13, x14] ∧ x13 ∈ S x15 ∧ x14 ∈ S !x15) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hG.1 g hg).1
  · intro j hj i hi; exact hG.2.1 j hj i hi
  · intro g hg; exact (hG.1 g hg).2
  · exact hG.2.2.1
  · exact hG.2.2.2

end PEqualNP.Outside.L_meta_2874

theorem PEqualNP.Outside.L_meta_2874 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro x1 x2 x3 x4 x5 hcov
  by_cases hx3 : x3 = ∅
  · subst hx3
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly], by simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack], by simp⟩
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro x9
      simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.getD_eq_getElem?_getD]
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · let NA : Fin x1 → Finset (Fin x2) := fun p => (x3.filter fun e => e.1 = p).image Prod.snd
    let NB : Fin x2 → Finset (Fin x1) := fun l => (x3.filter fun e => e.2 = l ∧ e.1 ∉ x4).image Prod.fst
    let A' : Finset (Fin x1) := x4.filter fun p => (NA p).Nonempty
    let B' : Finset (Fin x2) := x5.filter fun l => (NB l).Nonempty
    let pStars : List (Bool × ℕ × List ℕ) :=
      A'.toList.map fun p => (true, p.val, (NA p).toList.map fun l => x1 + l.val)
    let lStars : List (Bool × ℕ × List ℕ) :=
      B'.toList.map fun l => (false, x1 + l.val, (NB l).toList.map fun p => p.val)
    let stars : List (Bool × ℕ × List ℕ) := pStars ++ lStars
    have hstars_ok : ∀ s ∈ stars,
        s.2.2 ≠ [] ∧ s.2.1 ∈ PEqualNP.Outside.L_meta_2874.initS x1 x2 !s.1 ∧
          ∀ z ∈ s.2.2, z ∈ PEqualNP.Outside.L_meta_2874.initS x1 x2 s.1 := by
      intro s hs
      simp only [stars, List.mem_append, pStars, lStars, List.mem_map, Finset.mem_toList] at hs
      rcases hs with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [A', Finset.mem_filter] at hp
        refine ⟨?_, PEqualNP.Outside.L_meta_2874.mem_initS_false p, ?_⟩
        · intro hemp
          have : (NA p).toList = [] := List.map_eq_nil_iff.mp hemp
          have : NA p = ∅ := Finset.toList_eq_nil.mp this
          exact hp.2.ne_empty this
        · intro z hz
          simp only [List.mem_map, Finset.mem_toList] at hz
          rcases hz with ⟨l, _, rfl⟩
          exact PEqualNP.Outside.L_meta_2874.mem_initS_true l
      · simp only [B', Finset.mem_filter] at hl
        refine ⟨?_, PEqualNP.Outside.L_meta_2874.mem_initS_true l, ?_⟩
        · intro hemp
          have : (NB l).toList = [] := List.map_eq_nil_iff.mp hemp
          have : NB l = ∅ := Finset.toList_eq_nil.mp this
          exact hl.2.ne_empty this
        · intro z hz
          simp only [List.mem_map, Finset.mem_toList] at hz
          rcases hz with ⟨p, _, rfl⟩
          exact PEqualNP.Outside.L_meta_2874.mem_initS_false p
    have hbuilt := PEqualNP.Outside.L_meta_2874.buildStars_spec x1 x2 []
      (PEqualNP.Outside.L_meta_2874.initS x1 x2) stars
      (PEqualNP.Outside.L_meta_2874.good_init x1 x2) hstars_ok
    rcases hbuilt with ⟨hG1, ⟨gsAdd1, hgs1, hlen1⟩, _, houtsLen, houtsLt, heval1⟩
    have hstars_ne : stars ≠ [] := by
      intro hemp
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hx3
      by_cases he4 : e.1 ∈ x4
      · have hpA : e.1 ∈ A' := by
          simp only [A', Finset.mem_filter]
          exact ⟨he4, ⟨e.2, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩⟩
        have : pStars ≠ [] := by
          simp only [pStars, ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
          exact Finset.ne_empty_of_mem hpA
        have : stars ≠ [] := by simp [stars, this]
        exact this hemp
      · have he5 : e.2 ∈ x5 := (hcov e he).resolve_left he4
        have hlB : e.2 ∈ B' := by
          simp only [B', Finset.mem_filter]
          exact ⟨he5, ⟨e.1, Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl, he4⟩, rfl⟩⟩⟩
        have : lStars ≠ [] := by
          simp only [lStars, ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
          exact Finset.ne_empty_of_mem hlB
        have : stars ≠ [] := by simp [stars, this]
        exact this hemp
    let r1 := PEqualNP.Outside.L_meta_2874.buildStars x1 x2 []
      (PEqualNP.Outside.L_meta_2874.initS x1 x2) stars
    cases houts : r1.2.2 with
    | nil =>
      have : stars.length = 0 := by
        rw [← houtsLen]
        change r1.2.2.length = 0
        rw [houts]
        rfl
      exact False.elim (hstars_ne (List.eq_nil_of_length_eq_zero this))
    | cons w0 ws =>
      have hw0 : w0 < x1 + x2 + r1.1.length := houtsLt w0 (by rw [houts]; simp)
      have hws : ∀ z ∈ ws, z < x1 + x2 + r1.1.length := fun z hz => houtsLt z (by rw [houts]; simp [hz])
      have hchain := PEqualNP.Outside.L_meta_2874.orChainPlain_spec x1 x2 r1.1 r1.2.1 w0 ws
        hG1 hw0 hws
      rcases hchain with ⟨hG2, ⟨gsAdd2, hgs2, hlen2⟩, _, heval2⟩
      let r2 := PEqualNP.Outside.L_meta_2874.orChainPlain x1 x2 r1.1 w0 ws
      have hgt := PEqualNP.Outside.L_meta_2874.good_to_goal (out := r2.2) hG2
      refine ⟨⟨r2.1, r2.2⟩, r1.2.1, hgt.1, ?_, ?_, hgt.2⟩
      · have hsum_p : (pStars.map fun s => s.2.2.length).sum = ∑ p ∈ A', (NA p).card := by
          simp only [pStars, List.map_map, Function.comp_def, List.length_map, Finset.length_toList]
          exact PEqualNP.Outside.L_meta_2874.list_map_toList_sum A' (fun p => (NA p).card)
        have hsum_l : (lStars.map fun s => s.2.2.length).sum = ∑ l ∈ B', (NB l).card := by
          simp only [lStars, List.map_map, Function.comp_def, List.length_map, Finset.length_toList]
          exact PEqualNP.Outside.L_meta_2874.list_map_toList_sum B' (fun l => (NB l).card)
        have hsum_p_all : ∑ p ∈ A', (NA p).card = ∑ p ∈ x4, (NA p).card := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p _
          by_cases h : (NA p).Nonempty
          · simp [h]
          · simp [Finset.not_nonempty_iff_eq_empty.mp h]
        have hsum_l_all : ∑ l ∈ B', (NB l).card = ∑ l ∈ x5, (NB l).card := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro l _
          by_cases h : (NB l).Nonempty
          · simp [h]
          · simp [Finset.not_nonempty_iff_eq_empty.mp h]
        have hsum_eq : (stars.map fun s => s.2.2.length).sum = x3.card := by
          simp only [stars, List.map_append, List.sum_append, hsum_p, hsum_l, hsum_p_all, hsum_l_all]
          rw [← PEqualNP.Outside.L_meta_2874.card_filter_eq_sum_image_snd x3 x4,
              ← PEqualNP.Outside.L_meta_2874.card_filter_eq_sum_image_fst x3 x4 x5 hcov]
          have hdisj : Disjoint (x3.filter fun e => e.1 ∈ x4) (x3.filter fun e => e.1 ∉ x4) := by
            rw [Finset.disjoint_left]
            intro e h1 h2
            exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          rw [← Finset.card_union_of_disjoint hdisj]
          congr 1
          ext e
          by_cases h : e.1 ∈ x4 <;> simp [h]
        have hstars_len : stars.length = A'.card + B'.card := by
          simp [stars, pStars, lStars]
        have hA_le : A'.card ≤ x4.card := Finset.card_filter_le _ _
        have hB_le : B'.card ≤ x5.card := Finset.card_filter_le _ _
        have hws_len : ws.length + 1 = stars.length := by
          have : (w0 :: ws).length = stars.length := by rw [← houts]; exact houtsLen
          simpa using this
        have hsz : r2.1.length = x3.card + ws.length := by
          rw [hgs2, List.length_append, hlen2]
          have hr1len : r1.1.length = x3.card := by
            rw [hgs1, List.nil_append, hlen1, hsum_eq]
          omega
        change r2.1.length ≤ x3.card + x4.card + x5.card - 1
        omega
      · intro x9
        have hxs : (List.ofFn x9).length = x1 + x2 := List.length_ofFn
        change (PEqualNP.Outside.L_meta_2874.evalWires r2.1 (List.ofFn x9)).getD r2.2 false = _
        rw [heval2 (List.ofFn x9) hxs]
        have hcomb :
            ((PEqualNP.Outside.L_meta_2874.evalWires r1.1 (List.ofFn x9)).getD w0 false ||
              ws.any (fun z => (PEqualNP.Outside.L_meta_2874.evalWires r1.1 (List.ofFn x9)).getD z false)) =
            r1.2.2.any (fun z => (PEqualNP.Outside.L_meta_2874.evalWires r1.1 (List.ofFn x9)).getD z false) := by
          rw [houts]
          rfl
        rw [hcomb, heval1 (List.ofFn x9) hxs]
        simp only [PEqualNP.Outside.L_meta_2874.evalWires_nil]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨s, hs, hcond⟩
          simp only [Bool.and_eq_true, List.any_eq_true] at hcond
          rcases hcond with ⟨hc_true, ⟨z, hz, hz_true⟩⟩
          simp only [stars, List.mem_append, pStars, lStars, List.mem_map, Finset.mem_toList] at hs
          rcases hs with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
          · simp only [List.mem_map, Finset.mem_toList] at hz
            rcases hz with ⟨l, hlNA, rfl⟩
            simp only [NA, Finset.mem_image, Finset.mem_filter] at hlNA
            rcases hlNA with ⟨e, ⟨he3, he1⟩, he2⟩
            rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_castAdd] at hc_true
            rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_natAdd] at hz_true
            exact ⟨p, l, by rwa [← he1, ← he2], hc_true, hz_true⟩
          · simp only [List.mem_map, Finset.mem_toList] at hz
            rcases hz with ⟨p, hpNB, rfl⟩
            simp only [NB, Finset.mem_image, Finset.mem_filter] at hpNB
            rcases hpNB with ⟨e, ⟨he3, he2, _⟩, he1⟩
            rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_natAdd] at hc_true
            rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_castAdd] at hz_true
            exact ⟨p, l, by rwa [← he1, ← he2], hz_true, hc_true⟩
        · rintro ⟨p, l, hpl, hp_true, hl_true⟩
          by_cases hp4 : p ∈ x4
          · refine ⟨(true, p.val, (NA p).toList.map fun l' => x1 + l'.val), ?_, ?_⟩
            · simp only [stars, List.mem_append, pStars, List.mem_map, Finset.mem_toList]
              left
              refine ⟨p, ?_, rfl⟩
              simp only [A', Finset.mem_filter]
              exact ⟨hp4, ⟨l, Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨hpl, rfl⟩, rfl⟩⟩⟩
            · simp only [Bool.and_eq_true, List.any_eq_true]
              refine ⟨by rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_castAdd]; exact hp_true, ?_⟩
              refine ⟨x1 + l.val, ?_, by rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_natAdd]; exact hl_true⟩
              simp only [List.mem_map, Finset.mem_toList]
              exact ⟨l, Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨hpl, rfl⟩, rfl⟩, rfl⟩
          · have hl5 : l ∈ x5 := (hcov (p, l) hpl).resolve_left hp4
            refine ⟨(false, x1 + l.val, (NB l).toList.map fun p' => p'.val), ?_, ?_⟩
            · simp only [stars, List.mem_append, lStars, List.mem_map, Finset.mem_toList]
              right
              refine ⟨l, ?_, rfl⟩
              simp only [B', Finset.mem_filter]
              exact ⟨hl5, ⟨p, Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨hpl, rfl, hp4⟩, rfl⟩⟩⟩
            · simp only [Bool.and_eq_true, List.any_eq_true]
              refine ⟨by rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_natAdd]; exact hl_true, ?_⟩
              refine ⟨p.val, ?_, by rw [PEqualNP.Outside.L_meta_2874.getD_ofFn_castAdd]; exact hp_true⟩
              simp only [List.mem_map, Finset.mem_toList]
              exact ⟨p, Finset.mem_image.mpr ⟨(p, l), Finset.mem_filter.mpr ⟨hpl, rfl, hp4⟩, rfl⟩, rfl⟩
