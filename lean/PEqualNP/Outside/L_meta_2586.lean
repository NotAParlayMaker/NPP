import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2586
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

def rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
def val (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def step (w : List Bool) (g : Gate) := w ++ [val g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w

theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]; simp [step]; omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem last_read (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def Rel (q : Prop) (a b : Bool) : Prop := (a = true → b = true) ∧ (q → a = b)

theorem rel_refl (q : Prop) (b : Bool) : Rel q b b := ⟨id, fun _ => rfl⟩

theorem val_rel {q : Prop} (g : Gate) (f : ℕ → ℕ) (w v : List Bool)
    (hOp : g.op = .and ∨ g.op = .or)
    (hw : ∀ i, Rel q (w.getD i false) (v.getD (f i) false)) :
    Rel q (val g w) (val (rename f g) v) := by
  constructor
  · rcases hOp with h | h
    · simp [val, rename, h, GateOp.eval, List.all_eq_true]
      exact fun H i hi => (hw i).1 (H i hi)
    · simp [val, rename, h, GateOp.eval, List.any_eq_true]
      intro i hi H; exact ⟨i, hi, (hw i).1 H⟩
  · intro hq
    simp only [val, rename, List.map_map]; congr 1
    exact List.map_congr_left fun i _ => (hw i).2 hq

theorem red_lt {n j p i t : ℕ} (hp : p < n+j) (ht : n+j < t) (hi : i < t) :
    eraseRedirect n j p i < t-1 := by
  unfold eraseRedirect; split_ifs <;> omega

theorem run_rel {q : Prop} (n j p : ℕ) (hp : p < n+j) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w v : List Bool)
    (hl : w.length = v.length+1) (ht : n+j < w.length)
    (hw : ∀ i, Rel q (w.getD i false) (v.getD (eraseRedirect n j p i) false)) :
    ∀ i, Rel q ((run gs w).getD i false)
      ((run (gs.map (rename (eraseRedirect n j p))) v).getD (eraseRedirect n j p i) false) := by
  induction gs generalizing w v with
  | nil => exact hw
  | cons g gs ih =>
    change ∀ i, Rel q ((run gs (step w g)).getD i false)
      ((run (gs.map (rename (eraseRedirect n j p))) (step v (rename (eraseRedirect n j p) g))).getD _ false)
    apply ih (fun k hk => hm k (by simp [hk])) _ _ (by simp [step, hl]) (by simp [step]; omega)
    intro i
    rcases Nat.lt_trichotomy i w.length with hi | rfl | hi
    · have h := red_lt hp ht hi
      simpa only [step, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (show eraseRedirect n j p i < v.length by omega)] using hw i
    · have hr : eraseRedirect n j p w.length = v.length := by unfold eraseRedirect; split_ifs <;> omega
      simpa only [step, hr, last_read] using val_rel g (eraseRedirect n j p) w v (hm g (by simp)) hw
    · have hr : eraseRedirect n j p i = i-1 := by unfold eraseRedirect; split_ifs <;> omega
      rw [List.getD_eq_default _ _ (by simp [step]; omega), List.getD_eq_default _ _ (by simp [step]; omega)]
      exact rel_refl _ _

theorem positive (n : ℕ) (C : Circuit) (j p : ℕ)
    (hm : Monotone2 C) (hb : ReadsBack n C) (hj : j < C.gates.length)
    (ha : (gateAt C j).op = .and) (hpin : p ∈ (gateAt C j).inputs) :
    let D := eraseGate n C j p
    Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
      ∀ x : List Bool, x.length = n →
        (C.eval x = true → D.eval x = true) ∧
        ((C.wires x).getD (n+j) false = (C.wires x).getD p false → D.eval x = C.eval x) := by
  let D := eraseGate n C j p
  let a := C.gates.take j
  let g := gateAt C j
  let b := C.gates.drop (j+1)
  let f := eraseRedirect n j p
  have hlen : a.length = j := List.length_take_of_le (by omega)
  have hg : g = C.gates[j] := List.getD_eq_getElem _ _ hj
  have ho : a ++ g :: b = C.gates := by
    dsimp [a,b]; rw [hg, List.getElem_cons_drop hj, List.take_append_drop]
  have hd : D.gates = a ++ b.map (rename f) := by unfold D eraseGate; split <;> rfl
  have hout : D.output = f C.output := by simp [D, eraseGate, hj, f]
  have hp : p < n+j := hb j hj p hpin
  have hmb (k : Gate) (hk : k ∈ b) := hm k (ho ▸ (show k ∈ a ++ g :: b by simp [hk]))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hd, List.mem_append] at hk
    rcases hk with hk | hk
    · exact hm k (ho ▸ (show k ∈ a ++ g :: b by simp [hk]))
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hk
      simpa [rename] using hmb z hz
  · intro t ht i hi
    rw [hd] at ht
    rw [gateAt, hd, List.getD_eq_getElem _ _ ht] at hi
    by_cases hta : t < a.length
    · rw [List.getElem_append_left hta] at hi
      have htC : t < C.gates.length := by rw [← ho]; simp; omega
      apply hb t htC i
      rw [gateAt, ← ho, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hta]
      exact hi
    · rw [List.getElem_append_right (by omega), List.getElem_map] at hi
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
      have htb : t - a.length < b.length := by simpa using (show t - a.length < (b.map (rename f)).length by simp at ht ⊢; omega)
      have htC : j+1+(t-a.length) < C.gates.length := by dsimp [b] at htb; simp at htb; omega
      have hk' := hb (j+1+(t-a.length)) htC k (by
        rw [gateAt, List.getD_eq_getElem _ _ htC]
        dsimp [b] at hk; rw [List.getElem_drop] at hk; exact hk)
      have hr := red_lt (i := k) hp (t := j+1+(t-a.length)+n) (by omega) (by omega)
      change eraseRedirect n j p k < n+t; omega
  · change D.gates.length < C.gates.length
    rw [hd, ← ho]; simp
  · intro x hx
    let w := run a x
    have hw : w.length = n+j := by simp [w, length_run, hlen, hx]
    have old : C.wires x = run b (step w g) := by
      unfold Circuit.wires; rw [← ho, List.foldl_append]; rfl
    have new : D.wires x = run (b.map (rename f)) w := by
      unfold Circuit.wires; rw [hd, List.foldl_append]; rfl
    have hpw : p < w.length := hw ▸ hp
    have hgate : (C.wires x).getD (n+j) false = val g w := by
      rw [old, run_keep _ _ _ (by simp [step, hw]), ← hw]; exact last_read _ _
    have hoperand : (C.wires x).getD p false = w.getD p false := by
      rw [old, run_keep _ _ _ (by simp [step]; omega)]; exact List.getD_append _ _ _ _ hpw
    let q := val g w = w.getD p false
    have rel : ∀ i, Rel q ((step w g).getD i false) (w.getD (f i) false) := by
      intro i
      rcases Nat.lt_trichotomy i w.length with hi | rfl | hi
      · have hf : f i = i := by dsimp [f, eraseRedirect]; split_ifs <;> omega
        rw [hf]; unfold step; rw [List.getD_append _ _ _ _ hi]; exact rel_refl _ _
      · have hf : f w.length = p := by simp [f,eraseRedirect,hw]
        rw [hf]; unfold step; rw [last_read]; refine ⟨?_, id⟩
        intro h
        have hgop : g.op = .and := ha
        simp [val, hgop, GateOp.eval, List.all_eq_true] at h
        exact h p hpin
      · have hf : f i = i-1 := by dsimp [f,eraseRedirect]; split_ifs <;> omega
        rw [hf,List.getD_eq_default _ _ (by simp [step]; omega), List.getD_eq_default _ _ (by omega)]
        exact rel_refl _ _
    have out := run_rel n j p hp b (fun k hk => (hmb k hk).1) (step w g) w
      (by simp [step]) (by simp [step,hw]) rel C.output
    change ( (C.wires x).getD C.output false = true → (D.wires x).getD D.output false = true) ∧ _
    unfold Circuit.eval
    rw [hgate, hoperand, old, new, hout]
    exact ⟨out.1, fun he => (out.2 he).symm⟩

end PEqualNP.Outside.L_meta_2586

theorem PEqualNP.Outside.L_meta_2586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < x1.gates.length →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and →           x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs →             have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x1 x2 x3;             PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x9 ∧ x9.size < x1.size ∧ ∀ (x10 : List Bool), x10.length = (26 : ℕ) → (x1.eval x10 = Bool.true → x9.eval x10 = Bool.true) ∧ ((x1.wires x10).getD ((26 : ℕ) + x2) Bool.false = (x1.wires x10).getD x3 Bool.false → x9.eval x10 = x1.eval x10) :=
  L_meta_2586.positive 26
