import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332_aux

open PEqualNP.CircuitLowerBounds

private def binary (g : Gate) : Bool :=
  (match g.op with | .and | .or => true | _ => false) && (g.inputs.length == 2)

private def neg (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private theorem binary_iff (g : Gate) :
    binary g = true ↔ (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [binary]

private theorem neg_iff (g : Gate) : neg g = true ↔ g.op = .not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [neg]

private def skip (p : ℕ) (g : Gate) : Bool := binary g && g.inputs.contains p

private theorem skip_iff (p : ℕ) (g : Gate) :
    skip p g = true ↔ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧ p ∈ g.inputs := by
  simp [skip, binary_iff]

private def ref (z : ℕ) (rs : List ℕ) (i : ℕ) : ℕ := rs.getD i z

private def replacement (z p : ℕ) (rs : List ℕ) : Gate → ℕ
  | ⟨.or, [u, v]⟩ => if u = p then ref z rs v else ref z rs u
  | _ => z

private def remap (z : ℕ) (rs : List ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (ref z rs)⟩

private def pass (z p : ℕ) (k : ℕ) (rs : List ℕ) : List Gate → List Gate × List ℕ
  | [] => ([], rs)
  | g :: gs =>
    if skip p g then
      pass z p k (rs ++ [replacement z p rs g]) gs
    else
      let tail := pass z p (k + 1) (rs ++ [k]) gs
      (remap z rs g :: tail.1, tail.2)

private def readGate (g : Gate) (x : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => x.getD i false))

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [readGate g w]) x

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [readGate g x])).length = _
    rw [ih]
    simp
    omega

private theorem snoc_getD {α : Type} (xs : List α) (a d : α) (i : ℕ) :
    (xs ++ [a]).getD i d = if i = xs.length then a else xs.getD i d := by
  by_cases he : i = xs.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · by_cases hi : i < xs.length
    · rw [List.getD_append _ _ _ _ hi, ite_eq_right he]
    · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]

private def Related (z : ℕ) (rs : List ℕ) (x y : List Bool) : Prop :=
  rs.length = x.length ∧
    (∀ i, ref z rs i < y.length ∨ ref z rs i = z) ∧
    ∀ i, x.getD i false = y.getD (ref z rs i) false

private theorem related_append {z k : ℕ} {rs : List ℕ} {x y y' : List Bool}
    {v : Bool} (hr : Related z rs x y) (hy : y.length ≤ y'.length)
    (hs : ∀ i, y.getD (ref z rs i) false = y'.getD (ref z rs i) false)
    (hk : k < y'.length ∨ k = z) (hv : v = y'.getD k false) :
    Related z (rs ++ [k]) (x ++ [v]) y' := by
  obtain ⟨hlen, hbound, hval⟩ := hr
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i
    simp only [ref, snoc_getD]
    split
    · exact hk
    · exact (hbound i).imp (fun h => lt_of_lt_of_le h hy) id
  · intro i
    simp only [ref, snoc_getD, hlen]
    split
    · exact hv
    · exact (hval i).trans (hs i)

private theorem remap_sound {z : ℕ} {rs : List ℕ} {x y : List Bool}
    (hr : Related z rs x y) (g : Gate) : readGate g x = readGate (remap z rs g) y := by
  unfold readGate remap
  simp only [List.map_map, Function.comp_def]
  congr 1
  exact List.map_congr_left (fun i _ => hr.2.2 i)

private theorem replacement_sound {z p : ℕ} {rs : List ℕ} {x y : List Bool}
    {g : Gate} (hr : Related z rs x y) (hz : y.length ≤ z) (hp : ref z rs p = z)
    (hg : skip p g = true) :
    (replacement z p rs g < y.length ∨ replacement z p rs g = z) ∧
      readGate g x = y.getD (replacement z p rs g) false := by
  have hzero : y.getD z false = false := List.getD_eq_default _ _ hz
  have hx : x.getD p false = false := by rw [hr.2.2 p, hp, hzero]
  obtain ⟨⟨hop, hlen⟩, hmem⟩ := (skip_iff p g).mp hg
  rcases g with ⟨op, ins⟩
  change ins.length = 2 at hlen
  obtain ⟨u, v, rfl⟩ := List.length_eq_two.mp hlen
  change p ∈ [u, v] at hmem
  have he : u = p ∨ v = p := by simpa [eq_comm] using hmem
  rcases hop with rfl | rfl
  · refine ⟨Or.inr rfl, ?_⟩
    simp only [readGate, replacement, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, id_eq, Bool.and_true, hzero]
    rcases he with hu | hv
    · subst u
      rw [hx, Bool.false_and]
    · subst v
      rw [hx, Bool.and_false]
  · by_cases hu : u = p
    · subst u
      simpa only [replacement, readGate, GateOp.eval, ite_eq_left rfl, ite_true, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id_eq, hx, Bool.or_false, Bool.false_or] using
        (show (ref z rs v < y.length ∨ ref z rs v = z) ∧
          x.getD v false = y.getD (ref z rs v) false from ⟨hr.2.1 v, hr.2.2 v⟩)
    · have hv := he.resolve_left hu
      subst v
      simpa only [replacement, readGate, GateOp.eval, ite_eq_right hu, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id_eq, hx, Bool.or_false] using
        (show (ref z rs u < y.length ∨ ref z rs u = z) ∧
          x.getD u false = y.getD (ref z rs u) false from ⟨hr.2.1 u, hr.2.2 u⟩)

private theorem pass_sound (z p : ℕ) (gs : List Gate) :
    ∀ (rs : List ℕ) (x y : List Bool), Related z rs x y →
      p < rs.length → ref z rs p = z → y.length + gs.length ≤ z →
      Related z (pass z p y.length rs gs).2 (run gs x)
        (run (pass z p y.length rs gs).1 y) := by
  induction gs with
  | nil =>
    intro rs x y hr _ _ _
    exact hr
  | cons g gs ih =>
    intro rs x y hr hp hzero hz
    have hz' : y.length + gs.length + 1 ≤ z := by simpa [Nat.add_assoc] using hz
    by_cases hg : skip p g = true
    · obtain ⟨hb, he⟩ := replacement_sound hr (by omega) hzero hg
      let k := replacement z p rs g
      have hr' := related_append hr (le_refl y.length) (fun _ => rfl) hb he
      have hkeep : ref z (rs ++ [k]) p = z := (List.getD_append _ _ _ _ hp).trans hzero
      simpa only [pass, ite_eq_left hg, run, List.foldl_cons] using
        ih (rs ++ [k]) (x ++ [readGate g x]) y hr' (by simp; omega) hkeep (by omega)
    · let q := remap z rs g
      let y' := y ++ [readGate q y]
      have hy' : y'.length = y.length + 1 := by simp [y']
      have hs : ∀ i, y.getD (ref z rs i) false = y'.getD (ref z rs i) false := by
        intro i
        rcases hr.2.1 i with h | h
        · exact (List.getD_append _ _ _ _ h).symm
        · rw [h, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hv : readGate g x = y'.getD y.length false := by
        change readGate g x = (y ++ [readGate q y]).getD y.length false
        rw [remap_sound hr, snoc_getD, ite_eq_left rfl]
      have hr' := related_append hr (by omega) hs (Or.inl (by omega)) hv
      have hkeep : ref z (rs ++ [y.length]) p = z :=
        (List.getD_append _ _ _ _ hp).trans hzero
      have h := ih (rs ++ [y.length]) (x ++ [readGate g x]) y'
        hr' (by simp; omega) hkeep (by omega)
      rw [hy'] at h
      simpa only [pass, ite_eq_right hg, run, List.foldl_cons, q, y'] using h

private theorem pass_counts (z p k : ℕ) (rs : List ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, allowed g) :
    let gl := (pass z p k rs gs).1
    gl.length ≤ gs.length ∧
    gl.countP neg = gs.countP neg ∧
    gl.countP binary + gs.countP (skip p) = gs.countP binary ∧
    ∀ g ∈ gl, allowed g := by
  induction gs generalizing k rs with
  | nil => simp [pass]
  | cons g gs ih =>
    have hg₀ := hg g (by simp)
    have hg₁ : ∀ h ∈ gs, allowed h := fun h hh => hg h (by simp [hh])
    have hb : binary (remap z rs g) = binary g := by simp [binary, remap]
    have hn : neg (remap z rs g) = neg g := rfl
    by_cases h : skip p g = true
    · have hbin : binary g = true := (binary_iff g).mpr ((skip_iff p g).mp h).1
      have hnot : neg g = false := by
        rcases (binary_iff g).mp hbin with ⟨hop, -⟩
        unfold neg
        rcases hop with he | he <;> simp [he]
      obtain ⟨hl, hn', hc, ha⟩ := ih k (rs ++ [replacement z p rs g]) hg₁
      simp only [pass, List.length_cons, List.countP_cons, h, hbin, hnot,
        ite_true, Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ⟨by omega, hn', by omega, ha⟩
    · obtain ⟨hl, hn', hc, ha⟩ := ih (k + 1) (rs ++ [k]) hg₁
      simp only [pass, List.length_cons, List.countP_cons, h, Bool.false_eq_true, ite_false,
        Nat.add_zero, hn, hb]
      refine ⟨by omega, by omega, by omega, ?_⟩
      intro a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · simpa [allowed, remap] using hg₀
      · exact ha a ha'

private def refsFor {n : ℕ} (z : ℕ) (p : Fin n) : List ℕ :=
  List.ofFn fun i : Fin n => if i = p then z else i.val

private theorem ofFn_getD {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem input_related {n z : ℕ} (p : Fin n) (x : Fin n → Bool) (hz : n ≤ z) :
    Related z (refsFor z p) (List.ofFn (Function.update x p false)) (List.ofFn x) := by
  refine ⟨by simp [refsFor], ?_, ?_⟩
  · intro i
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      change ref z (refsFor z p) j.val < _ ∨ ref z (refsFor z p) j.val = z
      simp only [ref, refsFor, ofFn_getD, List.length_ofFn]
      split
      · exact Or.inr rfl
      · exact Or.inl hi
    · have h : ref z (refsFor z p) i = z :=
        List.getD_eq_default _ _ (by simpa [refsFor] using Nat.le_of_not_gt hi)
      exact Or.inr h
  · intro i
    by_cases hi : i < n
    · let j : Fin n := ⟨i, hi⟩
      change (List.ofFn (Function.update x p false)).getD j.val false =
        (List.ofFn x).getD (ref z (refsFor z p) j.val) false
      simp only [ref, refsFor, ofFn_getD]
      by_cases hj : j = p
      · rw [hj, ite_eq_left rfl, Function.update_self,
          List.getD_eq_default _ _ (by simpa using hz)]
      · rw [ite_eq_right hj, ofFn_getD, Function.update_of_ne hj]
    · have h : ref z (refsFor z p) i = z :=
        List.getD_eq_default _ _ (by simpa [refsFor] using Nat.le_of_not_gt hi)
      rw [h, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using hz)]

-- The set of possible gate indices must remain nonempty even if the pass drops every gate.
private def spare : Gate := ⟨.or, []⟩

private theorem append_spare {z : ℕ} {rs : List ℕ} {x y : List Bool}
    (hr : Related z rs x y) (hz : y.length + 1 ≤ z) (i : ℕ) :
    x.getD i false = (run [spare] y).getD (ref z rs i) false := by
  rw [hr.2.2 i]
  change _ = (y ++ [readGate spare y]).getD (ref z rs i) false
  rcases hr.2.1 i with hi | hi
  · exact (List.getD_append _ _ _ _ hi).symm
  · rw [hi, List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simp; omega)]

private def positions (P : Gate → Bool) (gs : List Gate) : Finset (Fin gs.length) :=
  Finset.univ.filter fun j => P (gs.get j) = true

private theorem positions_mem (P : Gate → Bool) (gs : List Gate) (j : Fin gs.length) :
    j ∈ positions P gs ↔ P (gs.get j) = true := by
  simp [positions]

private theorem positions_card (P : Gate → Bool) (gs : List Gate) :
    (positions P gs).card = gs.countP P := by
  unfold positions
  rw [← List.countP_ofFn gs.get, List.ofFn_get]

private theorem two_positions {P : Gate → Bool} {gs : List Gate}
    {a b : Fin gs.length} (hab : a ≠ b) (ha : P (gs.get a) = true) (hb : P (gs.get b) = true) :
    2 ≤ gs.countP P := by
  have hs : ({a, b} : Finset (Fin gs.length)) ⊆ positions P gs := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact (positions_mem _ _ _).mpr ha
    · exact (positions_mem _ _ _).mpr hb
  have hc := Finset.card_le_card hs
  simpa [hab, positions_card] using hc

private theorem cover_bound {α : Type} {t : ℕ} (S : Finset α) (i : Fin t → α)
    (h : ∀ s ∈ S, ∃ j, i j = s) : S.card ≤ t := by
  classical
  have hs : S ⊆ Finset.univ.image i := by
    intro s hs
    obtain ⟨j, hj⟩ := h s hs
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  exact (Finset.card_le_card hs).trans (by simpa using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := i)))

private theorem cover_of_bound {α : Type} {t : ℕ} (S : Finset α)
    (base : α) (h : S.card ≤ t) : ∃ f : Fin t → α, ∀ s ∈ S, ∃ j, f j = s := by
  classical
  let e := S.equivFin
  let f (j : Fin t) : α :=
    if hj : j.val < S.card then (e.symm ⟨j.val, hj⟩).val else base
  refine ⟨f, ?_⟩
  intro s hs
  let k := e ⟨s, hs⟩
  refine ⟨⟨k.val, lt_of_lt_of_le k.isLt h⟩, ?_⟩
  have he : e.symm k = ⟨s, hs⟩ := e.symm_apply_apply _
  simp [f, k.isLt, he]

private theorem restrict_sum {n : ℕ} (S : Finset (Fin n)) (p : Fin n) (x : Fin n → Bool) :
    (∃ v ∈ S, Function.update x p false v = true) ↔ ∃ v ∈ S, v ≠ p ∧ x v = true := by
  constructor
  · rintro ⟨v, hv, hval⟩
    have hvp : v ≠ p := by
      intro he
      subst v
      simp at hval
    exact ⟨v, hv, hvp, by simpa [Function.update_of_ne hvp] using hval⟩
  · rintro ⟨v, hv, hvp, hval⟩
    exact ⟨v, hv, by simpa [Function.update_of_ne hvp] using hval⟩

end PEqualNP.Outside.L_meta_1332_aux

open PEqualNP.Outside.L_meta_1332_aux

theorem PEqualNP.Outside.L_meta_1332 :
    ∀ (n m : ℕ) (S : Fin m →
    Finset (Fin n)), (∀ i j : Fin m, i ≠ j →
    (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m →
    ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ (o : Fin m) (x : Fin n →
    Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) →
    ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) →
    ∀ a b : Fin gates.length, a ≠ b →
    ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (gates.get a).inputs.length = 2 →
    p.val ∈ (gates.get a).inputs →
    ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (gates.get b).inputs.length = 2 →
    p.val ∈ (gates.get b).inputs →
    ∀ (t : ℕ) (ι : Fin t →
    Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    ∃ r : Fin t, ι r = q) →
    ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 →
    q2 ∈ I) →
    ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m →
    ℕ) (κ : Fin t →
    Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 →
    q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n →
    Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _ gates out hallow hspec p _ a b hab haop halen hap hbop hblen hbp t ii hii I hI
  let z := n + gates.length + 1
  let result := pass z p.val n (refsFor z p) gates
  let gl := result.1 ++ [spare]
  let ol (o : Fin m) := ref z result.2 (out o)
  let J := positions binary gl
  obtain ⟨hl, hn, hb, hok⟩ :=
    pass_counts z p.val n (refsFor z p) gates hallow
  change result.1.length ≤ gates.length at hl
  change result.1.countP neg = gates.countP neg at hn
  change result.1.countP binary + gates.countP (skip p.val) = gates.countP binary at hb
  have hTwo : 2 ≤ gates.countP (skip p.val) :=
    two_positions hab ((skip_iff _ _).mpr ⟨⟨haop, halen⟩, hap⟩)
      ((skip_iff _ _).mpr ⟨⟨hbop, hblen⟩, hbp⟩)
  have hOldB : gates.countP binary ≤ I.card := by
    rw [← positions_card]
    apply Finset.card_le_card
    intro q hq
    exact hI q ((binary_iff _).mp ((positions_mem _ _ _).mp hq))
  have hJ : J.card = result.1.countP binary := by
    simp [J, positions_card, gl, List.countP_append, spare, binary]
  have hOldN : gates.countP neg ≤ t := by
    rw [← positions_card]
    apply cover_bound _ ii
    intro q hq
    exact hii q ((neg_iff _).mp ((positions_mem _ _ _).mp hq))
  have hNewN : (positions neg gl).card ≤ t := by
    rw [positions_card]
    simpa [gl, List.countP_append, spare, neg, hn] using hOldN
  have hgl : 0 < gl.length := by simp [gl]
  obtain ⟨κ, hκ⟩ := cover_of_bound (positions neg gl) ⟨0, hgl⟩ hNewN
  refine ⟨gl, ol, κ, J, ?_, ?_, ?_, by omega, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hok g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact ⟨Or.inr (Or.inl rfl), by decide⟩
  · intro q hq
    exact hκ q ((positions_mem _ _ _).mpr ((neg_iff _).mpr hq))
  · intro q hq
    exact (positions_mem _ _ _).mpr ((binary_iff _).mpr hq)
  · intro o x
    let X := List.ofFn x
    let X' := List.ofFn (Function.update x p false)
    have hx : X.length = n := List.length_ofFn
    have hr : Related z result.2 (run gates X') (run result.1 X) := by
      have hzero : ref z (refsFor z p) p.val = z := by simp [ref, refsFor]
      have hp : p.val < (refsFor z p).length := by simp [refsFor]
      have hz : X.length + gates.length ≤ z := by rw [hx]; exact Nat.le_succ _
      have h := pass_sound z p.val gates (refsFor z p) X' X
        (input_related p x (by dsimp [z]; omega)) hp hzero hz
      rw [hx] at h
      exact h
    have hz : (run result.1 X).length + 1 ≤ z := by rw [run_length, hx]; dsimp [z]; omega
    have he := append_spare hr hz (out o)
    have hrun : run gl X = run [spare] (run result.1 X) := by
      simp only [gl, run, List.foldl_append]
    change (run gl X).getD (ol o) false = _
    rw [hrun, ← he]
    change (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ X') = _
    rw [hspec o (Function.update x p false)]
    have h := restrict_sum (S o) p x
    by_cases hpos : ∃ v ∈ S o, Function.update x p false v = true
    · simp [hpos, h.mp hpos]
    · simp [hpos, mt h.mpr hpos]
