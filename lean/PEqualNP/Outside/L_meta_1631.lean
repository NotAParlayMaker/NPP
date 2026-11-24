import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1631_aux

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

end PEqualNP.Outside.L_meta_1631_aux
open PEqualNP.Outside.L_meta_1631_aux in
theorem PEqualNP.Outside.L_meta_1631 :
∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  intro q N L i0 p0 p1 hq hN card meet unique neq hp0 hp1 gates ops nonempty earlier ev he o
  constructor
  · intro full t
    have same (a : p0∈L t) (b : p1∈L t) : t=i0 := by
      by_contra ne
      have h := meet t i0 ne
      have more := Finset.one_lt_card.mpr ⟨p0,Finset.mem_inter.mpr ⟨a,hp0⟩,p1,Finset.mem_inter.mpr ⟨b,hp1⟩,neq⟩
      omega
    have outside (nt : t≠i0) : ∃ w∈L t,w∉L i0 := by
      by_contra! no
      have sub : L t ⊆ L i0 := fun p h => no p h
      have e := meet t i0 nt
      rw [Finset.inter_eq_left.mpr sub,card] at e
      omega
    have offdom : (decide (p0∉L t)=true ∨ decide (p1∉L t)=true ∨ ∀ u, u∉L i0 → decide (u∉L t)=true) := by
      by_cases a : p0∈L t
      · by_cases b : p1∈L t
        · exact Or.inr (Or.inr (fun u hu => decide_eq_true ((same a b).symm ▸ hu)))
        · exact Or.inr (Or.inl (decide_eq_true b))
      · exact Or.inl (decide_eq_true a)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [full _ _ offdom]; simp
    · intro h; rw [full _ _ (Or.inl (by simp))]; simp [h]
    · intro h; rw [full _ _ (Or.inr (Or.inl (by simp)))]; simp [h]
    · intro p hp
      constructor
      · rw [full _ _ (Or.inl (by simp))]; exact decide_eq_true ⟨p,hp,by simp⟩
      · rw [full _ _ (Or.inr (Or.inl (by simp)))]; exact decide_eq_true ⟨p,hp,by simp⟩
    · intro nt
      obtain ⟨w,hw,ho⟩ := outside nt
      rw [full _ _ (Or.inr (Or.inr (fun u h => decide_eq_true h)))]
      exact decide_eq_true ⟨w,hw,decide_eq_true ho⟩
    · intro w hw _ _
      rw [full _ _ (Or.inr (Or.inr (fun u h => decide_eq_true (Or.inl h))))]
      exact decide_eq_true ⟨w,(Finset.mem_inter.mp hw).1,by simp⟩
  · intro finite t x dom
    obtain ⟨off,sing0,sing1,paired,other,extra⟩ := finite t
    have lift (a b : Fin N → Bool) (hle : ∀ j, a j=true → b j=true) :
        ev (o t) a=true → ev (o t) b=true := by
      rw [he,he]
      exact value_mono ⟨gates,0⟩ ops a b hle (o t)
    by_cases hit : ∃ v∈L t, x v=true
    · rw [decide_eq_true hit]
      obtain ⟨w,hw,hx⟩ := hit
      rcases dom with h0|h1|all
      · apply lift _ x _ (paired w hw).1
        intro j hj
        rcases of_decide_eq_true hj with rfl|rfl <;> assumption
      · apply lift _ x _ (paired w hw).2
        intro j hj
        rcases of_decide_eq_true hj with rfl|rfl <;> assumption
      · by_cases diff : t≠i0
        · exact lift _ x (fun j hj => all j (of_decide_eq_true hj)) (other diff)
        · have eqt : t=i0 := not_not.mp diff
          subst t
          by_cases eq0 : w=p0
          · subst w
            exact lift _ x (fun j hj => (of_decide_eq_true hj : j=p0) ▸ hx) (sing0 hp0)
          by_cases eq1 : w=p1
          · subst w
            exact lift _ x (fun j hj => (of_decide_eq_true hj : j=p1) ▸ hx) (sing1 hp1)
          apply lift _ x _ (extra w (Finset.mem_inter.mpr ⟨hw,hw⟩) eq0 eq1)
          intro j hj
          rcases of_decide_eq_true hj with h|rfl
          · exact all j h
          · exact hx
    · rw [decide_eq_false hit]
      cases hx : ev (o t) x with
      | false => rfl
      | true =>
        have hot := lift x (fun j => decide (j∉L t)) (fun j hj => decide_eq_true (fun mem => hit ⟨j,mem,hj⟩)) hx
        exact Bool.noConfusion (hot.symm.trans off)
