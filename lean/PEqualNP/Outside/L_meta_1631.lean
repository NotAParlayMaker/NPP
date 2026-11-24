import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631_aux

open PEqualNP.CircuitLowerBounds

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      value C x (n + k) = true → value C y (n + k) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


lemma andOr_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  apply mono C x y hxy
  intro k hk hn
  exact (hn (hC _ (List.getElem_mem hk))).elim


end PEqualNP.Outside.L_meta_1631_aux

open PEqualNP.Outside.L_meta_1631_aux

theorem PEqualNP.Outside.L_meta_1631 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
  classical
  intro q N L i0 p0 p1 hq hN hcard hinter hpoints hne hp0 hp1 gates hgate hlen hback ev hev o
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  have hC : PEqualNP.EdgeOwnership.AndOrOnly C := fun g hg => (hgate g hg).1
  have evVal (w : ℕ) (x : Fin N → Bool) : ev w x = value C x w := hev w x
  have mono (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
      ev w x = true → ev w y = true := by
    simp only [evVal]
    exact andOr_mono C hC x y hxy w
  let Dom (x : Fin N → Bool) : Prop := x p0 = true ∨ x p1 = true ∨ ∀ u, u ∉ L i0 → x u = true
  have line_eq (t : Fin N) (h0 : p0 ∈ L t) (h1 : p1 ∈ L t) : t = i0 := by
    by_contra ht
    have hc : (L i0 ∩ L t).card ≤ 1 := by rw [hinter i0 t (Ne.symm ht)]
    exact hne (Finset.card_le_one.mp hc p0 (Finset.mem_inter.mpr ⟨hp0, h0⟩)
      p1 (Finset.mem_inter.mpr ⟨hp1, h1⟩))
  have coDom (t : Fin N) : Dom (fun v => decide (v ∉ L t)) := by
    by_cases h0 : p0 ∈ L t
    · by_cases h1 : p1 ∈ L t
      · have ht := line_eq t h0 h1
        subst t
        exact Or.inr (Or.inr fun u hu => by simpa using hu)
      · exact Or.inr (Or.inl (by simpa using h1))
    · exact Or.inl (by simpa using h0)
  have offPoint (t : Fin N) (ht : t ≠ i0) : ∃ p ∈ L t, p ∉ L i0 := by
    by_contra! hn
    have hs : L t ⊆ L t ∩ L i0 := fun p hp => Finset.mem_inter.mpr ⟨hp, hn p hp⟩
    have hc := Finset.card_le_card hs
    rw [hcard t, hinter t i0 ht] at hc
    omega
  constructor
  · intro h t
    have test (x : Fin N → Bool) (hd : Dom x) (hit : ∃ v ∈ L t, x v = true) : ev (o t) x = true := by
      rw [h t x hd]
      simp [hit]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h t _ (coDom t)]
      simp
    · intro hp
      exact test _ (Or.inl (by simp)) ⟨p0, hp, by simp⟩
    · intro hp
      exact test _ (Or.inr (Or.inl (by simp))) ⟨p1, hp, by simp⟩
    · intro p hp
      constructor
      · exact test _ (Or.inl (by simp)) ⟨p, hp, by simp⟩
      · exact test _ (Or.inr (Or.inl (by simp))) ⟨p, hp, by simp⟩
    · intro ht
      obtain ⟨p, hp, hpoff⟩ := offPoint t ht
      exact test _ (Or.inr (Or.inr fun u hu => by simpa using hu)) ⟨p, hp, by simpa using hpoff⟩
    · intro w hw hw0 hw1
      exact test _ (Or.inr (Or.inr fun u hu => by simp [hu]))
        ⟨w, (Finset.mem_inter.mp hw).1, by simp⟩
  · intro tests t x hx
    obtain ⟨hco, hs0, hs1, hpair, hoff, hrim⟩ := tests t
    by_cases hit : ∃ p ∈ L t, x p = true
    · suffices ev (o t) x = true by simpa [hit] using this
      obtain ⟨p, hp, hpx⟩ := hit
      rcases hx with hx0 | hx1 | hall
      · apply mono (o t) (fun v => decide (v = p0 ∨ v = p)) x ?_ (hpair p hp).1
        intro v hv
        rcases of_decide_eq_true hv with rfl | rfl
        · exact hx0
        · exact hpx
      · apply mono (o t) (fun v => decide (v = p1 ∨ v = p)) x ?_ (hpair p hp).2
        intro v hv
        rcases of_decide_eq_true hv with rfl | rfl
        · exact hx1
        · exact hpx
      · by_cases ht : t = i0
        · by_cases he0 : p = p0
          · subst p
            apply mono (o t) (fun v => decide (v = p0)) x ?_ (hs0 hp)
            intro v hv
            have he : v = p0 := of_decide_eq_true hv
            subst v
            exact hpx
          · by_cases he1 : p = p1
            · subst p
              apply mono (o t) (fun v => decide (v = p1)) x ?_ (hs1 hp)
              intro v hv
              have he : v = p1 := of_decide_eq_true hv
              subst v
              exact hpx
            · have hpI : p ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hp, ht ▸ hp⟩
              apply mono (o t) (fun v => decide (v ∉ L i0 ∨ v = p)) x ?_ (hrim p hpI he0 he1)
              intro v hv
              rcases of_decide_eq_true hv with hout | rfl
              · exact hall v hout
              · exact hpx
        · apply mono (o t) (fun v => decide (v ∉ L i0)) x ?_ (hoff ht)
          intro v hv
          exact hall v (of_decide_eq_true hv)
    · have hfalse : ev (o t) x = false := by
        cases hv : ev (o t) x with
        | false => rfl
        | true =>
          have hh := mono (o t) x (fun v => decide (v ∉ L t)) (by
            intro v hxv
            have hnot : v ∉ L t := fun hvL => hit ⟨v, hvL, hxv⟩
            simpa using hnot) hv
          rw [hco] at hh
          contradiction
      simpa [hit] using hfalse