import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1468

open PEqualNP.CircuitLowerBounds

private theorem outsider_plan {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hjoin : ∀ u v : Fin n, u ≠ v → ∃ i, u ∈ S i ∧ v ∈ S i)
    (outside : ∃ (R : Fin m) (O : Fin n), O ∉ S R) :
    ∃ r : Fin m → Fin n, (∀ i, r i ∉ S i) ∧
      (∀ i j, i ≠ j → ¬ (r i ∈ S j ∧ r j ∈ S i)) ∧
      ∀ i, 2 ≤ (Finset.univ \ S i).card := by
  classical
  obtain ⟨R,O,hO⟩ := outside
  have lo (i : Fin m) : 2 < (S i).card := by rw [hsize]; omega
  obtain ⟨a,ha⟩ : (S R).Nonempty := Finset.card_pos.mp (by have h := lo R; omega)
  obtain ⟨L,hOL,haL⟩ := hjoin O a (fun he => hO (he ▸ ha))
  have hLR : L ≠ R := fun he => hO (he ▸ hOL)
  have hul := Finset.card_union_add_card_inter (S L) (S R)
  have hnc : 2*q+1 ≤ n := by
    have hc := Finset.card_le_univ (S L ∪ S R)
    simp only [Fintype.card_fin] at hc
    rw [hcross L R hLR, hsize L, hsize R] at hul
    omega
  have hcompl (i : Fin m) : 2 ≤ (Finset.univ \ S i).card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S i))
    simp only [Finset.card_univ, Fintype.card_fin, hsize] at h
    omega
  have uniqueLine {i j : Fin m} {u v : Fin n}
      (huv : u ≠ v) (hui : u ∈ S i) (hvi : v ∈ S i)
      (huj : u ∈ S j) (hvj : v ∈ S j) : i = j := by
    by_contra he
    exact huv (Finset.card_le_one.1 ((hcross i j he).le) u (Finset.mem_inter.2 ⟨hui,huj⟩)
      v (Finset.mem_inter.2 ⟨hvi,hvj⟩))
  let e : (S R) ≃ Fin (q+1) := Finset.equivFinOfCardEq (hsize R)
  let step : Equiv.Perm (S R) := e.trans ((Equiv.addRight (1 : Fin (q+1))).trans e.symm)
  have step_eq (d : S R) : e (step d) = e d + 1 := by simp [step]
  have hone : (1 : Fin (q+1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < q+1)] at hv
  have htwo : (1 : Fin (q+1)) + 1 ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < q+1),
      Nat.mod_eq_of_lt (by omega : 1 + 1 < q+1)] at hv
  have step_ne (d : S R) : step d ≠ d := by
    intro he
    have hh : e d + 1 = e d + 0 := by rw [← step_eq, he, add_zero]
    exact hone (add_left_cancel hh)
  have step_step_ne (d : S R) : step (step d) ≠ d := by
    intro he
    have hh : e d + (1 + 1) = e d + 0 := by
      have h := congrArg e he
      rw [step_eq, step_eq, add_assoc] at h
      simpa using h
    exact htwo (add_left_cancel hh)
  have next_ne (d : S R) : step.symm d ≠ d := by
    intro he
    apply step_ne d
    have hh := step.apply_symm_apply d
    rwa [he] at hh
  have next_twice_ne (d : S R) : step.symm (step.symm d) ≠ d := by
    intro he
    have h := congrArg (fun d => step (step d)) he
    simp only [Equiv.apply_symm_apply] at h
    exact step_step_ne d h.symm
  have ex_dir (i : Fin m) (hi : i ≠ R) : ∃ d : S R, d.val ∈ S i := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by rw [hcross i R hi]; decide)
    obtain ⟨hpi,hpr⟩ := Finset.mem_inter.1 hp
    exact ⟨⟨p,hpr⟩,hpi⟩
  let dir (i : Fin m) : S R := if h : i ≠ R then (ex_dir i h).choose else ⟨a,ha⟩
  have dir_mem (i : Fin m) (hi : i ≠ R) : (dir i).val ∈ S i := by
    simpa [dir,hi] using (ex_dir i hi).choose_spec
  have dir_unique (i : Fin m) (hi : i ≠ R) (d : S R) (hd : d.val ∈ S i) : d = dir i := by
    apply Subtype.ext
    exact Finset.card_le_one.1 (hcross i R hi).le _ (Finset.mem_inter.2 ⟨hd,d.2⟩) _
      (Finset.mem_inter.2 ⟨dir_mem i hi,(dir i).2⟩)
  have ex_line (d : S R) : ∃ i : Fin m, O ∈ S i ∧ d.val ∈ S i :=
    hjoin O d.val (fun he => hO (he ▸ d.2))
  let thru (d : S R) : Fin m := (ex_line d).choose
  have omem (d : S R) : O ∈ S (thru d) := (ex_line d).choose_spec.1
  have dmem (d : S R) : d.val ∈ S (thru d) := (ex_line d).choose_spec.2
  have th_ne (d : S R) : thru d ≠ R := by
    intro h
    exact hO (by simpa only [h] using omem d)
  have th_dir (d : S R) : dir (thru d) = d := (dir_unique _ (th_ne d) d (dmem d)).symm
  have dir_th (i : Fin m) (hi : i ≠ R) (hOi : O ∈ S i) : thru (dir i) = i :=
    uniqueLine (fun he : O = (dir i).val => hO (he ▸ (dir i).2))
      (omem _) (dmem _) hOi (dir_mem i hi)
  have ex_other (d : S R) : ∃ p ∈ S (thru d), p ≠ O ∧ p ≠ d.val := by
    by_contra! h
    have hs : S (thru d) ⊆ {O,d.val} := by
      intro p hp
      by_cases ho : p = O
      · simp [ho]
      · have hd := h p hp ho
        simp [hd]
    have hb := Finset.card_le_card hs
    have ht := Finset.card_insert_le O ({d.val} : Finset (Fin n))
    simp only [Finset.card_singleton] at ht
    have hl := lo (thru d)
    omega
  let other (d : S R) : Fin n := (ex_other d).choose
  have other_mem (d : S R) : other d ∈ S (thru d) := (ex_other d).choose_spec.1
  have other_ne (d : S R) : other d ≠ O := (ex_other d).choose_spec.2.1
  have other_off (d : S R) : other d ∉ S R := by
    intro h
    have hh := dir_unique (thru d) (th_ne d) ⟨other d,h⟩ (other_mem d)
    rw [th_dir d] at hh
    exact (ex_other d).choose_spec.2.2 (congrArg Subtype.val hh)
  let r (i : Fin m) : Fin n :=
    if i = R then O else if O ∈ S i then other (step.symm (dir i)) else (step (dir i)).val
  have rR : r R = O := by simp [r]
  have rOn (i : Fin m) (hi : i ≠ R) (hOi : O ∈ S i) :
      r i = other (step.symm (dir i)) := by simp [r,hi,hOi]
  have rOff (i : Fin m) (hi : i ≠ R) (hOi : O ∉ S i) :
      r i = (step (dir i)).val := by simp [r,hi,hOi]
  refine ⟨r, ?_, ?_, hcompl⟩
  · intro i
    by_cases hi : i = R
    · subst i
      rwa [rR]
    by_cases hOi : O ∈ S i
    · rw [rOn i hi hOi]
      intro hm
      have he := uniqueLine (other_ne _).symm (omem _) (other_mem _) hOi hm
      have hh := congrArg dir he
      rw [th_dir] at hh
      exact next_ne (dir i) hh
    · rw [rOff i hi hOi]
      exact fun h => step_ne (dir i) (dir_unique i hi _ h)
  · have through_points (i j : Fin m) (hi : i ≠ R) (hj : j ≠ R)
        (hOi : O ∈ S i) (hOj : O ∈ S j) (hri : r i ∈ S j) :
        step.symm (dir i) = dir j := by
      rw [rOn i hi hOi] at hri
      have he := uniqueLine (other_ne _).symm (omem _) (other_mem _) hOj hri
      have hh := congrArg dir he
      rwa [th_dir] at hh
    have mixed (i j : Fin m) (hi : i ≠ R) (hj : j ≠ R)
        (hOi : O ∈ S i) (hOj : O ∉ S j) (hri : r i ∈ S j) (hrj : r j ∈ S i) : False := by
      rw [rOff j hj hOj] at hrj
      have he := dir_unique i hi _ hrj
      have hh : step.symm (dir i) = dir j := by rw [← he, Equiv.symm_apply_apply]
      rw [rOn i hi hOi, hh] at hri
      have he' : thru (dir j) = j :=
        uniqueLine (fun e => other_off _ (e.symm ▸ (dir j).2))
          (dmem _) (other_mem _) (dir_mem j hj) hri
      exact hOj (he' ▸ omem _)
    intro i j hij h
    by_cases hi : i = R
    · subst i
      have hj : j ≠ R := Ne.symm hij
      by_cases ho : O ∈ S j
      · exact other_off _ (by simpa [rOn j hj ho] using h.2)
      · exact ho (by simpa [rR] using h.1)
    by_cases hj : j = R
    · subst j
      by_cases ho : O ∈ S i
      · exact other_off _ (by simpa [rOn i hi ho] using h.1)
      · exact ho (by simpa [rR] using h.2)
    by_cases ha : O ∈ S i <;> by_cases hb : O ∈ S j
    · have ha' := through_points i j hi hj ha hb h.1
      have hb' := through_points j i hj hi hb ha h.2
      exact next_twice_ne _ (by rw [ha',hb'])
    · exact mixed i j hi hj ha hb h.1 h.2
    · exact mixed j i hj hi hb ha h.2 h.1
    · have ha' : step (dir i) = dir j :=
        dir_unique j hj _ (by simpa [rOff i hi ha] using h.1)
      have hb' : step (dir j) = dir i :=
        dir_unique i hi _ (by simpa [rOff j hj hb] using h.2)
      exact step_step_ne _ (by rw [ha',hb'])

-- This cut and its wire evaluation are adapted from L-meta-1460.
private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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


private def Heavy {n : ℕ} (x : Fin n → Bool) : Prop :=
  2 ≤ (Finset.univ.filter (fun v => x v = true)).card

private def Allowed (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private def Fixed {n : ℕ} (C : Circuit) : Prop :=
  ∀ i : Fin C.gates.length, (C.gates.get i).op = .not →
    ∀ x : Fin n → Bool, Heavy x → value C x (n + (i : ℕ)) = false

private lemma gate_at_index {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin C.gates.length) :
    value C x (n + (i : ℕ)) =
      (C.gates.get i).op.eval ((C.gates.get i).inputs.map
        fun r => if r < n + (i : ℕ) then value C x r else false) := by
  have h := gate_value C x (n+i.val) (by omega) (by
    have h := i.isLt
    unfold Circuit.size
    omega)
  simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using h

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : Allowed C) (hFixed : Fixed (n := n) C)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), Heavy x → (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hheavy hxy hx
    have hvalue := hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩


    · let i : Fin C.gates.length := ⟨w-n, by unfold Circuit.size at hw; omega⟩
      have he : n + (i : ℕ) = w := by dsimp [i]; omega
      have hf := hFixed i hop x hheavy
      rw [he,hvalue] at hf
      cases hf

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : Allowed C) (hFixed : Fixed (n := n) C)
    (x y : Fin n → Bool) (hx : Heavy x) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG hFixed w (by omega) hw
      exact hstep x y hx fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

private def input {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ A)

private def probes {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  S.filter fun p => value C (input (R p)) w = true

private lemma mem_probes {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ probes C S R w ↔ p ∈ S ∧ value C (input (R p)) w = true := by
  simp [probes]


private lemma heavy_input {n : ℕ} (A : Finset (Fin n)) (h : 2 ≤ A.card) : Heavy (input A) := by
  have he : (Finset.univ.filter fun p => input A p = true) = A := by ext p; simp [input]
  unfold Heavy
  rwa [he]

private def outside {n : ℕ} (S : Finset (Fin n)) (p : Fin n) : Bool :=
  decide (p ∉ S)

private def charged {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, w = n + j.val ∧
    (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    value C (outside S) w = false ∧ 2 ≤ (probes C S R w).card ∧
    ∀ r ∈ (C.gates.get j).inputs, (probes C S R r).Nonempty

-- A gate rejecting the outside assignment can be replaced by earlier rejecting wires.
-- Only a binary OR with two productive reads can enlarge this frontier.
private lemma expand {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (hG : Allowed C) (hFixed : Fixed (n := n) C)
    (hR : ∀ p ∈ S, R p ∩ S = {p}) (hHeavy : ∀ p ∈ S, Heavy (input (R p))) (w : ℕ)
    (hF : value C (outside S) w = false) (hLarge : 1 < (probes C S R w).card) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (1 < P.card → charged C S R w) ∧
      (∀ r ∈ P, r < w ∧ value C (outside S) r = false) ∧
      probes C S R w ⊆ P.biUnion (probes C S R) := by
  classical
  have hw₀ : n ≤ w := by
    by_contra! hn
    let p : Fin n := ⟨w, hn⟩
    have hp : p ∈ S := by
      change value C (outside S) p = false at hF
      simpa [input_value, outside] using hF
    have hsmall : probes C S R w ⊆ {p} := by
      intro s hs
      obtain ⟨hsS, hv⟩ := (mem_probes C S R w s).1 hs
      change value C (input (R s)) p = true at hv
      have hr : p ∈ R s := by simpa [input_value, input] using hv
      have he : p ∈ ({s} : Finset (Fin n)) := hR s hsS ▸ Finset.mem_inter.mpr ⟨hr, hp⟩
      simp [Finset.mem_singleton.mp he]
    have hb := Finset.card_le_card hsmall
    simp at hb
    omega
  have hw₁ : w < n + C.size := by
    by_contra! hn
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    have hv := (mem_probes C S R w p).1 hp
    rw [missing_value C _ w hn] at hv
    simp_all
  let g := C.gates[w - n]'(by unfold Circuit.size at hw₁; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let read (x : Fin n → Bool) (r : ℕ) := if r < w then value C x r else false
  have hgate (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hw₀ hw₁
  have hAnd (h : g.op = GateOp.and) (x : Fin n → Bool) :
      value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
    rw [hgate, h, GateOp.eval, List.all_eq_true]
    simp
  have hOr (h : g.op = GateOp.or) (x : Fin n → Bool) :
      value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
    rw [hgate, h, GateOp.eval, List.any_eq_true]
    simp
  rcases hop with h | h | h
  · have hbad : ¬ ∀ r ∈ g.inputs, read (outside S) r = true := by
      rw [← hAnd h, hF]; decide
    push Not at hbad
    obtain ⟨r, hr, hrF⟩ := hbad
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    have hread := (hAnd h _).1 ((mem_probes C S R w p).1 hp).2 r hr
    have hrlt : r < w := (by simpa [read] using hread : r < w ∧ value C (input (R p)) r = true).1
    refine ⟨{r}, by simp, by simp, ?_, ?_⟩
    · intro s hs
      have he : s = r := Finset.mem_singleton.mp hs
      subst s
      exact ⟨hrlt, by simpa [read, hrlt] using hrF⟩
    · intro p hp
      obtain ⟨hps, hpv⟩ := (mem_probes C S R w p).1 hp
      exact Finset.mem_biUnion.mpr ⟨r, by simp, (mem_probes C S R r p).2
        ⟨hps, by simpa [read, hrlt] using (hAnd h _).1 hpv r hr⟩⟩
  · let P := g.inputs.toFinset.filter fun r => r < w ∧ (probes C S R r).Nonempty
    have hcard : P.card ≤ g.inputs.toFinset.card := Finset.card_filter_le _ _
    have hcard' := List.toFinset_card_le g.inputs
    refine ⟨P, by omega, ?_, ?_, ?_⟩
    · intro hlarge
      have hj : w - n < C.gates.length := by unfold Circuit.size at hw₁; omega
      have hlen' : g.inputs.length = 2 := by omega
      have hP : P = g.inputs.toFinset :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      refine ⟨⟨w - n, hj⟩, by simp; omega, h, hlen', hF, hLarge, ?_⟩
      intro r hr
      change r ∈ g.inputs at hr
      exact (Finset.mem_filter.mp (by rw [hP]; exact List.mem_toFinset.mpr hr : r ∈ P)).2.2
    · intro r hr
      obtain ⟨hri, hrlt, _⟩ := Finset.mem_filter.mp hr
      refine ⟨hrlt, ?_⟩
      have hn : read (outside S) r ≠ true := by
        intro ht
        have := (hOr h _).2 ⟨r, List.mem_toFinset.mp hri, ht⟩
        rw [hF] at this
        simp_all
      simpa [read, hrlt] using hn
    · intro p hp
      obtain ⟨hps, hpv⟩ := (mem_probes C S R w p).1 hp
      obtain ⟨r, hr, hrv⟩ := (hOr h _).1 hpv
      have hrlt : r < w := (by simpa [read] using hrv : r < w ∧ value C (input (R p)) r = true).1
      have hpr := (mem_probes C S R r p).2 ⟨hps, by simpa [read, hrlt] using hrv⟩
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr hr, hrlt, p, hpr⟩, hpr⟩
  · obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    obtain ⟨hpS,hv⟩ := (mem_probes C S R w p).1 hp
    let i : Fin C.gates.length := ⟨w-n, by unfold Circuit.size at hw₁; omega⟩
    have he : n + (i : ℕ) = w := by dsimp [i]; omega
    have hf := hFixed i h (input (R p)) (hHeavy p hpS)
    rw [he,hv] at hf
    cases hf

private lemma card_prefix (G : Finset ℕ) (t : ℕ) :
    (G.filter (· < t + 1)).card = (G.filter (· < t)).card + if t ∈ G then 1 else 0 := by
  classical
  by_cases ht : t ∈ G
  · have h : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw, hlt⟩
        by_cases he : w = t
        · exact Or.inl he
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hlt⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hw, by omega⟩
    rw [h, Finset.card_insert_of_notMem (by simp), ite_eq_left ht]
  · have h : G.filter (· < t + 1) = G.filter (· < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hlt⟩
        have hne : w ≠ t := fun e => ht (e ▸ hw)
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, hlt⟩
        exact ⟨hw, by omega⟩
    rw [h, ite_eq_right ht, Nat.add_zero]

-- Count each expanding wire at most once by processing the frontier in reverse order.
private lemma cut_card {α : Type*} [DecidableEq α]
    (P : ℕ → Finset α) (ok : ℕ → Prop) (G : Finset ℕ)
    (expandWire : ∀ w, ok w → 1 < (P w).card →
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → w ∈ G) ∧
        (∀ r ∈ B, r < w ∧ ok r) ∧ P w ⊆ B.biUnion P)
    (t : ℕ) (F : Finset ℕ)
    (hF : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t)) :
    (F.biUnion P).card ≤ F.card + (G.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    apply (Finset.card_biUnion_le_card_mul F P 1 ?_).trans
    · simp
    · intro r hr
      have h := (hF r hr).2
      omega
  | succ t ih =>
    by_cases ht : t ∈ F ∧ 1 < (P t).card
    · obtain ⟨B, hBcard, hcharge, hB, hcover⟩ := expandWire t (hF t ht.1).1 ht.2
      let F' := F.erase t ∪ B
      have hF' : ∀ w ∈ F', ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
          have ⟨hok, hlt⟩ := hF w hmem
          exact ⟨hok, fun h => by have := hlt h; omega⟩
        · exact ⟨(hB w hw).2, fun _ => (hB w hw).1⟩
      have hU : F.biUnion P ⊆ F'.biUnion P := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases h : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hpw⟩
      have hsize := Finset.card_union_le (F.erase t) B
      change F'.card ≤ _ at hsize
      have he := Finset.card_erase_add_one ht.1
      have hh := (Finset.card_le_card hU).trans (ih F' hF')
      rw [card_prefix]
      by_cases hg : t ∈ G
      · simp only [ite_eq_left hg]
        omega
      · simp only [ite_eq_right hg]
        have : B.card ≤ 1 := by by_contra! hl; exact hg (hcharge hl)
        omega
    · have hFt : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        refine ⟨(hF w hw).1, fun h => ?_⟩
        have hne : w ≠ t := fun e => ht ⟨e ▸ hw, e ▸ h⟩
        have := (hF w hw).2 h
        omega
      have hh := ih F hFt
      rw [card_prefix]
      omega

private noncomputable def charges {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) : Finset ℕ :=
  open Classical in
  (Finset.Ico n (n + C.size)).filter (charged C S R)

private lemma mem_charges {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) :
    w ∈ charges C S R ↔ charged C S R w := by
  classical
  rw [charges, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨j, rfl, _⟩ := h
  have hj := j.isLt
  unfold Circuit.size
  omega

private lemma charge_card {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hG : Allowed C) (hFixed : Fixed (n := n) C)
    (hR : ∀ p ∈ S, R p ∩ S = {p}) (hHeavy : ∀ p ∈ S, Heavy (input (R p)))
    (hFalse : value C (outside S) w = false)
    (hTrue : ∀ p ∈ S, value C (input (R p)) w = true) :
    S.card ≤ 1 + (charges C S R).card := by
  classical
  let G := charges C S R
  have hstep (r : ℕ) (hf : value C (outside S) r = false) (hcard : 1 < (probes C S R r).card) :
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → r ∈ G) ∧
        (∀ s ∈ B, s < r ∧ value C (outside S) s = false) ∧
        probes C S R r ⊆ B.biUnion (probes C S R) := by
    obtain ⟨B, hB, hcharge, hread, hcover⟩ := expand C S R hG hFixed hR hHeavy r hf hcard
    exact ⟨B, hB, fun h => (mem_charges C S R r).2 (hcharge h), hread, hcover⟩
  have hh := cut_card (probes C S R) (fun r => value C (outside S) r = false) G
    hstep (w + 1) {w} (by
      intro r hr
      have he : r = w := Finset.mem_singleton.mp hr
      subst r
      exact ⟨hFalse, fun _ => by omega⟩)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hh
  have hFull : probes C S R w = S := by
    ext p
    simp only [mem_probes]
    exact ⟨And.left, fun hp => ⟨hp, hTrue p hp⟩⟩
  rw [hFull] at hh
  have hbound := Finset.card_filter_le G (· < w + 1)
  change S.card ≤ 1 + G.card
  omega

private lemma cross_hit {n : ℕ} (C : Circuit)
    (S T : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hG : Allowed C) (hFixed : Fixed (n := n) C)
    (hSize : (S ∩ T).card ≤ 1) (hHeavy : ∀ p ∈ S, Heavy (input (R p)))
    (hCard : 2 ≤ (probes C S R w).card)
    (hFalse : value C (outside T) w = false) :
    ∃ p ∈ S \ T, (R p ∩ T).Nonempty := by
  classical
  have hex : ∃ p ∈ probes C S R w, p ∉ T := by
    by_contra! h
    have hsub : probes C S R w ⊆ S ∩ T := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨((mem_probes C S R w p).1 hp).1, h p hp⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp, hpt⟩ := hex
  obtain ⟨hps, hpw⟩ := (mem_probes C S R w p).1 hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hps, hpt⟩, ?_⟩
  by_contra hn
  have hxy (v : Fin n) (hv : input (R p) v = true) : outside T v = true := by
    simp only [input, decide_eq_true_eq] at hv
    simp only [outside, decide_eq_true_eq]
    exact fun ht => hn ⟨v, Finset.mem_inter.mpr ⟨hv, ht⟩⟩
  have := value_mono C hG hFixed _ _ (hHeavy p hps) hxy w hpw
  rw [hFalse] at this
  contradiction


private lemma not_source {n : ℕ} (C : Circuit) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op = .not) (hn : 3 ≤ n)
    (hfalse : ∀ x : Fin n → Bool, Heavy x → value C x (n+j.val) = false) :
    ∃ h : ℕ, n ≤ h ∧ h < n+j.val ∧ ∀ x : Fin n → Bool, Heavy x → value C x h = true := by
  classical
  let A : Finset (Fin n) := Finset.univ
  have hA : Heavy (input A) := heavy_input A (by simpa [A] using (show 2 ≤ n by omega))
  cases hs : (C.gates.get j).inputs with
  | nil =>
    have he := gate_at_index C (input A) j
    rw [hfalse _ hA,hop,hs] at he
    simp [GateOp.eval] at he
  | cons h rest =>
    have hsVal (x : Fin n → Bool) (hx : Heavy x) :
        h < n+j.val ∧ value C x h = true := by
      have he := hfalse x hx
      rw [gate_at_index,hop,hs] at he
      simpa [GateOp.eval] using he
    have hlt := (hsVal _ hA).1
    have hv (x : Fin n → Bool) (hx : Heavy x) : value C x h = true := (hsVal x hx).2
    have hh : n ≤ h := by
      by_contra! hh
      let p : Fin n := ⟨h,hh⟩
      let B := (Finset.univ : Finset (Fin n)).erase p
      have hB : 2 ≤ B.card := by
        have hc := Finset.card_erase_add_one (Finset.mem_univ p)
        change B.card + 1 = (Finset.univ : Finset (Fin n)).card at hc
        simp at hc
        omega
      have he := hv (input B) (heavy_input B hB)
      change value C (input B) p = true at he
      rw [input_value] at he
      simp [input,B] at he
    exact ⟨h,hh,hlt,hv⟩

private lemma outside_heavy {n : ℕ} (S : Finset (Fin n))
    (hS : 2 ≤ (Finset.univ \ S).card) : Heavy (outside S) := by
  have he : Finset.univ.filter (fun p => outside S p = true) = Finset.univ \ S := by
    ext p
    simp [outside]
  unfold Heavy
  rwa [he]

private theorem bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hjoin : ∀ u v : Fin n, u ≠ v → ∃ i, u ∈ S i ∧ v ∈ S i)
    (hex : ∃ (i : Fin m) (v : Fin n), v ∉ S i)
    (gates : List Gate) (out : Fin m → ℕ) (j : Fin gates.length)
    (hG : Allowed ⟨gates,0⟩)
    (hop : (gates.get j).op = .not)
    (hunique : ∀ i : Fin gates.length, (gates.get i).op = .not → i = j)
    (hval : ∀ (i : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates,out i⟩ (List.ofFn x) = decide (∃ p ∈ S i, x p = true))
    (hfalse : ∀ x : Fin n → Bool, Heavy x →
      Circuit.eval ⟨gates,n+j.val⟩ (List.ofFn x) = false) :
    m*q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n+j.val ∈ (gates.get i).inputs)).card + 2
      ≤ gates.length := by
  classical
  obtain ⟨r,hr,hm,hopen⟩ := outsider_plan S hq hsize hcross hjoin hex
  obtain ⟨i₀,p₀,hp₀⟩ := hex
  have hn : 3 ≤ n := by
    have hc := Finset.card_le_univ (S i₀)
    rw [hsize] at hc
    simp at hc
    omega
  let C : Circuit := ⟨gates,0⟩
  let z := n+j.val
  have hfixed : Fixed (n := n) C := by
    intro i hi x hx
    obtain rfl := hunique i hi
    exact hfalse x hx
  obtain ⟨h,hhn,hhz,hsrc⟩ := not_source C j hop hn (fun x hx => hfalse x hx)
  let R (i : Fin m) (p : Fin n) : Finset (Fin n) := {p,r i}
  have probe_size (i : Fin m) (p : Fin n) (hp : p ∈ S i) : Heavy (input (R i p)) := by
    have hne : p ≠ r i := fun he => hr i (he ▸ hp)
    exact heavy_input _ (by simp [R,hne])
  have probe_inter (i : Fin m) (p : Fin n) (hp : p ∈ S i) : R i p ∩ S i = {p} := by
    ext v
    constructor
    · rintro hv
      obtain ⟨hvp,hvs⟩ := Finset.mem_inter.mp hv
      rcases (show v = p ∨ v = r i by simpa [R] using hvp) with rfl | rfl
      · simp
      · exact (hr i hvs).elim
    · intro hv
      obtain rfl := Finset.mem_singleton.mp hv
      exact Finset.mem_inter.mpr ⟨by simp [R],hp⟩
  have true_out (i : Fin m) (p : Fin n) (hp : p ∈ S i) : value C (input (R i p)) (out i) = true := by
    change Circuit.eval ⟨gates,out i⟩ (List.ofFn (input (R i p))) = true
    rw [hval]
    exact decide_eq_true ⟨p,hp,by simp [R,input]⟩
  have false_out (i : Fin m) : value C (outside (S i)) (out i) = false := by
    change Circuit.eval ⟨gates,out i⟩ (List.ofFn (outside (S i))) = false
    rw [hval]
    simp [outside]
  let G (i : Fin m) := charges C (S i) (R i)
  have hGcard (i : Fin m) : q ≤ (G i).card := by
    have hc := charge_card C (S i) (R i) (out i) hG hfixed (probe_inter i) (probe_size i)
      (false_out i) (true_out i)
    rw [hsize] at hc
    change q ≤ (charges C (S i) (R i)).card
    omega
  have hDis : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ k _ hik
    change Disjoint (G i) (G k)
    rw [Finset.disjoint_left]
    intro w hwi hwk
    obtain ⟨_,_,_,_,hfi,hci,_⟩ := (mem_charges C (S i) (R i) w).1 hwi
    obtain ⟨_,_,_,_,hfk,hck,_⟩ := (mem_charges C (S k) (R k) w).1 hwk
    obtain ⟨p,hp,v,hv⟩ := cross_hit C (S i) (S k) (R i) w hG hfixed (by rw [hcross i k hik]) (probe_size i) hci hfk
    obtain ⟨s,hs,u,hu⟩ := cross_hit C (S k) (S i) (R k) w hG hfixed (by rw [hcross k i hik.symm]) (probe_size k) hck hfi
    have hri : r i ∈ S k := by
      obtain ⟨hvr,hvk⟩ := Finset.mem_inter.mp hv
      rcases (show v = p ∨ v = r i by simpa [R] using hvr) with rfl | rfl
      · exact ((Finset.mem_sdiff.mp hp).2 hvk).elim
      · exact hvk
    have hrk : r k ∈ S i := by
      obtain ⟨hur,hui⟩ := Finset.mem_inter.mp hu
      rcases (show u = s ∨ u = r k by simpa [R] using hur) with rfl | rfl
      · exact ((Finset.mem_sdiff.mp hs).2 hui).elim
      · exact hui
    exact hm i k hik ⟨hri,hrk⟩
  let U := Finset.univ.biUnion G
  have hU : m*q ≤ U.card := by
    calc
      m*q = ∑ i : Fin m, q := by simp
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hGcard i)
      _ = U.card := (Finset.card_biUnion hDis).symm

  let Ids := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ z ∈ (gates.get i).inputs)
  let Readers := Ids.image (fun i : Fin gates.length => n+(i : ℕ))
  have hReader_lt (w : ℕ) (hw : w ∈ Readers) : z < w := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hw
    have hj := (Finset.mem_filter.1 hi).2.1
    change j.val < i.val at hj
    dsimp [z]
    omega
  have probe_z (i : Fin m) : probes C (S i) (R i) z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro p hp
    obtain ⟨hps,hv⟩ := (mem_probes C (S i) (R i) z p).1 hp
    have hz := hfixed j hop (input (R i p)) (probe_size i p hps)
    change value C (input (R i p)) z = false at hz
    rw [hv] at hz
    cases hz
  have no_z : z ∉ U := by
    intro hz
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨_,_,_,_,_,hc,_⟩ := (mem_charges C (S i) (R i) z).1 hi
    simp [probe_z i] at hc
  have no_h : h ∉ U := by
    intro hh
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 hh
    obtain ⟨_,_,_,_,hv,_,_⟩ := (mem_charges C (S i) (R i) h).1 hi
    rw [hsrc (outside (S i)) (outside_heavy (S i) (hopen i))] at hv
    cases hv
  have dis : Disjoint U Readers := Finset.disjoint_left.mpr (by
    intro w hw hr
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 hw
    obtain ⟨k,hk,_,_,_,_,hprod⟩ := (mem_charges C (S i) (R i) w).1 hi
    obtain ⟨l,hl,he⟩ := Finset.mem_image.1 hr
    change Fin gates.length at k
    have hkl : k = l := Fin.ext (by omega)
    subst k
    have hz := hprod z (Finset.mem_filter.1 hl).2.2
    rw [probe_z i] at hz
    simp at hz)
  have hReadCard : Readers.card = Ids.card := Finset.card_image_of_injective _
    (fun a b he => Fin.ext (Nat.add_left_cancel he))
  let All := insert h (insert z (U ∪ Readers))
  have hNotRead : z ∉ Readers := fun hh => (Nat.lt_irrefl z) (hReader_lt z hh)
  have hSrcRead : h ∉ Readers := fun hh => (Nat.not_lt_of_ge hhz.le) (hReader_lt h hh)
  have hzNe : h ≠ z := hhz.ne
  have hcard : All.card = U.card + Ids.card + 2 := by
    change (insert h (insert z (U ∪ Readers))).card = _
    rw [Finset.card_insert_of_notMem (by simp [hzNe,no_h,hSrcRead])]
    rw [Finset.card_insert_of_notMem (by simp [no_z,hNotRead])]
    rw [Finset.card_union_of_disjoint dis,hReadCard]
  have hZ : z ∈ Finset.Ico n (n+C.size) := by
    have hj := j.isLt
    dsimp [C,z,Circuit.size]
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have hsub : All ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    change w ∈ insert h (insert z (U ∪ Readers)) at hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact Finset.mem_Ico.mpr ⟨hhn,hhz.trans (Finset.mem_Ico.1 hZ).2⟩
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hZ
    rcases Finset.mem_union.1 hw with hu | hr
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 hu
      exact (Finset.mem_filter.1 hi).1
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hr
      exact Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt _⟩
  have hlen := Finset.card_le_card hsub
  rw [hcard, Nat.card_Ico, Nat.add_sub_cancel_left] at hlen
  change m*q + Ids.card + 2 ≤ C.size
  omega

end PEqualNP.Outside.L_meta_1468


theorem PEqualNP.Outside.L_meta_1468 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  exact fun q n m S hq hs hc hj he gates out j hG hp hu hv hf =>
    PEqualNP.Outside.L_meta_1468.bound S hq hs hc hj he gates out j hG hp hu hv hf
