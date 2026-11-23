import Mathlib
import PEqualNP.Defs

-- Every wire that is false at the zero input is true on a set of unit inputs lying inside one
-- class of a partition of D. An AND gate keeps the set inside a class of one of its inputs; an OR
-- gate with two inputs joins at most two classes. The output holds all of D in one class, so the
-- partition has one class, and the number of classes dropped at most once per OR gate.

namespace PEqualNP.Outside.L601

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (gs ++ [g]).foldl step x = step (gs.foldl step x) g := by
  simp [List.foldl_append]

theorem length_foldl (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [step]
    omega

theorem getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]
    simp
    omega

open Classical in
noncomputable def orPos (gs : List Gate) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j => ∃ g, gs[j]? = some g ∧ g.op = GateOp.or)

theorem orPos_mono (gs : List Gate) (g : Gate) : orPos gs ⊆ orPos (gs ++ [g]) := by
  intro j hj
  simp only [orPos, Finset.mem_filter, Finset.mem_range] at hj ⊢
  obtain ⟨hjl, g', hg', hop⟩ := hj
  exact ⟨by simp; omega, g', by rw [List.getElem?_append_left hjl]; exact hg', hop⟩

theorem orPos_snoc_or (gs : List Gate) (g : Gate) (hg : g.op = GateOp.or) :
    (orPos gs).card + 1 ≤ (orPos (gs ++ [g])).card := by
  have hnot : gs.length ∉ orPos gs := by simp [orPos]
  have hin : gs.length ∈ orPos (gs ++ [g]) := by
    simp only [orPos, Finset.mem_filter, Finset.mem_range, List.length_append,
      List.length_singleton]
    exact ⟨by omega, g, by simp, hg⟩
  rw [← Finset.card_insert_of_notMem hnot]
  exact Finset.card_le_card (Finset.insert_subset hin (orPos_mono gs g))

-- joining the class with label b into the class with label a drops at most one class
theorem card_merge {n : ℕ} (D : Finset (Fin n)) (c : Fin n → ℕ) (a b : ℕ) :
    (D.image c).card ≤ (D.image (fun i => if c i = b then a else c i)).card + 1 := by
  have h1 : D.image (fun i => if c i = b then a else c i) =
      (D.image c).image (fun x => if x = b then a else x) := by
    rw [Finset.image_image]; rfl
  rw [h1]
  have h2 : ((D.image c).erase b).card ≤
      ((D.image c).image (fun x => if x = b then a else x)).card := by
    calc ((D.image c).erase b).card
        = (((D.image c).erase b).image (fun x => if x = b then a else x)).card := by
          rw [Finset.card_image_of_injOn]
          intro x hx y hy hxy
          have hx' : x ≠ b := (Finset.mem_erase.1 hx).1
          have hy' : y ≠ b := (Finset.mem_erase.1 hy).1
          simp only [if_neg hx', if_neg hy'] at hxy
          exact hxy
      _ ≤ _ := Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset _ _))
  have h3 := Finset.pred_card_le_card_erase (s := D.image c) (a := b)
  omega

def x0 (n : ℕ) : List Bool := List.ofFn (fun _ : Fin n => false)

def xe (n : ℕ) (u : Fin n) : List Bool := List.ofFn (fun w : Fin n => decide (w = u))

def Good (n : ℕ) (D : Finset (Fin n)) (c : Fin n → ℕ) (gs : List Gate) : Prop :=
  ∀ w : ℕ, (gs.foldl step (x0 n)).getD w false = false → ∀ u ∈ D, ∀ v ∈ D,
    (gs.foldl step (xe n u)).getD w false = true →
    (gs.foldl step (xe n v)).getD w false = true → c u = c v

theorem main (n : ℕ) (D : Finset (Fin n)) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ c : Fin n → ℕ, D.card ≤ (D.image c).card + (orPos gs).card ∧ Good n D c gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun i => i.val, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective]
      simp
    · intro w _ u hu v hv h1 h2
      simp only [List.foldl_nil, xe, List.getD_eq_getElem?_getD, List.getElem?_ofFn] at h1 h2
      by_cases hw : w < n
      · simp only [hw, dite_true, Option.getD_some, decide_eq_true_eq] at h1 h2
        rw [← h1, ← h2]
      · simp [hw] at h1
  | append_singleton gs g ih =>
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hgs g (by simp)
    obtain ⟨c, hcount, hgood⟩ := ih (fun g' hg' => hgs g' (by simp [hg']))
    have hlen0 : (gs.foldl step (x0 n)).length = n + gs.length := by
      rw [length_foldl]; simp [x0]
    have hlenU : ∀ u, (gs.foldl step (xe n u)).length = n + gs.length := by
      intro u; rw [length_foldl]; simp [xe]
    -- the value of every wire after one more gate
    have hval0 : ∀ w, ((gs ++ [g]).foldl step (x0 n)).getD w false =
        if w < n + gs.length then (gs.foldl step (x0 n)).getD w false
        else if w = n + gs.length then
          g.op.eval (g.inputs.map fun j => (gs.foldl step (x0 n)).getD j false)
        else false := by
      intro w; rw [foldl_snoc, getD_step, hlen0]
    have hvalU : ∀ u w, ((gs ++ [g]).foldl step (xe n u)).getD w false =
        if w < n + gs.length then (gs.foldl step (xe n u)).getD w false
        else if w = n + gs.length then
          g.op.eval (g.inputs.map fun j => (gs.foldl step (xe n u)).getD j false)
        else false := by
      intro u w; rw [foldl_snoc, getD_step, hlenU]
    rcases hg.1 with hand | hor
    · -- an AND gate keeps the partition
      refine ⟨c, le_trans hcount (by
        have := Finset.card_le_card (orPos_mono gs g); omega), ?_⟩
      intro w hz u hu v hv h1 h2
      rw [hval0] at hz
      rw [hvalU] at h1 h2
      split_ifs at hz h1 h2 with hw hw'
      · exact hgood w hz u hu v hv h1 h2
      · rw [hand] at hz h1 h2
        simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false,
          Function.comp_apply, id] at hz h1 h2
        obtain ⟨a, ha, hza⟩ := hz
        exact hgood a (by simpa using hza) u hu v hv (h1 a ha) (h2 a ha)
    · -- an OR gate joins at most two classes
      have hpair : ∃ c' : Fin n → ℕ, (D.image c).card ≤ (D.image c').card + 1 ∧
          (∀ u v, c u = c v → c' u = c' v) ∧
          (∀ a ∈ g.inputs, ∀ b ∈ g.inputs,
            (gs.foldl step (x0 n)).getD a false = false →
            (gs.foldl step (x0 n)).getD b false = false →
            ∀ u ∈ D, ∀ v ∈ D, (gs.foldl step (xe n u)).getD a false = true →
              (gs.foldl step (xe n v)).getD b false = true → c' u = c' v) := by
        have hl := hg.2
        match hins : g.inputs with
        | [] =>
          exact ⟨c, by omega, fun _ _ h => h, by intro a ha; simp at ha⟩
        | [a0] =>
          refine ⟨c, by omega, fun _ _ h => h, ?_⟩
          intro a ha b hb hza _ u hu v hv h1 h2
          simp only [List.mem_singleton] at ha hb
          rw [ha] at hza h1
          rw [hb] at h2
          exact hgood a0 hza u hu v hv h1 h2
        | [a0, b0] =>
          by_cases hT : (∃ ra ∈ D, (gs.foldl step (xe n ra)).getD a0 false = true) ∧
              (∃ rb ∈ D, (gs.foldl step (xe n rb)).getD b0 false = true)
          · obtain ⟨⟨ra, hra, hta⟩, ⟨rb, hrb, htb⟩⟩ := hT
            refine ⟨fun i => if c i = c rb then c ra else c i, card_merge D c (c ra) (c rb),
              fun u v h => by simp only [h], ?_⟩
            intro a ha b hb hza hzb u hu v hv h1 h2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
            show (if c u = c rb then c ra else c u) = (if c v = c rb then c ra else c v)
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha] at hza h1 <;>
              rw [hb] at hzb h2
            · rw [hgood a0 hza u hu v hv h1 h2]
            · rw [hgood a0 hza u hu ra hra h1 hta, hgood b0 hzb v hv rb hrb h2 htb]
              simp
            · rw [hgood b0 hza u hu rb hrb h1 htb, hgood a0 hzb v hv ra hra h2 hta]
              simp
            · rw [hgood b0 hza u hu v hv h1 h2]
          · refine ⟨c, by omega, fun _ _ h => h, ?_⟩
            intro a ha b hb hza hzb u hu v hv h1 h2
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha] at hza h1 <;>
              rw [hb] at hzb h2
            · exact hgood a0 hza u hu v hv h1 h2
            · exact absurd ⟨⟨u, hu, h1⟩, ⟨v, hv, h2⟩⟩ hT
            · exact absurd ⟨⟨v, hv, h2⟩, ⟨u, hu, h1⟩⟩ hT
            · exact hgood b0 hza u hu v hv h1 h2
        | _ :: _ :: _ :: _ =>
          rw [hins] at hl
          simp at hl
      obtain ⟨c', hc'count, hc'old, hc'new⟩ := hpair
      refine ⟨c', ?_, ?_⟩
      · have := orPos_snoc_or gs g hor
        omega
      · intro w hz u hu v hv h1 h2
        rw [hval0] at hz
        rw [hvalU] at h1 h2
        split_ifs at hz h1 h2 with hw hw'
        · exact hc'old u v (hgood w hz u hu v hv h1 h2)
        · rw [hor] at hz h1 h2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false,
            Function.comp_apply, id] at hz h1 h2
          obtain ⟨a, ha, h1a⟩ := h1
          obtain ⟨b, hb, h2b⟩ := h2
          exact hc'new a ha b hb (by simpa using hz a ha) (by simpa using hz b hb)
            u hu v hv h1a h2b

end PEqualNP.Outside.L601

theorem PEqualNP.Outside.L_meta_601 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (D : Finset (Fin n)) (A : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → C.eval (List.ofFn (fun _ : Fin n => false)) = false → (∀ u ∈ D, C.eval (List.ofFn (fun w : Fin n => decide (w = u))) = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → D.card ≤ A.card + 1 := by
  intro n C D A hmono h0 hD hA
  obtain ⟨c, hcount, hgood⟩ := PEqualNP.Outside.L601.main n D C.gates hmono
  have hall : ∀ u ∈ D, ∀ v ∈ D, c u = c v := by
    intro u hu v hv
    exact hgood C.output h0 u hu v hv (hD u hu) (hD v hv)
  have h1 : (D.image c).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hb
    exact hall u hu v hv
  have h2 : (PEqualNP.Outside.L601.orPos C.gates).card ≤ A.card := by
    apply Finset.card_le_card
    intro j hj
    simp only [PEqualNP.Outside.L601.orPos, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨-, g, hg, hop⟩ := hj
    exact hA j g hg hop
  omega
