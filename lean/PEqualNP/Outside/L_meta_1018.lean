import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Induction
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1018_aux

open PEqualNP.CircuitLowerBounds

private def runStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) : Bool :=
  (gs.foldl runStep (List.ofFn x)).getD j false

private theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl runStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, runStep]; omega

private theorem val_empty {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i,h⟩ else false := by
  unfold val
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

private theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j) else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, runStep]
  have hn : (gs.foldl runStep (List.ofFn x)).length = n + gs.length := by simp [run_length]
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right h.ne, List.getD_append _ _ _ _ (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hn, h]
  · rw [ite_eq_right (by omega)]
    have hL : (gs.foldl runStep (List.ofFn x) ++
      [g.op.eval (List.map (fun i => (gs.foldl runStep (List.ofFn x)).getD i false) g.inputs)]).length ≤ i := by
      simp [hn]
      omega
    rw [List.getD_eq_default _ _ hL, List.getD_eq_default _ _ (by omega)]

private def arms (g : Gate) : ℕ × ℕ :=
  match g.inputs with
  | a :: b :: _ => (a,b)
  | [a] => (a,a)
  | [] => (0,0)

private theorem mem_arms (g : Gate) (h : g.inputs.length ≤ 2) {j : ℕ} (hj : j ∈ g.inputs) :
    j = (arms g).1 ∨ j = (arms g).2 := by
  unfold arms
  match g.inputs, h, hj with
  | [], _, hj => simp at hj
  | [a], _, hj => simpa using hj
  | [a,b], _, hj => simpa using hj
  | _ :: _ :: _ :: _, h, _ => simp at h

private theorem arms_exact (g : Gate) (h : g.inputs.length ≤ 2)
    (hne : (arms g).1 ≠ (arms g).2) : g.inputs = [(arms g).1, (arms g).2] := by
  unfold arms at hne ⊢
  match g.inputs, h, hne with
  | [], _, hne => exact (hne rfl).elim
  | [a], _, hne => exact (hne rfl).elim
  | [a,b], _, _ => rfl
  | _ :: _ :: _ :: _, h, _ => simp at h

private def merge (a b l : ℕ) : ℕ := if l = b then a else l

-- Each binary gate can merge at most two existing components.
private def labelStep (n : ℕ) (state : ℕ × (ℕ → ℕ)) (g : Gate) : ℕ × (ℕ → ℕ) :=
  let a := state.2 (arms g).1
  let b := state.2 (arms g).2
  (state.1 + 1, fun w => if w = n + state.1 then a else merge a b (state.2 w))

private def labels (n : ℕ) (gs : List Gate) : ℕ → ℕ :=
  (gs.foldl (labelStep n) (0, id)).2

private theorem fold_label_index (n : ℕ) (gs : List Gate) (state : ℕ × (ℕ → ℕ)) :
    (gs.foldl (labelStep n) state).1 = state.1 + gs.length := by
  induction gs generalizing state with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, labelStep]; omega

private theorem labels_snoc (n : ℕ) (gs : List Gate) (g : Gate) (w : ℕ) :
    labels n (gs ++ [g]) w =
      if w = n + gs.length then labels n gs (arms g).1
      else merge (labels n gs (arms g).1) (labels n gs (arms g).2) (labels n gs w) := by
  unfold labels
  rw [List.foldl_append]
  simp [labelStep, fold_label_index]

private def classes {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  S.image (fun v => labels n gs v.val)

private theorem classes_snoc {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    classes S (gs ++ [g]) =
      (classes S gs).image (merge (labels n gs (arms g).1) (labels n gs (arms g).2)) := by
  unfold classes
  rw [Finset.image_image]
  apply Finset.image_congr
  intro v _
  change labels n (gs ++ [g]) v.val =
    merge (labels n gs (arms g).1) (labels n gs (arms g).2) (labels n gs v.val)
  rw [labels_snoc, ite_eq_right (by omega)]

private theorem classes_empty {n : ℕ} (S : Finset (Fin n)) :
    (classes S []).card = S.card :=
  Finset.card_image_of_injective _ Fin.val_injective

private theorem merge_drop (P : Finset ℕ) (a b : ℕ) :
    P.card ≤ (P.image (merge a b)).card + 1 := by
  have sub : P ⊆ insert b (P.image (merge a b)) := by
    intro u hu
    by_cases h : u = b
    · simp [h]
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, hu, by simp [merge, h]⟩)
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le ..)

private theorem class_bound {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) :
    S.card ≤ (classes S gs).card + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [classes_empty]
  | append_singleton gs g ih =>
    rw [classes_snoc]
    have h := merge_drop (classes S gs) (labels n gs (arms g).1) (labels n gs (arms g).2)
    simp at ⊢
    omega

private theorem drop_means_both {P : Finset ℕ} {a b : ℕ}
    (h : (P.image (merge a b)).card < P.card) : a ∈ P ∧ b ∈ P ∧ a ≠ b := by
  have hni := Finset.not_injOn_of_card_image_lt h
  unfold Set.InjOn at hni
  push Not at hni
  obtain ⟨u, hu, v, hv, he, hne⟩ := hni
  by_cases huB : u = b <;> by_cases hvB : v = b
  · exact (hne (huB.trans hvB.symm)).elim
  · have hvA : v = a := by simpa [merge,huB,hvB] using he.symm
    exact ⟨hvA ▸ hv, huB ▸ hu, fun h => hvB (hvA.trans h)⟩
  · have huA : u = a := by simpa [merge,huB,hvB] using he
    exact ⟨huA ▸ hu, hvB ▸ hv, fun h => huB (huA.trans h)⟩
  · exact (hne (by simpa [merge,huB,hvB] using he)).elim

private def Depends {n : ℕ} (gs : List Gate) (i : ℕ) (v : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ w, w ≠ v → x w = y w) ∧ val gs x i ≠ val gs y i

private theorem labels_depends {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (i : ℕ) (v : Fin n)
    (h : Depends gs i v) : labels n gs i = labels n gs v.val := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    obtain ⟨x,y,hxy,hne⟩ := h
    rw [val_empty, val_empty] at hne
    by_cases hi : i < n
    · simp only [hi, dite_true] at hne
      have hv : (⟨i,hi⟩ : Fin n) = v := by
        by_contra hh
        exact hne (hxy _ hh)
      exact congrArg Fin.val hv
    · simp [hi] at hne
  | append_singleton gs g ih =>
    have hgp : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hg a (by simp [ha])
    have hg1 := hg g (by simp)
    obtain ⟨x,y,hxy,hne⟩ := h
    rw [val_snoc, val_snoc] at hne
    rw [labels_snoc, labels_snoc, ite_eq_right (by omega : v.val ≠ n + gs.length)]
    by_cases hi : i = n + gs.length
    · simp only [hi, ite_true] at hne ⊢
      have hd : val gs x (arms g).1 ≠ val gs y (arms g).1 ∨
          val gs x (arms g).2 ≠ val gs y (arms g).2 := by
        by_contra! hh
        apply hne
        congr 1
        apply List.map_congr_left
        intro j hj
        rcases mem_arms g hg1 hj with rfl | rfl
        · exact hh.1
        · exact hh.2
      rcases hd with hd|hd
      · rw [← ih hgp (arms g).1 ⟨x,y,hxy,hd⟩]
        simp [merge]
      · rw [← ih hgp (arms g).2 ⟨x,y,hxy,hd⟩]
        simp [merge]
    · simp only [hi, ite_false] at hne ⊢
      rw [ih hgp i ⟨x,y,hxy,hne⟩]

private theorem tight_step {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate)
    (ht : S.card = (classes S (gs ++ [g])).card + (gs ++ [g]).length) :
    let a := labels n gs (arms g).1
    let b := labels n gs (arms g).2
    S.card = (classes S gs).card + gs.length ∧
    a ∈ classes S gs ∧ b ∈ classes S gs ∧ a ≠ b := by
  dsimp only
  have h := class_bound S gs
  have hm := merge_drop (classes S gs) (labels n gs (arms g).1) (labels n gs (arms g).2)
  rw [classes_snoc] at ht
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at ht
  have hd : ((classes S gs).image (merge (labels n gs (arms g).1) (labels n gs (arms g).2))).card <
      (classes S gs).card := by
    have hs : ((classes S gs).image (merge (labels n gs (arms g).1) (labels n gs (arms g).2))).card ≤
        (classes S gs).card := Finset.card_image_le
    omega
  exact ⟨by omega, drop_means_both hd⟩

private def TrueOn {n : ℕ} (x : Fin n → Bool) (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, x i = true

-- A certificate records input points, the AND gates joining them, and the support
-- that can be replaced by any other way of making a recorded gate fire.
private def Certificate {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (w : ℕ)
    (x : Fin n → Bool) (I : Finset (Fin n)) (Q : Finset ℕ) : Prop :=
  I.Nonempty ∧ I ⊆ S ∧ TrueOn x I ∧
  (∀ t ∈ I, labels n gs t.val = labels n gs w) ∧
  (∀ j ∈ Q, n ≤ j ∧ j < n + gs.length ∧ labels n gs j = labels n gs w) ∧
  I.card = Q.card + 1 ∧
  (∀ y, TrueOn y I → val gs y w = true) ∧
  (∀ j ∈ Q, ∃ J ⊆ I, 2 ≤ J.card ∧
    (∀ y, TrueOn y J → val gs y j = true) ∧
    (∀ y, TrueOn y (I \ J) → val gs y j = true → val gs y w = true))

private theorem label_old {n : ℕ} (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length) :
    labels n (gs ++ [g]) w =
      merge (labels n gs (arms g).1) (labels n gs (arms g).2) (labels n gs w) := by
  rw [labels_snoc, ite_eq_right hw.ne]

private theorem val_old {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n + gs.length) : val (gs ++ [g]) x w = val gs x w := by
  rw [val_snoc, ite_eq_right hw.ne]

private theorem val_true_range {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (h : val gs x w = true) : w < n + gs.length := by
  by_contra! hh
  unfold val at h
  rw [List.getD_eq_default _ _ (by simpa [run_length] using hh)] at h
  cases h

private theorem transfer_certificate {n : ℕ} {S : Finset (Fin n)} {gs : List Gate} {g : Gate}
    {x : Fin n → Bool} {i w : ℕ} {I : Finset (Fin n)} {Q : Finset ℕ}
    (cert : Certificate S gs i x I Q)
    (hLabel : labels n (gs ++ [g]) w =
      merge (labels n gs (arms g).1) (labels n gs (arms g).2) (labels n gs i))
    (hVal : ∀ y : Fin n → Bool, val gs y i = true → val (gs ++ [g]) y w = true) :
    Certificate S (gs ++ [g]) w x I Q := by
  obtain ⟨hne, hsub, hx, hpoints, hgates, hcard, heval, hsubtree⟩ := cert
  refine ⟨hne, hsub, hx, ?_, ?_, hcard, fun y hy => hVal y (heval y hy), ?_⟩
  · intro t ht
    rw [label_old gs g _ (by omega : t.val < n + gs.length), hpoints t ht, hLabel]
  · intro j hj
    obtain ⟨hlo,hhi,hl⟩ := hgates j hj
    exact ⟨hlo, by simp; omega, by rw [label_old gs g _ hhi, hl, hLabel]⟩
  · intro j hj
    obtain ⟨J,hJI,hJC,hJ,hrest⟩ := hsubtree j hj
    have hhi := (hgates j hj).2.1
    refine ⟨J,hJI,hJC,?_,?_⟩
    · intro y hy
      rw [val_old gs g _ _ hhi]
      exact hJ y hy
    · intro y hy hjv
      rw [val_old gs g _ _ hhi] at hjv
      exact hVal y (hrest y hy hjv)

private theorem merged_mem_old {P : Finset ℕ} {a b t : ℕ} (ha : a ∈ P) (hb : b ∈ P)
    (h : merge a b t ∈ P.image (merge a b)) : t ∈ P := by
  by_cases ht : t = b
  · exact ht ▸ hb
  · obtain ⟨v,hv,hEq⟩ := Finset.mem_image.mp h
    rw [show merge a b t = t by simp [merge, ht]] at hEq
    by_cases h' : v = b
    · simp [merge,h'] at hEq
      exact hEq ▸ ha
    · simp [merge,h'] at hEq
      exact hEq ▸ hv

private theorem and_certificate {n : ℕ} {S : Finset (Fin n)} {gs : List Gate} {g : Gate}
    {x : Fin n → Bool} {I₁ I₂ : Finset (Fin n)} {Q₁ Q₂ : Finset ℕ}
    (hg : g.op = .and) (hi : g.inputs = [(arms g).1, (arms g).2])
    (hd : labels n gs (arms g).1 ≠ labels n gs (arms g).2)
    (h₁ : Certificate S gs (arms g).1 x I₁ Q₁) (h₂ : Certificate S gs (arms g).2 x I₂ Q₂) :
    Certificate S (gs ++ [g]) (n + gs.length) x (I₁ ∪ I₂) (insert (n + gs.length) (Q₁ ∪ Q₂)) := by
  obtain ⟨hn₁, hs₁, hx₁, hp₁, hq₁, hc₁, he₁, hr₁⟩ := h₁
  obtain ⟨hn₂, hs₂, hx₂, hp₂, hq₂, hc₂, he₂, hr₂⟩ := h₂
  have hI : Disjoint I₁ I₂ := Finset.disjoint_left.mpr (fun t h₁ h₂ => hd ((hp₁ t h₁).symm.trans (hp₂ t h₂)))
  have hQ : Disjoint Q₁ Q₂ := Finset.disjoint_left.mpr (fun t h₁ h₂ => hd ((hq₁ t h₁).2.2.symm.trans (hq₂ t h₂).2.2))
  have hdQ : n+gs.length ∉ Q₁ ∪ Q₂ := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact (Nat.lt_irrefl _ (hq₁ _ h).2.1)
    · exact (Nat.lt_irrefl _ (hq₂ _ h).2.1)
  have hLabels : labels n (gs ++ [g]) (n + gs.length) = labels n gs (arms g).1 := by
    rw [labels_snoc, ite_eq_left rfl]
  have hAnd (y : Fin n → Bool) (h₁ : val gs y (arms g).1 = true) (h₂ : val gs y (arms g).2 = true) :
      val (gs ++ [g]) y (n + gs.length) = true := by
    rw [val_snoc, ite_eq_left rfl, hg, hi]
    simp [GateOp.eval, h₁, h₂]
  have hWhole (y : Fin n → Bool) (hy : TrueOn y (I₁ ∪ I₂)) :
      val (gs ++ [g]) y (n+gs.length) = true :=
    hAnd y (he₁ y fun t ht => hy t (Finset.mem_union_left _ ht))
      (he₂ y fun t ht => hy t (Finset.mem_union_right _ ht))
  refine ⟨hn₁.mono Finset.subset_union_left, Finset.union_subset hs₁ hs₂, ?_, ?_, ?_, ?_, hWhole, ?_⟩
  · intro t ht
    exact (Finset.mem_union.mp ht).elim (hx₁ t) (hx₂ t)
  · intro t ht
    rw [label_old gs g _ (by omega : t.val < n+gs.length), hLabels]
    rcases Finset.mem_union.mp ht with ha|hb
    · rw [hp₁ t ha]
      simp [merge]
    · rw [hp₂ t hb]
      simp [merge]
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact ⟨by omega, by simp, rfl⟩
    · rcases Finset.mem_union.mp hj with hj|hj
      · obtain ⟨hl, hh, hLab⟩ := hq₁ j hj
        exact ⟨hl, by simp; omega, by rw [label_old gs g j hh, hLab, hLabels]; simp [merge]⟩
      · obtain ⟨hl, hh, hLab⟩ := hq₂ j hj
        exact ⟨hl, by simp; omega, by rw [label_old gs g j hh, hLab, hLabels]; simp [merge]⟩
  · rw [Finset.card_union_of_disjoint hI, Finset.card_insert_of_notMem hdQ, Finset.card_union_of_disjoint hQ]
    omega
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · have h2 : 2 ≤ (I₁ ∪ I₂).card := by
        rw [Finset.card_union_of_disjoint hI]
        have h₁ := Finset.card_pos.mpr hn₁
        have h₂ := Finset.card_pos.mpr hn₂
        omega
      exact ⟨I₁∪I₂,le_rfl,h2,hWhole,fun _ _ hy => hy⟩
    · rcases Finset.mem_union.mp hj with hj|hj
      · obtain ⟨J,hJ,hcard,hEval,hRest⟩ := hr₁ j hj
        have hdj := (hq₁ j hj).2.1
        refine ⟨J,hJ.trans Finset.subset_union_left,hcard,?_,?_⟩
        · intro y hy
          rw [val_old gs g _ _ hdj]
          exact hEval y hy
        · intro y hy hjv
          rw [val_old gs g _ _ hdj] at hjv
          apply hAnd y (hRest y (fun t ht => hy t (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp ht).1,(Finset.mem_sdiff.mp ht).2⟩)) hjv)
          exact he₂ y (fun t ht => hy t (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right _ ht, fun h => Finset.disjoint_left.mp hI (hJ h) ht⟩))
      · obtain ⟨J,hJ,hcard,hEval,hRest⟩ := hr₂ j hj
        have hdj := (hq₂ j hj).2.1
        refine ⟨J,hJ.trans Finset.subset_union_right,hcard,?_,?_⟩
        · intro y hy
          rw [val_old gs g _ _ hdj]
          exact hEval y hy
        · intro y hy hjv
          rw [val_old gs g _ _ hdj] at hjv
          apply hAnd y _ (hRest y (fun t ht => hy t (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp ht).1,(Finset.mem_sdiff.mp ht).2⟩)) hjv)
          exact he₁ y (fun t ht => hy t (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_left _ ht, fun h => Finset.disjoint_left.mp hI ht (hJ h)⟩))

private theorem makes_certificate {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (ht : S.card = (classes S gs).card + gs.length) (x : Fin n → Bool) (w : ℕ)
    (hw : labels n gs w ∈ classes S gs) (hv : val gs x w = true) :
    ∃ I Q, Certificate S gs w x I Q := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    have h : w ∈ S.image Fin.val := hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
    refine ⟨{t}, ∅, ?_⟩
    have he : ∀ y : Fin n → Bool, val [] y t.val = y t := by
      intro y
      simp [val_empty,t.isLt]
    simp only [Certificate, Finset.singleton_nonempty, Finset.singleton_subset_iff, ht, he,
      TrueOn, Finset.mem_singleton, Finset.notMem_empty, forall_eq, false_implies, implies_true,
      Finset.card_singleton, Finset.card_empty, zero_add, true_and, and_true]
    exact ⟨(he x) ▸ hv, fun _ hy => hy⟩
  | append_singleton gs g ih =>
    obtain ⟨hpre, ha, hb, hdiff⟩ := tight_step S gs g ht
    have hgp : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hg' := hg g (by simp)
    have him := arms_exact g hg'.2 (fun e => hdiff (congrArg (labels n gs) e))
    by_cases hnew : w = n+gs.length
    · subst w
      rw [val_snoc, ite_eq_left rfl, him] at hv
      rcases hg'.1 with hAnd|hOr
      · rw [hAnd] at hv
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
          Bool.and_true, Bool.and_eq_true] at hv
        obtain ⟨I₁,Q₁,h₁⟩ := ih hgp hpre (arms g).1 ha hv.1
        obtain ⟨I₂,Q₂,h₂⟩ := ih hgp hpre (arms g).2 hb hv.2
        exact ⟨_,_,and_certificate hAnd him hdiff h₁ h₂⟩
      · rw [hOr] at hv
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, Bool.or_eq_true] at hv
        rcases hv with hv|hv
        · obtain ⟨I,Q,hc⟩ := ih hgp hpre (arms g).1 ha hv
          refine ⟨I,Q,transfer_certificate hc ?_ ?_⟩
          · rw [labels_snoc, ite_eq_left rfl]; simp [merge]
          · intro y hy
            rw [val_snoc, ite_eq_left rfl, him, hOr]
            simp [GateOp.eval, hy]
        · obtain ⟨I,Q,hc⟩ := ih hgp hpre (arms g).2 hb hv
          refine ⟨I,Q,transfer_certificate hc ?_ ?_⟩
          · rw [labels_snoc, ite_eq_left rfl]; simp [merge]
          · intro y hy
            rw [val_snoc, ite_eq_left rfl, him, hOr]
            simp [GateOp.eval, hy]
    · rw [val_snoc, ite_eq_right hnew] at hv
      rw [classes_snoc, labels_snoc, ite_eq_right hnew] at hw
      obtain ⟨I,Q,hc⟩ := ih hgp hpre w (merged_mem_old ha hb hw) hv
      refine ⟨I,Q,transfer_certificate hc ?_ ?_⟩
      · rw [labels_snoc, ite_eq_right hnew]
      · intro y hy
        rw [val_snoc, ite_eq_right hnew]
        exact hy

private def line (i : Fin 3) : Finset (Fin 13) :=
  ({0,1,3,9} : Finset (Fin 13)).image (fun u => u + Fin.ofNat 13 i.val)

private def points : Finset (Fin 13) := Finset.univ.biUnion line

private def pad : Finset (Fin 13) := {6,7,8}

private def onSet (T : Finset (Fin 13)) (v : Fin 13) : Bool := decide (v ∈ T)

private def weight (x : Fin 13 → Bool) : ℕ :=
  (Finset.univ.filter (fun v : Fin 13 => x v = true)).card

private def anchor (i : Fin 3) : Fin 13 → Bool := onSet (line i ∪ pad)

private def removal (i : Fin 3) (t : Fin 13) : Fin 13 → Bool := onSet ((line i).erase t ∪ pad)

private theorem points_card : points.card = 9 := by decide

private theorem line_card : ∀ i : Fin 3, (line i).card = 4 := by decide

private theorem line_inter : ∀ i j : Fin 3, i ≠ j → ((line i) ∩ (line j)).card = 1 := by decide

private theorem meet : ∀ i j : Fin 3, ∃ t ∈ line i, t ∈ line j := by decide

private theorem pad_disj : Disjoint points pad := by decide

private theorem anchor_weight : ∀ i : Fin 3, weight (anchor i) = 7 := by decide

private theorem removal_weight : ∀ (i : Fin 3) (t : Fin 13), t ∈ line i → weight (removal i t) = 6 := by decide

private theorem line_in_points (i : Fin 3) : line i ⊆ points := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩

private theorem weight_on (T : Finset (Fin 13)) : weight (onSet T) = T.card := by
  unfold weight
  congr 1
  ext t
  simp [onSet]

private def RightOnBand (gs : List Gate) (out : Fin 3 → ℕ) : Prop :=
  ∀ (i : Fin 3) (x : Fin 13 → Bool), weight x = 6 ∨ weight x = 7 →
    val gs x (out i) = decide (∀ v ∈ line i, x v = true)

private theorem positive (gs : List Gate) (out : Fin 3 → ℕ)
    (hr : RightOnBand gs out) (i : Fin 3) : val gs (anchor i) (out i) = true := by
  rw [hr i _ (Or.inr (anchor_weight i)), decide_eq_true_eq]
  intro v hv
  exact decide_eq_true (Finset.mem_union_left _ hv)

private theorem negative (gs : List Gate) (out : Fin 3 → ℕ)
    (hr : RightOnBand gs out) (i : Fin 3) (t : Fin 13) (ht : t ∈ line i) :
    val gs (removal i t) (out i) = false := by
  rw [hr i _ (Or.inl (removal_weight i t ht))]
  apply Bool.eq_false_of_not_eq_true
  rw [decide_eq_true_eq]
  intro h
  have hm : t ∈ (line i).erase t ∪ pad := of_decide_eq_true (h t ht)
  rcases Finset.mem_union.mp hm with hm|hm
  · exact (Finset.mem_erase.mp hm).1 rfl
  · exact Finset.disjoint_left.mp pad_disj (line_in_points i ht) hm

private theorem line_depends (gs : List Gate) (out : Fin 3 → ℕ)
    (hr : RightOnBand gs out) (i : Fin 3) (t : Fin 13) (ht : t ∈ line i) :
    Depends gs (out i) t := by
  refine ⟨anchor i, removal i t, ?_, ?_⟩
  · intro a ha
    simp [anchor, removal, onSet, Finset.mem_erase, ha]
  · rw [positive gs out hr i, negative gs out hr i t ht]
    decide

private theorem points_one_component (gs : List Gate) (out : Fin 3 → ℕ)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) (hr : RightOnBand gs out) :
    classes points gs = {labels 13 gs (out 0)} := by
  have coincide (i : Fin 3) : labels 13 gs (out i) = labels 13 gs (out 0) := by
    obtain ⟨t,h₁,h₂⟩ := meet i 0
    exact (labels_depends gs hfan _ t (line_depends gs out hr i t h₁)).trans
      (labels_depends gs hfan _ t (line_depends gs out hr 0 t h₂)).symm
  ext l
  simp only [classes, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨i,_,hti⟩ := Finset.mem_biUnion.mp ht
    exact (labels_depends gs hfan _ t (line_depends gs out hr i t hti)).symm.trans (coincide i)
  · intro hl
    obtain ⟨t,ht,_⟩ := meet 0 0
    exact ⟨t,line_in_points 0 ht,(labels_depends gs hfan _ t (line_depends gs out hr 0 t ht)).symm.trans hl.symm⟩

private theorem line_certificate (gs : List Gate) (out : Fin 3 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hr : RightOnBand gs out) (ht : points.card = (classes points gs).card + gs.length) (i : Fin 3) :
    ∃ Q, Certificate points gs (out i) (anchor i) (line i) Q := by
  obtain ⟨t,htl,_⟩ := meet i i
  have hmem : labels 13 gs (out i) ∈ classes points gs := by
    unfold classes
    exact Finset.mem_image.mpr ⟨t,line_in_points i htl,
      (labels_depends gs (fun g hg' => (hg g hg').2) _ t (line_depends gs out hr i t htl)).symm⟩
  obtain ⟨I,Q,hcert⟩ := makes_certificate points gs hg ht (anchor i) (out i) hmem (positive gs out hr i)
  have eq : I = line i := by
    obtain ⟨_,hIP,hIa,_,_,_,heval,_⟩ := hcert
    apply Finset.Subset.antisymm
    · intro v hv
      have h : v ∈ line i ∪ pad := of_decide_eq_true (hIa v hv)
      exact (Finset.mem_union.mp h).elim id (fun h => (Finset.disjoint_left.mp pad_disj (hIP hv) h).elim)
    · intro v hv
      by_contra hh
      have hAll : TrueOn (removal i v) I := by
        intro a ha
        have ha' : a ∈ line i ∪ pad := of_decide_eq_true (hIa a ha)
        rcases Finset.mem_union.mp ha' with hla|hpa
        · exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hh (e ▸ ha),hla⟩))
        · exact decide_eq_true (Finset.mem_union_right _ hpa)
      have ht := heval _ hAll
      rw [negative gs out hr i v hv] at ht
      cases ht
  exact ⟨Q,eq ▸ hcert⟩

-- Substituting the smaller support preserves the output but loses a point on its line.
private theorem cannot_exchange (gs : List Gate) (out : Fin 3 → ℕ)
    (hr : RightOnBand gs out) {i j : Fin 3} (hij : i ≠ j) {I J : Finset (Fin 13)}
    (hi : I ⊆ line i) (hj : J ⊆ line j) (hI : 2 ≤ I.card) (hJ : J.card ≤ I.card)
    (w : ℕ) (hfill : ∀ x, TrueOn x J → val gs x w = true)
    (hrest : ∀ x, TrueOn x (line i \ I) → val gs x w = true → val gs x (out i) = true) : False := by
  have hnot : ¬ I ⊆ J := by
    intro hsub
    have hincl : I ⊆ line i ∩ line j := fun _ hv => Finset.mem_inter.mpr ⟨hi hv,hj (hsub hv)⟩
    have h := Finset.card_le_card hincl
    rw [line_inter i j hij] at h
    omega
  obtain ⟨t,ht,hne⟩ := Finset.not_subset.mp hnot
  let W := line i \ I ∪ J
  have hwcard : W.card ≤ 6 := by
    have h := Finset.card_union_le (line i \ I) J
    rw [Finset.card_sdiff_of_subset hi, line_card] at h
    have hle : I.card ≤ 4 := by simpa only [line_card] using Finset.card_le_card hi
    change W.card ≤ 6
    dsimp [W]
    omega
  have hwsub : W ⊆ (Finset.univ : Finset (Fin 13)).erase t := by
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro e
    subst v
    rcases Finset.mem_union.mp hv with h|h
    · exact (Finset.mem_sdiff.mp h).2 ht
    · exact hne h
  have he : 6 ≤ ((Finset.univ : Finset (Fin 13)).erase t).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ t)]
    decide
  obtain ⟨T,hWT,hTe,hT⟩ := Finset.exists_subsuperset_card_eq hwsub hwcard he
  have hout : val gs (onSet T) (out i) = true := by
    apply hrest _ (fun a ha => decide_eq_true (hWT (Finset.mem_union_left _ ha)))
    exact hfill _ (fun a ha => decide_eq_true (hWT (Finset.mem_union_right _ ha)))
  rw [hr i _ (Or.inl ((weight_on T).trans hT)), decide_eq_true_eq] at hout
  have hf := of_decide_eq_true (hout t (hi ht))
  exact (Finset.mem_erase.mp (hTe hf)).1 rfl

private theorem certificates_disjoint (gs : List Gate) (out : Fin 3 → ℕ)
    (hr : RightOnBand gs out) {i j : Fin 3} (hij : i ≠ j) {Q R : Finset ℕ}
    (hQ : Certificate points gs (out i) (anchor i) (line i) Q)
    (hR : Certificate points gs (out j) (anchor j) (line j) R) : Disjoint Q R := by
  obtain ⟨_,_,_,_,_,_,_,heQ⟩ := hQ
  obtain ⟨_,_,_,_,_,_,_,heR⟩ := hR
  apply Finset.disjoint_left.mpr
  intro w hqw hrw
  obtain ⟨I,hI,hIcard,hIval,hIrest⟩ := heQ _ hqw
  obtain ⟨J,hJ,hJcard,hJval,hJrest⟩ := heR _ hrw
  rcases le_total J.card I.card with h|h
  · exact cannot_exchange gs out hr hij hI hJ hIcard h w hJval hIrest
  · exact cannot_exchange gs out hr hij.symm hJ hI hJcard h w hIval hJrest

private theorem triangle_lower (gs : List Gate) (out : Fin 3 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hr : RightOnBand gs out) : 9 ≤ gs.length := by
  classical
  by_contra! hs
  have hclasses := points_one_component gs out (fun g hm => (hg g hm).2) hr
  have hb := class_bound points gs
  rw [points_card, hclasses, Finset.card_singleton] at hb
  have he : points.card = (classes points gs).card + gs.length := by
    rw [points_card, hclasses, Finset.card_singleton]
    omega
  choose Q hQ using line_certificate gs out hg hr he
  have hdisj : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint Q := by
    intro i _ j _ hij
    exact certificates_disjoint gs out hr hij (hQ i) (hQ j)
  have hsub : Finset.univ.biUnion Q ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro w hw
    obtain ⟨i,_,hwi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨_,_,_,_,hrange,_,_,_⟩ := hQ i
    exact Finset.mem_Ico.mpr ⟨(hrange w hwi).1,(hrange w hwi).2.1⟩
  have hcard (i : Fin 3) : (Q i).card = 3 := by
    obtain ⟨_,_,_,_,_,hc,_,_⟩ := hQ i
    rw [line_card] at hc
    omega
  have h := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Nat.card_Ico, Nat.add_sub_cancel_left] at h
  simp [hcard] at h
  omega

end PEqualNP.Outside.L_meta_1018_aux

open PEqualNP.Outside.L_meta_1018_aux in
theorem PEqualNP.Outside.L_meta_1018 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 3 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin 13 → Bool, ((Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 6 ∨ (Finset.univ.filter (fun i : Fin 13 => x i = true)).card = 7) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 0⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 0)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 1⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 1)), x v = true) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out 2⟩ (List.ofFn x) = decide (∀ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + 2)), x v = true)) → 9 ≤ gates.length := by
  intro gates out hg hr
  apply triangle_lower gates out hg
  intro i x hx
  have h := hr x hx
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2
