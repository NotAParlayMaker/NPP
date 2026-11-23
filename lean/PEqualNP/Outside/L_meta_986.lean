import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import PEqualNP.Defs

-- Mythos 6 et Codex Betelgeuse

namespace PEqualNP.Outside.L_meta_986_aux

open scoped BigOperators

lemma charge_unique {α : Type*} [DecidableEq α]
    (S U P : Finset α) (t : α)
    (hlin : (S ∩ U).card ≤ 1)
    (hS : P.erase t ⊆ S) (hU : P.erase t ⊆ U)
    (hcS : 2 ≤ (P ∩ S).card) (hcU : 2 ≤ (P ∩ U).card) : False := by
  have htU : t ∈ U := by
    by_contra hn
    have hs : P ∩ U ⊆ S ∩ U := by
      intro a ha
      obtain ⟨haP, haU⟩ := Finset.mem_inter.mp ha
      have hat : a ≠ t := by
        intro he
        subst a
        exact hn haU
      exact Finset.mem_inter.mpr ⟨hS (Finset.mem_erase.mpr ⟨hat, haP⟩), haU⟩
    have hh := Finset.card_le_card hs
    omega
  have hs : P ∩ S ⊆ S ∩ U := by
    intro a ha
    obtain ⟨haP, haS⟩ := Finset.mem_inter.mp ha
    refine Finset.mem_inter.mpr ⟨haS, ?_⟩
    by_cases hat : a = t
    · simpa [hat] using htU
    · exact hU (Finset.mem_erase.mpr ⟨hat, haP⟩)
  have hh := Finset.card_le_card hs
  omega

lemma residual_card {α : Type*} [DecidableEq α] (S A : Finset α) :
    S.card - 1 ≤ (S \ A).card - 1 + (S ∩ A).card := by
  have h := Finset.card_sdiff_add_card_inter S A
  omega

lemma incidence_sum {α ι : Type*} [DecidableEq α] [Fintype ι]
    (S : ι → Finset α) (A : Finset α) :
    ∑ i, (S i ∩ A).card =
      ∑ u ∈ A, (Finset.univ.filter (fun i => u ∈ S i)).card := by
  classical
  calc
    ∑ i, (S i ∩ A).card = ∑ i, ∑ u ∈ A, if u ∈ S i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp [Finset.filter_mem_eq_inter, Finset.inter_comm]
    _ = ∑ u ∈ A, ∑ i, if u ∈ S i then 1 else 0 := Finset.sum_comm
    _ = ∑ u ∈ A, (Finset.univ.filter (fun i => u ∈ S i)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.sum_filter]
      simp

lemma finish_from_residual {α ι : Type*} [DecidableEq α] [Fintype ι]
    (S : ι → Finset α) (A : Finset α) (G : ℕ)
    (h : 1 + ∑ i, ((S i \ A).card - 1) ≤ G) :
    1 + ∑ i, ((S i).card - 1) ≤
      G + ∑ u ∈ A, (Finset.univ.filter (fun i => u ∈ S i)).card := by
  classical
  have hb : ∑ i, ((S i).card - 1) ≤
      (∑ i, ((S i \ A).card - 1)) + ∑ i, (S i ∩ A).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => residual_card (S i) A)
  rw [incidence_sum S A] at hb
  omega

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

def Collapsed {α β : Type*} (f : α → β) (Q : Finset α) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, f x = f y

lemma collapsed_subset {α β : Type*} {f : α → β} {A B : Finset α}
    (h : Collapsed f B) (hAB : A ⊆ B) : Collapsed f A := by
  intro x hx y hy
  exact h x (hAB hx) y (hAB hy)

lemma collapsed_comp {α β γ : Type*} {f : α → β} {Q : Finset α}
    (h : Collapsed f Q) (g : β → γ) : Collapsed (g ∘ f) Q := by
  intro x hx y hy
  exact congrArg g (h x hx y hy)

lemma collapsed_small {α β : Type*} {f : α → β} {Q : Finset α}
    (h : Q.card ≤ 1) : Collapsed f Q := by
  intro x hx y hy
  exact congrArg f (Finset.card_le_one.mp h x hx y hy)

lemma collapsed_iff_image {α β : Type*} [DecidableEq β]
    (f : α → β) (Q : Finset α) : Collapsed f Q ↔ (Q.image f).card ≤ 1 := by
  rw [Finset.card_le_one]
  constructor
  · intro h x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact h a ha b hb
  · intro h x hx y hy
    exact h (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (f y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

def mergeLabel {α : Type*} [DecidableEq α] (a b x : α) : α :=
  if x = b then a else x

lemma merge_image {α : Type*} [DecidableEq α] (C : Finset α) (a b : α)
    (ha : a ∈ C) (hab : a ≠ b) :
    C.image (mergeLabel a b) = C.erase b := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    by_cases he : y = b
    · simpa [mergeLabel, he] using (Finset.mem_erase.mpr ⟨hab, ha⟩)
    · simpa [mergeLabel, he] using (Finset.mem_erase.mpr ⟨he, hy⟩)
  · intro hx
    obtain ⟨hne, hc⟩ := Finset.mem_erase.mp hx
    exact Finset.mem_image.mpr ⟨x, hc, by simp [mergeLabel, hne]⟩

lemma merge_binary {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R A B Q : Finset α) (f : α → β)
    (hAR : A ⊆ R) (hBR : B ⊆ R) (hQ : Q ⊆ A ∪ B)
    (hA : Collapsed f A) (hB : Collapsed f B) (hn : ¬ Collapsed f Q) :
    ∃ g : β → β, Collapsed (g ∘ f) Q ∧
      (R.image (g ∘ f)).card + 1 = (R.image f).card := by
  have hAn : A.Nonempty := by
    by_contra he
    have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    exact hn (collapsed_subset hB (by simpa [he] using hQ))
  have hBn : B.Nonempty := by
    by_contra he
    have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    exact hn (collapsed_subset hA (by simpa [he] using hQ))
  obtain ⟨a, ha⟩ := hAn
  obtain ⟨b, hb⟩ := hBn
  have hvalues : ∀ x ∈ Q, f x = f a ∨ f x = f b := by
    intro x hx
    rcases Finset.mem_union.mp (hQ hx) with h | h
    · exact Or.inl (hA x h a ha)
    · exact Or.inr (hB x h b hb)
  have hab : f a ≠ f b := by
    intro he
    apply hn
    intro x hx y hy
    rcases hvalues x hx with h | h <;>
      rcases hvalues y hy with h' | h' <;> exact h.trans (by simpa [he] using h'.symm)
  refine ⟨mergeLabel (f a) (f b), ?_, ?_⟩
  · have hall : ∀ x ∈ Q, mergeLabel (f a) (f b) (f x) = f a := by
      intro x hx
      rcases hvalues x hx with h | h
      · simp [mergeLabel, h, hab]
      · simp [mergeLabel, h]
    intro x hx y hy
    exact (hall x hx).trans (hall y hy).symm
  · rw [← Finset.image_image, merge_image _ _ _
        (Finset.mem_image.mpr ⟨a, hAR ha, rfl⟩) hab]
    exact Finset.card_erase_add_one (Finset.mem_image.mpr ⟨b, hBR hb, rfl⟩)

lemma prefix_marks {α : Type*} [DecidableEq α]
    (R : Finset α) (n G : ℕ) (Q : ℕ → Finset α) (allowed : ℕ → Prop)
    (hR : ∀ w < n + G, Q w ⊆ R)
    (hinput : ∀ w < n, (Q w).card ≤ 1)
    (hstep : ∀ j < G,
      (Q (n + j)).card ≤ 1 ∨
      (∃ a < n + j, Q (n + j) ⊆ Q a) ∨
      (allowed j ∧ ∃ a < n + j, ∃ b < n + j, Q (n + j) ⊆ Q a ∪ Q b)) :
    ∀ k ≤ G, ∃ (f : α → α) (M : Finset ℕ),
      (R.image f).card + M.card = R.card ∧
      (∀ w < n + k, Collapsed f (Q w)) ∧
      (∀ j ∈ M, j < k ∧ allowed j ∧ 2 ≤ (Q (n + j)).card) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, ∅, by simp, ?_, by simp⟩
    intro w hw
    exact collapsed_small (hinput w (by simpa using hw))
  | succ k ih =>
    intro hk
    obtain ⟨f, M, hcount, hcollapsed, hmarks⟩ := ih (by omega)
    by_cases hc : Collapsed f (Q (n + k))
    · refine ⟨f, M, hcount, ?_, ?_⟩
      · intro w hw
        by_cases he : w = n + k
        · simpa [he] using hc
        · exact hcollapsed w (by omega)
      · intro j hj
        obtain ⟨hjlt, hjallowed, hjcard⟩ := hmarks j hj
        exact ⟨by omega, hjallowed, hjcard⟩
    · have hlarge : 2 ≤ (Q (n + k)).card := by
        by_contra hh
        exact hc (collapsed_small (by omega))
      rcases hstep k (by omega) with hsmall | hcopy | ⟨hok, a, ha, b, hb, hbinary⟩
      · exact False.elim (hc (collapsed_small hsmall))
      · obtain ⟨a, ha, hsub⟩ := hcopy
        exact False.elim (hc (collapsed_subset (hcollapsed a ha) hsub))
      · obtain ⟨g, hg, hdrop⟩ := merge_binary R (Q a) (Q b) (Q (n + k)) f
          (hR a (by omega)) (hR b (by omega)) hbinary
          (hcollapsed a ha) (hcollapsed b hb) hc
        have hkm : k ∉ M := by
          intro h
          have := (hmarks k h).1
          omega
        refine ⟨g ∘ f, insert k M, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hkm]
          omega
        · intro w hw
          by_cases he : w = n + k
          · simpa [he] using hg
          · exact collapsed_comp (hcollapsed w (by omega)) g
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact ⟨by omega, hok, hlarge⟩
          · obtain ⟨hjlt, hjallowed, hjcard⟩ := hmarks j hj
            exact ⟨by omega, hjallowed, hjcard⟩

lemma mark_support_trace {α : Type*} [DecidableEq α]
    (R : Finset α) (n G : ℕ) (Q : ℕ → Finset α) (allowed : ℕ → Prop)
    (hR : ∀ w < n + G, Q w ⊆ R)
    (hinput : ∀ w < n, (Q w).card ≤ 1)
    (hstep : ∀ j < G,
      (Q (n + j)).card ≤ 1 ∨
      (∃ a < n + j, Q (n + j) ⊆ Q a) ∨
      (allowed j ∧ ∃ a < n + j, ∃ b < n + j, Q (n + j) ⊆ Q a ∪ Q b))
    (houtput : R = ∅ ∨ ∃ w < n + G, Q w = R) :
    ∃ M : Finset ℕ, M.card = R.card - 1 ∧
      ∀ j ∈ M, j < G ∧ allowed j ∧ 2 ≤ (Q (n + j)).card := by
  classical
  obtain ⟨f, M, hcount, hcollapsed, hmarks⟩ :=
    prefix_marks R n G Q allowed hR hinput hstep G le_rfl
  refine ⟨M, ?_, hmarks⟩
  by_cases hzero : R = ∅
  · simpa [hzero] using hcount
  · have hc : Collapsed f R := by
      rcases houtput with he | ⟨w, hw, he⟩
      · exact False.elim (hzero he)
      · simpa [he] using hcollapsed w hw
    have hle := (collapsed_iff_image f R).mp hc
    have hpos : 0 < (R.image f).card := by
      apply Finset.card_pos.mpr
      exact (Finset.nonempty_iff_ne_empty.mpr hzero).image f
    omega

lemma mark_support_trace_fin {α : Type*} [DecidableEq α]
    (R : Finset α) (n G : ℕ) (Q : ℕ → Finset α) (allowed : ℕ → Prop)
    (hR : ∀ w < n + G, Q w ⊆ R)
    (hinput : ∀ w < n, (Q w).card ≤ 1)
    (hstep : ∀ j < G,
      (Q (n + j)).card ≤ 1 ∨
      (∃ a < n + j, Q (n + j) ⊆ Q a) ∨
      (allowed j ∧ ∃ a < n + j, ∃ b < n + j, Q (n + j) ⊆ Q a ∪ Q b))
    (houtput : R = ∅ ∨ ∃ w < n + G, Q w = R) :
    ∃ M : Finset (Fin G), M.card = R.card - 1 ∧
      ∀ j ∈ M, allowed j.val ∧ 2 ≤ (Q (n + j.val)).card := by
  classical
  obtain ⟨M, hc, hm⟩ := mark_support_trace R n G Q allowed hR hinput hstep houtput
  let lift : {j // j ∈ M} → Fin G := fun j => ⟨j.val, (hm j.val j.property).1⟩
  have hinj : Function.Injective lift := by
    intro a b he
    apply Subtype.ext
    exact congrArg Fin.val he
  refine ⟨M.attach.image lift, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hc]
  · intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact (hm k.val k.property).2

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

def singletonInput {α : Type*} [DecidableEq α] (v : α) : α → Bool :=
  fun u => decide (u = v)

def backgroundInput {α : Type*} [DecidableEq α] (S T : Finset α) : α → Bool :=
  fun u => decide (u ∉ T ∧ u ∉ S)

def singletonSupport {α : Type*} [DecidableEq α] [Fintype α]
    (A : Finset α) (f : (α → Bool) → Bool) : Finset α :=
  Finset.univ.filter (fun v => v ∉ A ∧ f (singletonInput v) = true)

lemma support_erased_subset {α : Type*} [DecidableEq α] [Fintype α]
    (S T : Finset α) (t : α) (f : (α → Bool) → Bool)
    (hf : f (backgroundInput S T) = false)
    (hmono : ∀ x y : α → Bool,
      (∀ u ∈ T, x u = false) → (∀ u ∈ T, y u = false) →
      (∀ u, x u = true → y u = true) → f x = true → f y = true) :
    (singletonSupport (T.erase t) f).erase t ⊆ S \ T.erase t := by
  intro v hv
  obtain ⟨hvt, hv⟩ := Finset.mem_erase.mp hv
  obtain ⟨_, hnotA, hfv⟩ := Finset.mem_filter.mp hv
  have hnotT : v ∉ T := by
    intro h
    exact hnotA (Finset.mem_erase.mpr ⟨hvt, h⟩)
  have hvS : v ∈ S := by
    by_contra hnotS
    have hs : ∀ u ∈ T, singletonInput v u = false := by
      intro u hu
      have hne : u ≠ v := by
        intro he
        exact hnotT (he ▸ hu)
      simp [singletonInput, hne]
    have hb : ∀ u ∈ T, backgroundInput S T u = false := by
      intro u hu
      simp [backgroundInput, hu]
    have hle : ∀ u, singletonInput v u = true → backgroundInput S T u = true := by
      intro u hu
      have he : u = v := by simpa [singletonInput] using hu
      subst u
      simp [backgroundInput, hnotT, hnotS]
    have htrue := hmono (singletonInput v) (backgroundInput S T) hs hb hle hfv
    simp [hf] at htrue
  exact Finset.mem_sdiff.mpr ⟨hvS, hnotA⟩

lemma support_of_sum {α : Type*} [DecidableEq α] [Fintype α]
    (S A : Finset α) (f : (α → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ v ∈ S, x v = true)) :
    singletonSupport A f = S \ A := by
  ext v
  simp [singletonSupport, hf, singletonInput, and_comm]

lemma background_sum_false {α : Type*} [DecidableEq α]
    (S T : Finset α) (f : (α → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ v ∈ S, x v = true)) :
    f (backgroundInput S T) = false := by
  rw [hf]
  simp only [decide_eq_false_iff_not, not_exists, not_and]
  intro v hv
  simp [backgroundInput, hv]

def falseSupport {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (f : (α → Bool) → Bool) (z : α → Bool) : Finset α :=
  if f z = false then singletonSupport A f ∩ R else ∅

lemma falseSupport_false {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (z : α → Bool) :
    falseSupport R A (fun _ => false) z = ∅ := by
  simp [falseSupport, singletonSupport]

lemma falseSupport_true {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (z : α → Bool) :
    falseSupport R A (fun _ => true) z = ∅ := by
  simp [falseSupport]

lemma falseSupport_and {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (f g : (α → Bool) → Bool) (z : α → Bool) :
    falseSupport R A (fun x => f x && g x) z ⊆ falseSupport R A f z ∨
    falseSupport R A (fun x => f x && g x) z ⊆ falseSupport R A g z := by
  cases hf : f z
  · left
    intro v hv
    simp only [falseSupport, hf, Bool.false_and, ↓reduceIte, Finset.mem_inter,
      singletonSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.and_eq_true] at hv ⊢
    exact ⟨⟨hv.1.1, hv.1.2.1⟩, hv.2⟩
  · right
    cases hg : g z
    · intro v hv
      simp only [falseSupport, hf, hg, Bool.true_and, ↓reduceIte, Finset.mem_inter,
        singletonSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.and_eq_true] at hv ⊢
      exact ⟨⟨hv.1.1, hv.1.2.2⟩, hv.2⟩
    · simp [falseSupport, hf, hg]

lemma falseSupport_or {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (f g : (α → Bool) → Bool) (z : α → Bool) :
    falseSupport R A (fun x => f x || g x) z ⊆
      falseSupport R A f z ∪ falseSupport R A g z := by
  cases hf : f z <;> cases hg : g z
  · intro v hv
    simp only [falseSupport, hf, hg, Bool.false_or, ↓reduceIte, Finset.mem_inter,
      singletonSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.or_eq_true, Finset.mem_union] at hv ⊢
    rcases hv.1.2 with h | h
    · exact Or.inl ⟨⟨hv.1.1, h⟩, hv.2⟩
    · exact Or.inr ⟨⟨hv.1.1, h⟩, hv.2⟩
  all_goals simp [falseSupport, hf, hg]

lemma falseSupport_projection {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (v : α) (z : α → Bool) :
    (falseSupport R A (fun x => x v) z).card ≤ 1 := by
  apply le_trans (Finset.card_le_card (show
    falseSupport R A (fun x => x v) z ⊆ {v} from ?_))
    (by simp)
  intro u hu
  simp only [falseSupport] at hu
  split_ifs at hu with h
  · have he : v = u := by
      simpa [singletonSupport, singletonInput] using
        (Finset.mem_filter.mp (Finset.mem_inter.mp hu).1).2.2
    simp [he]
  · simp at hu

lemma falseSupport_of_sum {α : Type*} [DecidableEq α] [Fintype α]
    (S T A : Finset α) (f : (α → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ v ∈ S, x v = true)) :
    falseSupport (S \ A) A f (backgroundInput S T) = S \ A := by
  simp [falseSupport, background_sum_false S T f hf, support_of_sum S A f hf]

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

def growingFold {α β : Type*} (step : List β → α → β)
    (events : List α) (initial : List β) : List β :=
  events.foldl (fun state event => state ++ [step state event]) initial

lemma growingFold_length {α β : Type*} (step : List β → α → β)
    (events : List α) (initial : List β) :
    (growingFold step events initial).length = initial.length + events.length := by
  induction events generalizing initial with
  | nil => simp [growingFold]
  | cons event rest ih =>
    simpa [growingFold, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using ih (initial ++ [step initial event])

lemma growingFold_extends {α β : Type*} (step : List β → α → β)
    (events : List α) (initial : List β) :
    ∃ tail, growingFold step events initial = initial ++ tail := by
  induction events generalizing initial with
  | nil => exact ⟨[], by simp [growingFold]⟩
  | cons event rest ih =>
    obtain ⟨tail, he⟩ := ih (initial ++ [step initial event])
    exact ⟨[step initial event] ++ tail, by
      simpa [growingFold, List.foldl_cons, List.append_assoc] using he⟩

lemma growingFold_prefix {α β : Type*} (step : List β → α → β)
    (events : List α) (initial : List β) (k : ℕ) :
    ∃ tail, growingFold step events initial =
      growingFold step (events.take k) initial ++ tail := by
  obtain ⟨tail, he⟩ := growingFold_extends step (events.drop k)
    (growingFold step (events.take k) initial)
  refine ⟨tail, ?_⟩
  simpa only [growingFold, ← List.foldl_append, List.take_append_drop] using he

lemma guarded_prefix_lookup {α β : Type*} (step : List β → α → β)
    (events : List α) (initial : List β) (k r : ℕ) (fallback : β)
    (hk : k ≤ events.length) :
    (growingFold step (events.take k) initial).getD r fallback =
      if r < initial.length + k then
        (growingFold step events initial).getD r fallback else fallback := by
  have hlength : (growingFold step (events.take k) initial).length =
      initial.length + k := by
    rw [growingFold_length, List.length_take_of_le hk]
  by_cases hr : r < initial.length + k
  · rw [ite_eq_left hr]
    obtain ⟨tail, he⟩ := growingFold_prefix step events initial k
    rw [he]
    have hlt : r < (growingFold step (events.take k) initial).length := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  · rw [ite_eq_right hr]
    have hle : (growingFold step (events.take k) initial).length ≤ r := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle, Option.getD_none]

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

open scoped BigOperators

lemma residual_bound_of_traces {α ι : Type*} [DecidableEq α] [Fintype ι]
    (S : ι → Finset α) (A : Finset α) (t : α) (n G i0 : ℕ)
    (P : ℕ → Finset α) (Q : ι → ℕ → Finset α) (allowed : ι → ℕ → Prop)
    (hi0 : i0 < G)
    (hlin : ∀ i k, i ≠ k → (S i ∩ S k).card ≤ 1)
    (hR : ∀ i w, w < n + G → Q i w ⊆ S i \ A)
    (hinput : ∀ i w, w < n → (Q i w).card ≤ 1)
    (hstep : ∀ i j, j < G →
      (Q i (n + j)).card ≤ 1 ∨
      (∃ a < n + j, Q i (n + j) ⊆ Q i a) ∨
      (allowed i j ∧ ∃ a < n + j, ∃ b < n + j,
        Q i (n + j) ⊆ Q i a ∪ Q i b))
    (houtput : ∀ i, S i \ A = ∅ ∨ ∃ w < n + G, Q i w = S i \ A)
    (hmarked : ∀ i j, j < G → allowed i j →
      j ≠ i0 ∧ Q i (n + j) = P j ∩ (S i \ A) ∧ (P j).erase t ⊆ S i \ A) :
    1 + ∑ i, ((S i \ A).card - 1) ≤ G := by
  classical
  have hex : ∀ i, ∃ M : Finset ℕ, M.card = (S i \ A).card - 1 ∧
      ∀ j ∈ M, j < G ∧ allowed i j ∧ 2 ≤ (Q i (n + j)).card := by
    intro i
    exact mark_support_trace (S i \ A) n G (Q i) (allowed i)
      (hR i) (hinput i) (hstep i) (houtput i)
  choose M hcard hmarks using hex
  have hdisjoint : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint M := by
    intro i _ k _ hik
    apply Finset.disjoint_left.mpr
    intro j hji hjk
    obtain ⟨hj, hai, hci⟩ := hmarks i j hji
    obtain ⟨_, hak, hck⟩ := hmarks k j hjk
    obtain ⟨_, hqi, hpi⟩ := hmarked i j hj hai
    obtain ⟨_, hqk, hpk⟩ := hmarked k j hj hak
    have hres : ((S i \ A) ∩ (S k \ A)).card ≤ 1 := by
      apply le_trans (Finset.card_le_card ?_) (hlin i k hik)
      exact Finset.inter_subset_inter Finset.sdiff_subset Finset.sdiff_subset
    rw [hqi] at hci
    rw [hqk] at hck
    exact charge_unique (S i \ A) (S k \ A) (P j) t hres hpi hpk hci hck
  have hsub : Finset.univ.biUnion M ⊆ (Finset.range G).erase i0 := by
    intro j hj
    obtain ⟨i, _, hji⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hjlt, hai, _⟩ := hmarks i j hji
    exact Finset.mem_erase.mpr ⟨(hmarked i j hjlt hai).1, Finset.mem_range.mpr hjlt⟩
  have hbound := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisjoint] at hbound
  simp_rw [hcard] at hbound
  have hcapacity := Finset.card_erase_add_one (Finset.mem_range.mpr hi0)
  rw [Finset.card_range] at hcapacity
  omega

lemma finish_from_traces {α ι : Type*} [DecidableEq α] [Fintype ι]
    (S : ι → Finset α) (A : Finset α) (t : α) (n G i0 : ℕ)
    (P : ℕ → Finset α) (Q : ι → ℕ → Finset α) (allowed : ι → ℕ → Prop)
    (hi0 : i0 < G)
    (hlin : ∀ i k, i ≠ k → (S i ∩ S k).card ≤ 1)
    (hR : ∀ i w, w < n + G → Q i w ⊆ S i \ A)
    (hinput : ∀ i w, w < n → (Q i w).card ≤ 1)
    (hstep : ∀ i j, j < G →
      (Q i (n + j)).card ≤ 1 ∨
      (∃ a < n + j, Q i (n + j) ⊆ Q i a) ∨
      (allowed i j ∧ ∃ a < n + j, ∃ b < n + j,
        Q i (n + j) ⊆ Q i a ∪ Q i b))
    (houtput : ∀ i, S i \ A = ∅ ∨ ∃ w < n + G, Q i w = S i \ A)
    (hmarked : ∀ i j, j < G → allowed i j →
      j ≠ i0 ∧ Q i (n + j) = P j ∩ (S i \ A) ∧ (P j).erase t ⊆ S i \ A) :
    1 + ∑ i, ((S i).card - 1) ≤
      G + ∑ u ∈ A, (Finset.univ.filter (fun i => u ∈ S i)).card := by
  apply finish_from_residual
  exact residual_bound_of_traces S A t n G i0 P Q allowed hi0 hlin
    hR hinput hstep houtput hmarked

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

open scoped BigOperators

def guarded {n : ℕ} (F : ℕ → (Fin n → Bool) → Bool) (j r : ℕ) :
    (Fin n → Bool) → Bool := if r < n + j then F r else fun _ => false

def MonotoneOnZero {n : ℕ} (T : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ u ∈ T, x u = false) → (∀ u ∈ T, y u = false) →
    (∀ u, x u = true → y u = true) → f x = true → f y = true

def PositiveStep {n : ℕ} (F : ℕ → (Fin n → Bool) → Bool)
    (allowed : ℕ → Prop) (j : ℕ) : Prop :=
  (∃ c : Bool, F (n + j) = fun _ => c) ∨
  (∃ a, F (n + j) = guarded F j a) ∨
  (∃ a b, F (n + j) = fun x => guarded F j a x && guarded F j b x) ∨
  (allowed j ∧ ∃ a b, F (n + j) = fun x => guarded F j a x || guarded F j b x)

lemma guarded_monotone {n : ℕ} (T : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (j r : ℕ)
    (h : ∀ w < n + j, MonotoneOnZero T (F w)) :
    MonotoneOnZero T (guarded F j r) := by
  by_cases hr : r < n + j
  · simpa [guarded, hr] using h r hr
  · intro x y hx hy hxy hf
    simp [guarded, hr] at hf

lemma all_wires_monotone {n G : ℕ} (T : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (allowed : ℕ → Prop) (i0 : Fin G)
    (hinput : ∀ w (hw : w < n), F w = fun x => x ⟨w, hw⟩)
    (hmissing : ∀ w, n + G ≤ w → F w = fun _ => false)
    (hnot : ∀ x, (∀ u ∈ T, x u = false) → F (n + i0.val) x = true)
    (hstep : ∀ j < G, j ≠ i0.val → PositiveStep F allowed j) :
    ∀ w, MonotoneOnZero T (F w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [hinput w hw]
      intro x y hx hy hxy hf
      exact hxy _ hf
    · by_cases hlast : n + G ≤ w
      · rw [hmissing w hlast]
        intro x y hx hy hxy hf
        cases hf
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        by_cases hj : j = i0.val
        · subst j
          intro x y hx hy hxy hf
          exact hnot y hy
        · have hg (r : ℕ) : MonotoneOnZero T (guarded F j r) :=
            guarded_monotone T F j r (fun v hv => ih v hv)
          rcases hstep j (by omega) hj with ⟨c, hc⟩ | ⟨a, ha⟩ |
            ⟨a, b, hab⟩ | ⟨_, a, b, hab⟩
          · rw [hc]
            intro x y hx hy hxy hf
            exact hf
          · rw [ha]
            exact hg a
          · rw [hab]
            intro x y hx hy hxy hf
            simp only [Bool.and_eq_true] at hf ⊢
            exact ⟨hg a x y hx hy hxy hf.1, hg b x y hx hy hxy hf.2⟩
          · rw [hab]
            intro x y hx hy hxy hf
            simp only [Bool.or_eq_true] at hf ⊢
            rcases hf with ha | hb
            · exact Or.inl (hg a x y hx hy hxy ha)
            · exact Or.inr (hg b x y hx hy hxy hb)

lemma falseSupport_subset {α : Type*} [DecidableEq α] [Fintype α]
    (R A : Finset α) (f : (α → Bool) → Bool) (z : α → Bool) :
    falseSupport R A f z ⊆ R := by
  unfold falseSupport
  split_ifs
  · exact Finset.inter_subset_right
  · exact Finset.empty_subset R

lemma falseSupport_guarded {n : ℕ} (R A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (z : Fin n → Bool) (j r : ℕ) :
    falseSupport R A (guarded F j r) z =
      if r < n + j then falseSupport R A (F r) z else ∅ := by
  by_cases hr : r < n + j <;> simp [guarded, hr, falseSupport_false]

lemma guarded_copy_trace {n : ℕ} (R A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (z : Fin n → Bool) (j r : ℕ)
    (Q : Finset (Fin n)) (hQ : Q ⊆ falseSupport R A (guarded F j r) z) :
    Q.card ≤ 1 ∨ ∃ a < n + j, Q ⊆ falseSupport R A (F a) z := by
  rw [falseSupport_guarded] at hQ
  by_cases hr : r < n + j
  · exact Or.inr ⟨r, hr, by simpa [hr] using hQ⟩
  · left
    have he : Q = ∅ := Finset.subset_empty.mp (by simpa [hr] using hQ)
    simp [he]

lemma guarded_binary_trace {n : ℕ} (R A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (z : Fin n → Bool) (j a b : ℕ)
    (Q : Finset (Fin n))
    (hQ : Q ⊆ falseSupport R A (guarded F j a) z ∪
      falseSupport R A (guarded F j b) z) :
    Q.card ≤ 1 ∨ (∃ r < n + j, Q ⊆ falseSupport R A (F r) z) ∨
      ∃ r < n + j, ∃ s < n + j,
        Q ⊆ falseSupport R A (F r) z ∪ falseSupport R A (F s) z := by
  simp only [falseSupport_guarded] at hQ
  by_cases ha : a < n + j <;> by_cases hb : b < n + j
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, by simpa [ha, hb] using hQ⟩)
  · exact Or.inr (Or.inl ⟨a, ha, by simpa [ha, hb] using hQ⟩)
  · exact Or.inr (Or.inl ⟨b, hb, by simpa [ha, hb] using hQ⟩)
  · left
    have he : Q = ∅ := Finset.subset_empty.mp (by simpa [ha, hb] using hQ)
    simp [he]

lemma positive_support_trace {n : ℕ} (R A : Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (z : Fin n → Bool)
    (allowed : ℕ → Prop) (j : ℕ) (hstep : PositiveStep F allowed j) :
    (falseSupport R A (F (n + j)) z).card ≤ 1 ∨
    (∃ a < n + j, falseSupport R A (F (n + j)) z ⊆ falseSupport R A (F a) z) ∨
    (allowed j ∧ F (n + j) z = false ∧ ∃ a < n + j, ∃ b < n + j,
      falseSupport R A (F (n + j)) z ⊆
        falseSupport R A (F a) z ∪ falseSupport R A (F b) z) := by
  by_cases hz : F (n + j) z = false
  · rcases hstep with ⟨c, hc⟩ | ⟨a, ha⟩ | ⟨a, b, hab⟩ | ⟨hok, a, b, hab⟩
    · left
      rw [hc]
      cases c <;> simp [falseSupport_false, falseSupport_true]
    · rw [ha]
      exact (guarded_copy_trace R A F z j a _ le_rfl).imp_right Or.inl
    · rw [hab]
      rcases falseSupport_and R A (guarded F j a) (guarded F j b) z with h | h
      · exact (guarded_copy_trace R A F z j a _ h).imp_right Or.inl
      · exact (guarded_copy_trace R A F z j b _ h).imp_right Or.inl
    · have ht := guarded_binary_trace R A F z j a b _
        (falseSupport_or R A (guarded F j a) (guarded F j b) z)
      rw [← hab] at ht
      rcases ht with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hok, hz, h⟩)
  · left
    simp [falseSupport, hz]

lemma bound_of_guarded_semantics {n m G : ℕ} (S : Fin m → Finset (Fin n))
    (F : ℕ → (Fin n → Bool) → Bool) (out : Fin m → ℕ) (i0 : Fin G)
    (T : Finset (Fin n)) (t0 : Fin n) (allowed : ℕ → Prop)
    (hlin : ∀ i k, i ≠ k → (S i ∩ S k).card ≤ 1)
    (hinput : ∀ w (hw : w < n), F w = fun x => x ⟨w, hw⟩)
    (hmissing : ∀ w, n + G ≤ w → F w = fun _ => false)
    (hnot : ∀ x, (∀ u ∈ T, x u = false) → F (n + i0.val) x = true)
    (hstep : ∀ j < G, j ≠ i0.val → PositiveStep F allowed j)
    (hexclude : ¬ allowed i0.val)
    (hspec : ∀ i x, F (out i) x = decide (∃ v ∈ S i, x v = true)) :
    1 + ∑ i, ((S i).card - 1) ≤
      G + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun i => u ∈ S i)).card := by
  classical
  let A := T.erase t0
  let R := fun i => S i \ A
  let z := fun i => backgroundInput (S i) T
  let Q := fun i w => falseSupport (R i) A (F w) (z i)
  let P := fun j => singletonSupport A (F (n + j))
  let ok := fun i j => allowed j ∧ F (n + j) (z i) = false
  have hz (i) : ∀ u ∈ T, z i u = false := by
    intro u hu
    simp [z, backgroundInput, hu]
  have hm := all_wires_monotone T F allowed i0 hinput hmissing hnot hstep
  apply finish_from_traces S A t0 n G i0.val P Q ok i0.isLt hlin
  · intro i w hw
    exact falseSupport_subset (R i) A (F w) (z i)
  · intro i w hw
    dsimp [Q]
    rw [hinput w hw]
    exact falseSupport_projection (R i) A ⟨w, hw⟩ (z i)
  · intro i j hj
    by_cases he : j = i0.val
    · left
      subst j
      simp [Q, falseSupport, hnot (z i) (hz i)]
    · simpa only [Q, ok, and_assoc] using
        positive_support_trace (R i) A F (z i) allowed j (hstep j hj he)
  · intro i
    by_cases hR : R i = ∅
    · exact Or.inl hR
    · right
      have he : Q i (out i) = R i := falseSupport_of_sum (S i) T A (F (out i))
        (fun x => by
          by_cases hp : ∃ v ∈ S i, x v = true <;> simpa only [hp, decide_true, decide_false]
            using hspec i x)
      refine ⟨out i, ?_, he⟩
      by_contra hout
      have hzero := hmissing (out i) (by omega)
      have : Q i (out i) = ∅ := by simp [Q, hzero, falseSupport_false]
      exact hR (he.symm.trans this)
  · intro i j hj hok
    refine ⟨?_, ?_, ?_⟩
    · intro he
      exact hexclude (he ▸ hok.1)
    · simp [Q, P, R, falseSupport, hok.2]
    · exact support_erased_subset (S i) T t0 (F (n + j)) hok.2 (hm (n + j))

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

lemma growingFold_input {α : Type*} {n : ℕ} (step : List Bool → α → Bool)
    (events : List α) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (growingFold step events (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  have h := guarded_prefix_lookup step events (List.ofFn x) 0 w false (Nat.zero_le _)
  simpa [growingFold, hw] using h.symm

lemma growingFold_missing {α : Type*} {n : ℕ} (step : List Bool → α → Bool)
    (events : List α) (x : Fin n → Bool) (w : ℕ) (hw : n + events.length ≤ w) :
    (growingFold step events (List.ofFn x)).getD w false = false := by
  have hl : (growingFold step events (List.ofFn x)).length ≤ w := by
    simpa [growingFold_length] using hw
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]

lemma growingFold_gate {α : Type*} {β : Type*} (step : List β → α → β)
    (events : List α) (initial : List β) (j : Fin events.length) (fallback : β) :
    (growingFold step events initial).getD (initial.length + j.val) fallback =
      step (growingFold step (events.take j.val) initial) (events.get j) := by
  have he : growingFold step (events.take (j.val + 1)) initial =
      growingFold step (events.take j.val) initial ++
        [step (growingFold step (events.take j.val) initial) (events.get j)] := by
    rw [List.take_succ_eq_append_getElem j.isLt]
    simp only [growingFold, List.foldl_append, List.foldl_cons, List.foldl_nil, List.get_eq_getElem]
  have h := guarded_prefix_lookup step events initial (j.val + 1)
    (initial.length + j.val) fallback (by omega)
  have hl : (growingFold step (events.take j.val) initial).length = initial.length + j.val := by
    simp [growingFold_length, List.length_take_of_le (Nat.le_of_lt j.isLt)]
  rw [ite_eq_left (by omega), he, ← hl] at h
  rw [← hl]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_concat_length] using h.symm

lemma growingFold_gate_guarded {α : Type*} {n : ℕ}
    (events : List α) (inputs : α → List ℕ) (operation : α → List Bool → Bool)
    (j : Fin events.length) (x : Fin n → Bool) :
    (growingFold (fun state g => operation g ((inputs g).map fun r => state.getD r false))
      events (List.ofFn x)).getD (n + j.val) false =
    operation (events.get j) ((inputs (events.get j)).map fun r =>
      guarded (fun w x =>
        (growingFold (fun state g => operation g ((inputs g).map fun r => state.getD r false))
          events (List.ofFn x)).getD w false) j.val r x) := by
  let step := fun (state : List Bool) g => operation g ((inputs g).map fun r => state.getD r false)
  have he := growingFold_gate step events (List.ofFn x) j false
  simp only [List.length_ofFn] at he
  rw [he]
  dsimp only [step]
  congr 1
  apply List.map_congr_left
  intro r hr
  have h := guarded_prefix_lookup step events (List.ofFn x) j.val r false
    (Nat.le_of_lt j.isLt)
  by_cases hr : r < n + j.val <;> simpa [List.length_ofFn, guarded, hr, step] using h

lemma positive_of_list_all {n : ℕ} (F : ℕ → (Fin n → Bool) → Bool)
    (allowed : ℕ → Prop) (j : ℕ) (args : List ℕ) (hargs : args.length ≤ 2)
    (hf : ∀ x, F (n + j) x = (args.map fun r => guarded F j r x).all id) :
    PositiveStep F allowed j := by
  cases args with
  | nil => exact Or.inl ⟨true, funext (fun x => by simpa using hf x)⟩
  | cons a tail =>
    cases tail with
    | nil => exact Or.inr (Or.inl ⟨a, funext (fun x => by simpa using hf x)⟩)
    | cons b tail =>
      cases tail with
      | nil => exact Or.inr (Or.inr (Or.inl ⟨a, b,
          funext (fun x => by simpa using hf x)⟩))
      | cons c tail => simp at hargs

lemma positive_of_list_any {n : ℕ} (F : ℕ → (Fin n → Bool) → Bool)
    (allowed : ℕ → Prop) (j : ℕ) (args : List ℕ) (hargs : args.length ≤ 2)
    (hj : allowed j)
    (hf : ∀ x, F (n + j) x = (args.map fun r => guarded F j r x).any id) :
    PositiveStep F allowed j := by
  cases args with
  | nil => exact Or.inl ⟨false, funext (fun x => by simpa using hf x)⟩
  | cons a tail =>
    cases tail with
    | nil => exact Or.inr (Or.inl ⟨a, funext (fun x => by simpa using hf x)⟩)
    | cons b tail =>
      cases tail with
      | nil => exact Or.inr (Or.inr (Or.inr ⟨hj, a, b,
          funext (fun x => by simpa using hf x)⟩))
      | cons c tail => simp at hargs

lemma list_negation_on_zero {n : ℕ} (F : ℕ → (Fin n → Bool) → Bool)
    (T : Finset (Fin n)) (j hw : ℕ) (args : List ℕ)
    (hhead : args.head? = some hw) (hbefore : hw < n + j)
    (hf : ∀ x, F (n + j) x = !((args.map fun r => guarded F j r x).headD false))
    (hzero : ∀ x, (∀ u ∈ T, x u = false) → F hw x = false) :
    ∀ x, (∀ u ∈ T, x u = false) → F (n + j) x = true := by
  intro x hx
  cases args with
  | nil => simp at hhead
  | cons a tail =>
    have ha : a = hw := by simpa using hhead
    subst a
    simpa [guarded, hbefore, hzero x hx] using hf x

end PEqualNP.Outside.L_meta_986_aux

namespace PEqualNP.Outside.L_meta_986_aux

open scoped BigOperators

def traceValue {α : Type*} (n : ℕ) (events : List α) (inputs : α → List ℕ)
    (operation : α → List Bool → Bool) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (growingFold (fun state g => operation g ((inputs g).map fun r => state.getD r false))
    events (List.ofFn x)).getD w false

lemma bound_of_fold_semantics {α : Type*} {n m : ℕ}
    (S : Fin m → Finset (Fin n)) (events : List α) (inputs : α → List ℕ)
    (operation : α → List Bool → Bool) (out : Fin m → ℕ) (i0 : Fin events.length)
    (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n)
    (hlin : ∀ i k, i ≠ k → (S i ∩ S k).card ≤ 1)
    (hfan : ∀ j : Fin events.length, (inputs (events.get j)).length ≤ 2)
    (hpos : ∀ j : Fin events.length, j ≠ i0 →
      (∀ l, operation (events.get j) l = l.all id) ∨
      (∀ l, operation (events.get j) l = l.any id))
    (hneg : ∀ l, operation (events.get i0) l = !(l.headD false))
    (hhead : (inputs (events.get i0)).head? = some hw)
    (hbefore : hw < n + i0.val)
    (hspec : ∀ i x, traceValue n events inputs operation (out i) x =
      decide (∃ v ∈ S i, x v = true))
    (hzero : ∀ x, (∀ u ∈ T, x u = false) →
      traceValue n events inputs operation hw x = false) :
    1 + ∑ i, ((S i).card - 1) ≤
      events.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun i => u ∈ S i)).card := by
  let F := traceValue n events inputs operation
  let allowed := fun j => ∃ h : j < events.length,
    ∀ l, operation (events.get ⟨j, h⟩) l = l.any id
  have hgate (j : Fin events.length) (x : Fin n → Bool) :
      F (n + j.val) x = operation (events.get j)
        ((inputs (events.get j)).map fun r => guarded F j.val r x) :=
    growingFold_gate_guarded events inputs operation j x
  apply bound_of_guarded_semantics S F out i0 T t0 allowed hlin
  · intro w hw
    funext x
    exact growingFold_input _ events x w hw
  · intro w hw
    funext x
    exact growingFold_missing _ events x w hw
  · apply list_negation_on_zero F T i0.val hw (inputs (events.get i0)) hhead hbefore
    · intro x
      rw [hgate, hneg]
    · exact hzero
  · intro j hj hji
    have hneq : (⟨j, hj⟩ : Fin events.length) ≠ i0 := by
      intro he
      exact hji (congrArg Fin.val he)
    rcases hpos ⟨j, hj⟩ hneq with hand | hor
    · apply positive_of_list_all F allowed j (inputs (events.get ⟨j, hj⟩)) (hfan ⟨j, hj⟩)
      intro x
      exact (hgate ⟨j, hj⟩ x).trans (hand _)
    · apply positive_of_list_any F allowed j (inputs (events.get ⟨j, hj⟩)) (hfan ⟨j, hj⟩)
      · exact ⟨hj, hor⟩
      · intro x
        exact (hgate ⟨j, hj⟩ x).trans (hor _)
  · rintro ⟨hi, h⟩
    have hn := hneg []
    have ho := h []
    have he : (⟨i0.val, hi⟩ : Fin events.length) = i0 := Fin.ext rfl
    rw [he] at ho
    simp only [List.headD_nil, Bool.not_false, List.any_nil] at hn ho
    exact Bool.noConfusion (hn.symm.trans ho)
  · exact hspec

end PEqualNP.Outside.L_meta_986_aux

theorem PEqualNP.Outside.L_meta_986 :
∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  intro n m S gates out i0 hw T t0 hsizes hlin hfan honly hneg hhead hbefore hspec hzero ht0 hfreq
  apply PEqualNP.Outside.L_meta_986_aux.bound_of_fold_semantics S gates
    PEqualNP.CircuitLowerBounds.Gate.inputs
    (fun g l => g.op.eval l) out i0 hw T t0 hlin
  · intro j
    exact (hfan (gates.get j) (List.get_mem gates j)).2
  · intro j hne
    rcases (hfan (gates.get j) (List.get_mem gates j)).1 with hand | hor | hnot
    · left
      intro l
      change (gates.get j).op.eval l = l.all id
      rw [hand]
      rfl
    · right
      intro l
      change (gates.get j).op.eval l = l.any id
      rw [hor]
      rfl
    · exact False.elim (hne (honly j hnot))
  · intro l
    change (gates.get i0).op.eval l = !(l.headD false)
    rw [hneg]
    rfl
  · exact hhead
  · exact hbefore
  · intro i x
    exact hspec i x
  · intro x hx
    exact hzero x hx
