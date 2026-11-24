import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328_aux

def CanDerive (base : List ℕ) (value : ℕ) : Prop :=
  ∃ a ∈ base, ∃ b ∈ base, value = a &&& b ∨ value = a ||| b

def Valid (base values : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < values.length),
    CanDerive (base ++ values.take i) values[i]

lemma derive_mono {base wider : List ℕ} {value : ℕ} (h : base ⊆ wider)
    (hv : CanDerive base value) : CanDerive wider value := by
  obtain ⟨a, ha, b, hb, hvalue⟩ := hv
  exact ⟨a, h ha, b, h hb, hvalue⟩

lemma valid_mono {base wider values : List ℕ} (h : base ⊆ wider)
    (hv : Valid base values) : Valid wider values := by
  intro i hi
  apply derive_mono _ (hv i hi)
  intro a ha
  rcases List.mem_append.mp ha with hbase | htake
  · exact List.mem_append_left _ (h hbase)
  · exact List.mem_append_right _ htake

lemma derive_cons_swap (base tail : List ℕ) (head value : ℕ) :
    CanDerive (base ++ head :: tail) value ↔ CanDerive ((head :: base) ++ tail) value := by
  have hmem (a : ℕ) : a ∈ base ++ head :: tail ↔ a ∈ (head :: base) ++ tail := by
    simp only [List.mem_append, List.mem_cons]
    tauto
  exact ⟨derive_mono (fun a ha => (hmem a).mp ha),
    derive_mono (fun a ha => (hmem a).mpr ha)⟩

lemma valid_cons (base tail : List ℕ) (head : ℕ) :
    Valid base (head :: tail) ↔ CanDerive base head ∧ Valid (head :: base) tail := by
  constructor
  · intro h
    have hzero := h 0 (by simp)
    change CanDerive (base ++ []) head at hzero
    refine ⟨by simpa only [List.append_nil] using hzero, ?_⟩
    intro i hi
    have hnext := h (i + 1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hi)
    apply (derive_cons_swap base (tail.take i) head _).mp
    simpa only [List.take_succ_cons, List.getElem_cons_succ] using hnext
  · rintro ⟨hhead, htail⟩ i hi
    cases i with
    | zero => simpa using hhead
    | succ i =>
      have hi' : i < tail.length := by
        simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      simp only [List.take_succ_cons, List.getElem_cons_succ]
      exact (derive_cons_swap base (tail.take i) head _).mpr (htail i hi')

lemma valid_append_one {base values : List ℕ} {value : ℕ} (hv : Valid base values)
    (hd : CanDerive (base ++ values) value) : Valid base (values ++ [value]) := by
  intro i hi
  by_cases hlt : i < values.length
  · rw [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt]
    exact hv i hlt
  · have heq : i = values.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    subst i
    rw [List.take_left, List.getElem_append_right (by rfl)]
    simpa using hd

lemma normalize (base values : List ℕ) (h : Valid base values) :
    ∃ kept : List ℕ, kept.length ≤ values.length ∧ kept.Nodup ∧
      (∀ x ∈ kept, x ∉ base) ∧ Valid base kept ∧
      (∀ x, x ∈ base ++ values ↔ x ∈ base ++ kept) := by
  induction values generalizing base with
  | nil => exact ⟨[], by simp, by simp, by simp, h, fun _ => Iff.rfl⟩
  | cons a tail ih =>
    obtain ⟨ha, ht⟩ := (valid_cons base tail a).mp h
    by_cases hm : a ∈ base
    · have hsubset : a :: base ⊆ base := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hm
        · exact hx
      obtain ⟨kept, hlen, hn, hdis, hk, hmem⟩ := ih base (valid_mono hsubset ht)
      refine ⟨kept, by simp only [List.length_cons]; omega, hn, hdis, hk, ?_⟩
      intro x
      refine Iff.trans ?_ (hmem x)
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro (hx | rfl | hx)
        · exact Or.inl hx
        · exact Or.inl hm
        · exact Or.inr hx
      · exact fun hx => hx.imp_right Or.inr
    · obtain ⟨kept, hlen, hn, hdis, hk, hmem⟩ := ih (a :: base) ht
      have hnot : a ∉ kept := fun hk => hdis a hk (List.mem_cons_self)
      refine ⟨a :: kept, by simp only [List.length_cons]; omega,
        List.nodup_cons.mpr ⟨hnot, hn⟩, ?_, (valid_cons base kept a).mpr ⟨ha,hk⟩, ?_⟩
      · intro x hx hxbase
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hm hxbase
        · exact hdis x hx (List.mem_cons_of_mem _ hxbase)
      · intro x
        simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem x

end PEqualNP.Outside.L_meta_3328_aux

open PEqualNP.Outside.L_meta_3328_aux

theorem PEqualNP.Outside.L_meta_3328 :
  have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  dsimp only
  intro base first target values htarget hfirst hvalues hderive
  change CanDerive base first at hfirst
  change CanDerive ((first :: base) ++ values) target at hderive
  have hv : Valid (first :: base) values := fun i hi => hvalues ⟨i, hi⟩
  have hprefix := (valid_cons base values first).mpr ⟨hfirst, hv⟩
  have hlast := (derive_cons_swap base values first target).mpr hderive
  have hvalid := valid_append_one hprefix hlast
  obtain ⟨kept, hlen, hn, hdis, hk, hmem⟩ := normalize base ((first :: values) ++ [target]) hvalid
  have hkept : target ∈ base ++ kept := (hmem target).mp (by simp)
  refine ⟨kept, by simpa using hlen, hn, hdis, (List.mem_append.mp hkept).resolve_left htarget, ?_⟩
  exact fun i => hk i.val i.isLt
