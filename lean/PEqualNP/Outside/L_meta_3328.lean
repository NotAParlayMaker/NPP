import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def gate (s : List ℕ) (y : ℕ) : Prop :=
  ∃ u ∈ s, ∃ v ∈ s, y = u &&& v ∨ y = u ||| v

def valid (s t : List ℕ) : Prop :=
  ∀ i : Fin t.length, gate (s ++ t.take i.val) (t.get i)

lemma mono {s t : List ℕ} {v : ℕ} (h : ∀ x ∈ s, x ∈ t) (hv : gate s v) : gate t v := by
  obtain ⟨a, ha, b, hb, e⟩ := hv
  exact ⟨a, h _ ha, b, h _ hb, e⟩

lemma consValid {s t : List ℕ} {a : ℕ} :
    valid s (a :: t) ↔ gate s a ∧ valid (s ++ [a]) t := by
  constructor
  · intro h
    constructor
    · simpa using h ⟨0, by simp⟩
    · intro i
      simpa [List.append_assoc] using h i.succ
  · rintro ⟨ha, ht⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa [List.append_assoc] using ht j

lemma baseMono {s s' t : List ℕ} (h : ∀ x ∈ s, x ∈ s') (ht : valid s t) : valid s' t := by
  intro i
  apply mono _ (ht i)
  intro x hx
  rcases List.mem_append.mp hx with h₁ | h₂
  · exact List.mem_append_left _ (h _ h₁)
  · exact List.mem_append_right _ h₂

lemma snocValid {s t : List ℕ} {a : ℕ} (ht : valid s t) (ha : gate (s ++ t) a) :
    valid s (t ++ [a]) := by
  induction t generalizing s with
  | nil => exact consValid.mpr ⟨by simpa using ha, fun i => Fin.elim0 i⟩
  | cons b t ih =>
    obtain ⟨hb, ht⟩ := consValid.mp ht
    exact consValid.mpr ⟨hb, ih ht (by simpa [List.append_assoc] using ha)⟩

lemma compress {s t : List ℕ} (ht : valid s t) :
    ∃ u : List ℕ, u.length ≤ t.length ∧ u.Nodup ∧ (∀ v ∈ u, v ∉ s) ∧
      (∀ v ∈ t, v ∈ s ∨ v ∈ u) ∧ valid s u := by
  induction t generalizing s with
  | nil => exact ⟨[], by simp, by simp, by simp, by simp, fun i => Fin.elim0 i⟩
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := consValid.mp ht
    by_cases h : a ∈ s
    · have hsub : ∀ v ∈ s ++ [a], v ∈ s := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hv
        · simpa [List.mem_singleton.mp hv] using h
      obtain ⟨u, hn, hd, hs, hc, hv⟩ := ih (baseMono hsub ht)
      exact ⟨u, by simp; omega, hd, hs, by simpa [h] using hc, hv⟩
    · obtain ⟨u, hn, hd, hs, hc, hv⟩ := ih ht
      refine ⟨a :: u, by simpa using hn, List.nodup_cons.mpr ⟨?_, hd⟩, ?_, ?_, consValid.mpr ⟨ha,hv⟩⟩
      · intro hau
        exact hs a hau (by simp)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hm
        · exact h
        · exact fun hvs => hs v hm (List.mem_append_left _ hvs)
      · intro v hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simp
        · simpa [or_assoc, or_left_comm, or_comm] using hc v hm

end PEqualNP.Outside.L_meta_3328

open PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  dsimp only
  intro s a b t hb ha ht hlast
  have ht' : valid (s ++ [a]) t := baseMono (by simp [or_comm]) ht
  have hv : valid s (a :: t) := consValid.mpr ⟨ha, ht'⟩
  have hend : gate (s ++ (a :: t)) b := mono (by simp [or_left_comm]) hlast
  obtain ⟨u, hn, hd, hs, hc, hu⟩ := compress (snocValid hv hend)
  exact ⟨u, by simpa [Nat.add_assoc] using hn, hd, hs, (hc b (by simp)).resolve_left hb, hu⟩
