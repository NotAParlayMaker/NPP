import Mathlib
import PEqualNP.Defs

-- The last b bits of x form a string of length b, so they are among the sections of b copies
-- of [false, true], and with them the prefix gives back x, which f accepts. So find? succeeds,
-- and what it returns is accepted and is a section, hence of length b.

namespace PEqualNP.Outside.L_lib_121

theorem sections_length (b : ℕ) (s : List Bool)
    (hs : s ∈ (List.replicate b [false, true]).sections) : s.length = b := by
  rw [List.mem_sections] at hs
  simpa using hs.length_eq

theorem mem_sections_of_length (b : ℕ) (s : List Bool) (hs : s.length = b) :
    s ∈ (List.replicate b [false, true]).sections := by
  rw [List.mem_sections]
  subst hs
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (by cases a <;> simp) ih

end PEqualNP.Outside.L_lib_121

open PEqualNP.Outside.L_lib_121

theorem PEqualNP.Outside.L_lib_121 : ∀ (f : List Bool → Bool) (b : ℕ) (x : List Bool), b ≤ x.length → f x = true → ∃ s : List Bool, (List.replicate b [false, true]).sections.find? (fun s => f (x.take (x.length - b) ++ s)) = some s ∧ s.length = b ∧ f (x.take (x.length - b) ++ s) = true := by
  intro f b x hb hx
  have hsuf : (x.drop (x.length - b)) ∈ (List.replicate b [false, true]).sections :=
    mem_sections_of_length b _ (by simp; omega)
  have hp : f (x.take (x.length - b) ++ x.drop (x.length - b)) = true := by
    rw [List.take_append_drop]
    exact hx
  cases hfind : (List.replicate b [false, true]).sections.find?
      (fun s => f (x.take (x.length - b) ++ s)) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd hp (by simpa using hfind _ hsuf)
  | some s =>
    refine ⟨s, rfl, sections_length b s (List.mem_of_find?_eq_some hfind), ?_⟩
    simpa using List.find?_some hfind
