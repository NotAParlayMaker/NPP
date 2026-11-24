import Mathlib
import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

theorem PEqualNP.Outside.R_meta_3210_67
    (cover : let p : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
      let n : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
      let F := enc 10 14 p.contains (p ++ n)
      ∀ a : Nat → Bool, (∀ c ∈ F, ClauseSat a c) →
        ∃ t : Fin 2, ∃ u : Fin 12, ∀ c ∈ ([[188868],[27276+2*t.val],[58766+2*u.val],[90260]] ++ (List.range 13).map (fun j => [188843+2*j])), ClauseSat a c)
    (andCuts : let p : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
      let n : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
      let F := enc 10 14 p.contains (p ++ n)
      ∀ u : Fin 12, ¬FormulaSat (F ++ ([[188868],[27276],[58766+2*u.val],[90260]] ++ (List.range 13).map (fun j => [188843+2*j]))))
    (orCuts : let p : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
      let n : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
      let F := enc 10 14 p.contains (p ++ n)
      ∀ u : Fin 12, ¬FormulaSat (F ++ ([[188868],[27278],[58766+2*u.val],[90260]] ++ (List.range 13).map (fun j => [188843+2*j])))) :
    have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) := by
  dsimp only
  rintro ⟨a,ha⟩
  obtain ⟨t,u,h⟩ := cover a ha
  fin_cases t
  · apply andCuts u
    exact ⟨a,fun c hc => (List.mem_append.mp hc).elim (ha c) (h c)⟩
  · apply orCuts u
    exact ⟨a,fun c hc => (List.mem_append.mp hc).elim (ha c) (h c)⟩
