import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1994_aux

abbrev graph : SimpleGraph (Fin 10) := SimpleGraph.fromRel fun a b =>
  (a.val,b.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
abbrev mask (m : ℕ) : Finset (Fin 10) := {v | m.testBit v.val = true}
abbrev masks : List ℕ := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
abbrev independent (s : Finset (Fin 10)) : Prop := ∀ v ∈ s, ∀ w ∈ s, ¬ graph.Adj v w
abbrev maximal (s : Finset (Fin 10)) : Prop := ∀ v ∉ s, ∃ w ∈ s, graph.Adj w v
abbrev classified (s : Finset (Fin 10)) : Prop := ∃ m ∈ masks, s = mask m
abbrev covered (s : Finset (Fin 10)) : Prop :=
  s.card = 3 ∨ ∀ v ∉ s, ∃ m ∈ masks, (mask m).card = 3 ∧
    ∃ w ∉ mask m, insert w (mask m) ⊆ insert v s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma certificate : ∀ s : Finset (Fin 10), independent s → maximal s → classified s ∧ covered s := by
  letI : DecidablePred independent := fun _ => inferInstance
  letI : DecidablePred maximal := fun _ => inferInstance
  letI : DecidablePred classified := fun _ => inferInstance
  letI : DecidablePred covered := fun _ => inferInstance
  decide

end PEqualNP.Outside.L_meta_1994_aux

theorem PEqualNP.Outside.L_meta_1994 : ∀ (x1 : SimpleGraph (Fin (10 : ℕ))),   (x1 = SimpleGraph.fromRel fun (x2 x3 : Fin (10 : ℕ)) => (↑x2, ↑x3) ∈ [((0 : ℕ), (1 : ℕ)), ((1 : ℕ), (2 : ℕ)), ((2 : ℕ), (3 : ℕ)), ((3 : ℕ), (4 : ℕ)), ((4 : ℕ), (0 : ℕ)), ((0 : ℕ), (5 : ℕ)), ((1 : ℕ), (6 : ℕ)), ((2 : ℕ), (7 : ℕ)), ((3 : ℕ), (8 : ℕ)), ((4 : ℕ), (9 : ℕ)), ((5 : ℕ), (7 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((9 : ℕ), (6 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((8 : ℕ), (5 : ℕ))]) →     have x3 : ℕ → Finset (Fin (10 : ℕ)) := fun (x3 : ℕ) => {x4 : Fin (10 : ℕ) | x3.testBit ↑x4 = Bool.true};     have x4 : List ℕ := [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)];     ∀ (x5 : Finset (Fin (10 : ℕ))), (∀ x6 ∈ x5, ∀ x8 ∈ x5, ¬x1.Adj x6 x8) → (∀ x7 ∉ x5, ∃ x9 ∈ x5, x1.Adj x9 x7) → (∃ x8 ∈ x4, x5 = x3 x8) ∧ (x5.card = (3 : ℕ) ∨ ∀ x8 ∉ x5, ∃ x10 ∈ x4, (x3 x10).card = (3 : ℕ) ∧ ∃ x11 ∉ x3 x10, Insert.insert x11 (x3 x10) ⊆ Insert.insert x8 x5) := by
  intro G hG
  subst G
  exact PEqualNP.Outside.L_meta_1994_aux.certificate
