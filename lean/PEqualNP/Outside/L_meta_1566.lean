import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1566

abbrev line (t : Fin 13) : Finset (Fin 13) := {t, t+1, t+3, t+9}
abbrev leftPart : Finset (Fin 13) := {4,10,12}
abbrev rightPart : Finset (Fin 13) := {1,5,11}

abbrev witness (t u : Fin 13) : Prop :=
  ∃ p ∈ line t \ line u, ∃ v ∈ line u, decide (v = p ∨ v ∈
    (if (0 : Fin 13) ∉ line t ∧ p ≠ 1 then ({0} : Finset (Fin 13))
     else if t ∈ leftPart ∧ p ≠ 0 then {1}
     else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ line 0 else ∅)) = true

abbrev mutualEdge (t u : Fin 13) := t ≠ u ∧ witness t u ∧ witness u t
abbrev edge (t u : Fin 13) := (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨
  (t ∈ leftPart ∧ u ∈ rightPart) ∨ (t ∈ rightPart ∧ u ∈ leftPart)
abbrev clique (K : Finset (Fin 13)) := ∀ t ∈ K, ∀ u ∈ K, t ≠ u → edge t u
abbrev triangle (K : Finset (Fin 13)) := ∃ l ∈ leftPart, ∃ m ∈ rightPart, K = {0,l,m}
abbrev tally (K : Finset (Fin 13)) := K.card - 1 =
  (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
  (if ∃ l ∈ K, ∃ m ∈ K, l ∈ leftPart ∧ m ∈ rightPart then 1 else 0)
abbrev near (v : Fin 13) := Finset.univ.filter (fun t => v = t ∨ edge v t)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma adjacency : ∀ t u : Fin 13, mutualEdge t u ↔ edge t u := by decide

lemma enclosure (K : Finset (Fin 13)) (hk : clique K) :
    ∃ v : Fin 13, v ≠ 0 ∧ K ⊆ near v := by
  by_cases h : ∃ v ∈ K, v ≠ 0
  · obtain ⟨v,hv,hn⟩ := h
    refine ⟨v,hn,fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    by_cases e : v = t
    · exact Or.inl e
    · exact Or.inr (hk v hv t ht e)
  · refine ⟨1,by decide,fun t ht => ?_⟩
    have he : t = 0 := by by_contra hn; exact h ⟨t,ht,hn⟩
    subst t
    decide

abbrev localStatement (v : Fin 13) := ∀ K ∈ (near v).powerset,
  clique K → (3 ≤ K.card → triangle K) ∧ (1 ≤ K.card → tally K)

set_option synthInstance.maxSize 4096 in
def checkNeighborhood (v : Fin 13) : Decidable (localStatement v) :=
  Finset.decidableDforallFinset

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
lemma neighborhoods (v : Fin 13) (hn : v ≠ 0) : localStatement v := by
  have allValid : ∀ w : Fin 13, w ≠ 0 → @decide (localStatement w) (checkNeighborhood w) = true := by
    decide
  exact @of_decide_eq_true _ (checkNeighborhood v) (allValid v hn)

lemma classify (K : Finset (Fin 13)) (hk : clique K) :
    (3 ≤ K.card → triangle K) ∧ (1 ≤ K.card → tally K) := by
  obtain ⟨v,hn,hs⟩ := enclosure K hk
  exact neighborhoods v hn K (Finset.mem_powerset.mpr hs) hk

lemma converse : ∀ l ∈ leftPart, ∀ m ∈ rightPart, clique {0,l,m} := by decide

end PEqualNP.Outside.L_meta_1566

open PEqualNP.Outside.L_meta_1566

theorem PEqualNP.Outside.L_meta_1566 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ t u : Fin 13, (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true)) ↔
      (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) ∧
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  intro L hL
  have e : L = PEqualNP.Outside.L_meta_1566.line := funext hL
  subst L
  change (∀ t u, mutualEdge t u ↔ edge t u) ∧
    (∀ K, 3 ≤ Finset.card K → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → mutualEdge t u) ↔ triangle K)) ∧
    (∀ K, 1 ≤ Finset.card K → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → mutualEdge t u) → tally K)
  refine ⟨adjacency, ?_, ?_⟩
  · intro K hs
    constructor
    · intro h
      exact (classify K (fun t ht u hu he => (adjacency t u).mp (h t ht u hu he))).1 hs
    · rintro ⟨l,hl,m,hm,rfl⟩ t ht u hu he
      exact (adjacency t u).mpr (converse l hl m hm t ht u hu he)
  · intro K hs h
    exact (classify K (fun t ht u hu he => (adjacency t u).mp (h t ht u hu he))).2 hs
