import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_1884_704
    (negated : ∀ (σ : Fin 10 → Fin 10) (f : Bool → Bool),
      let computes := fun D : Circuit => FanInTwo D ∧ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (ℕ × ℕ)).any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false)) x
      ∀ C : Circuit, computes C → (∀ D : Circuit, computes D → C.size ≤ D.size) →
        (∃ g ∈ C.gates, g.op = GateOp.not) → 19 ≤ C.size)
    (nested : ∀ (σ : Fin 10 → Fin 10) (f : Bool → Bool),
      let computes := fun D : Circuit => FanInTwo D ∧ ∀ x : Fin 10 → Bool,
        D.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (ℕ × ℕ)).any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false)) x
      ∀ C : Circuit, computes C → (∀ D : Circuit, computes D → C.size ≤ D.size) →
        AndOrOnly C → 0 < PEqualNP.TopForm.andPairs 11 C → 19 ≤ C.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  -- Choose a least correct circuit for the given input map and unary signal.
  let F := (fun x : Fin 10 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (ℕ × ℕ)).any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false))
  let direct := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have same : ∀ x, direct x = F x := by
    dsimp only [direct,F]
    decide +kernel
  suffices flatProof : ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (f : Bool → Bool),
      FanInTwo C → AndOrOnly C → PEqualNP.TopForm.andPairs 11 C = 0 →
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = F x) → 20 ≤ C.size by
    classical
    intro C σ f fan budget
    by_contra no
    let works := fun D : Circuit => FanInTwo D ∧ ∀ x : Fin 10 → Bool,
      D.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = F x
    let possible := fun s : ℕ => ∃ D : Circuit, works D ∧ D.size = s
    have proofC : works C := by
      refine ⟨fan,?_⟩
      intro x
      by_contra e
      apply no
      refine ⟨x,?_⟩
      intro exactResult
      apply e
      exact exactResult.trans (same x)
    have ex : ∃ s, possible s := ⟨C.size,C,proofC,rfl⟩
    obtain ⟨D,hd,sz⟩ := Nat.find_spec ex
    have least (E : Circuit) (hE : works E) : D.size ≤ E.size := by
      rw [sz]
      exact Nat.find_min' ex ⟨E,hE,rfl⟩
    have small := (least C proofC).trans budget
    by_cases ao : AndOrOnly D
    · by_cases pair : PEqualNP.TopForm.andPairs 11 D = 0
      · have h := flatProof D σ f hd.1 ao pair hd.2
        omega
      · have h := nested σ f D hd least ao (Nat.pos_of_ne_zero pair)
        omega
    · have inv : ∃ g ∈ D.gates, g.op = GateOp.not := by
        by_contra h
        apply ao
        intro g hg
        have op := (hd.1 g hg).1
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op
        rcases op with eq | eq | eq
        · exact Or.inl eq
        · exact Or.inr eq
        · exact False.elim (h ⟨g,hg,eq⟩)
      have h := negated σ f D hd least inv
      omega
  let SideBank (k : ℕ) (bank : Finset (Finset (Fin 10))) : Prop :=
    ∀ P : ℕ → Finset (Finset (Fin 10)) → Prop,
      (∀ bank, (∀ s ∈ bank, s.card ≤ 1) → P 0 bank) →
      (∀ k bank, P k bank → ∀ (a b : Finset (Fin 10)), a ∈ bank → b ∈ bank →
        P (k+1) (insert (a ∪ b) bank)) → P k bank
  have SBinputs (bank : Finset (Finset (Fin 10))) (small : ∀ s ∈ bank, s.card ≤ 1) :
      SideBank 0 bank := fun P base step => base bank small
  have SBjoin {k bank} (prior : SideBank k bank) (a b : Finset (Fin 10))
      (ha : a ∈ bank) (hb : b ∈ bank) : SideBank (k+1) (insert (a ∪ b) bank) :=
    fun P base step => step k bank (prior P base step) a b ha hb
  let obligations (q : Finset (Fin 10 × Finset (Fin 10))) : Finset ((Fin 10) × (Fin 10)) :=
    q.biUnion fun p => p.2.image (Prod.mk p.1)
  have mem_obligations (q : Finset (Fin 10 × Finset (Fin 10))) (i j : (Fin 10)) :
      (i,j) ∈ obligations q ↔ ∃ s, (i,s) ∈ q ∧ j ∈ s := by
    simp [obligations, Finset.mem_biUnion, Finset.mem_image, Prod.exists]
  have tiny (q : Finset (Fin 10 × Finset (Fin 10))) (small : ∀ p ∈ q, p.2.card ≤ 1) :
      (obligations q).card ≤ q.card := by
    calc
      (obligations q).card ≤ ∑ p ∈ q, (p.2.image (Prod.mk p.1)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ q, 1 := Finset.sum_le_sum fun p hp =>
        Finset.card_image_le.trans (small p hp)
      _ = q.card := by simp
  -- Trace requests for star sides backwards through shared unions. In the Petersen graph a side
  -- with two distinct vertices belongs to at most one neighborhood, so a union is charged once.
  have shared_sides (N : (Fin 10) → (Finset (Fin 10)))
      (unique : ∀ i j s, s ⊆ N i → s ⊆ N j → 2 ≤ s.card → i = j)
      {k bank} (reachable : SideBank k bank) (q : Finset (Fin 10 × Finset (Fin 10)))
      (available : ∀ p ∈ q, p.2 ∈ bank ∨ p.2.card ≤ 1)
      (valid : ∀ p ∈ q, p.2 ⊆ N p.1) : (obligations q).card ≤ q.card + k := by
    classical
    revert q
    apply reachable (fun k bank => ∀ q : Finset (Fin 10 × Finset (Fin 10)),
      (∀ p ∈ q, p.2 ∈ bank ∨ p.2.card ≤ 1) →
      (∀ p ∈ q, p.2 ⊆ N p.1) → (obligations q).card ≤ q.card + k)
    · intro bank small q available valid
      simpa using tiny q (fun p hp => (available p hp).elim (small _) id)
    · intro k bank ih a b ha hb q available valid
      by_cases present : ∃ i, (i,a ∪ b) ∈ q ∧ 2 ≤ (a ∪ b).card
      · obtain ⟨i,hi,large⟩ := present
        let rest := q.erase (i,a ∪ b)
        let fresh := insert (i,a) (insert (i,b) rest)
        have inside := valid (i, a ∪ b) hi
        have old (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ rest) : p ∈ q := Finset.mem_of_mem_erase hp
        have restAvail (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ rest) : p.2 ∈ bank ∨ p.2.card ≤ 1 := by
          rcases available p (old p hp) with h | h
          · rcases Finset.mem_insert.mp h with e | ok
            · have same := unique p.1 i p.2 (valid p (old p hp)) (e ▸ inside) (e ▸ large)
              exact False.elim ((Finset.mem_erase.mp hp).1 (Prod.ext same e))
            · exact Or.inl ok
          · exact Or.inr h
        have av (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ fresh) : p.2 ∈ bank ∨ p.2.card ≤ 1 := by
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Or.inl ha
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Or.inl hb
          exact restAvail _ hp
        have va (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ fresh) : p.2 ⊆ N p.1 := by
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Finset.Subset.trans Finset.subset_union_left inside
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact Finset.Subset.trans Finset.subset_union_right inside
          exact valid _ (old _ hp)
        have cover : obligations q ⊆ obligations fresh := by
          rintro ⟨c,v⟩ hv
          obtain ⟨s,hs,hv⟩ := (mem_obligations q c v).mp hv
          apply (mem_obligations fresh c v).mpr
          by_cases eq : (c,s) = (i,a ∪ b)
          · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
            rcases Finset.mem_union.mp hv with h | h
            · exact ⟨a, by simp [fresh], h⟩
            · exact ⟨b, by simp [fresh], h⟩
          · exact ⟨s, by simp [fresh, rest, eq, hs], hv⟩
        have cut : rest.card + 1 = q.card := Finset.card_erase_add_one hi
        have add1 := Finset.card_insert_le (i,b) rest
        have add2 := Finset.card_insert_le (i,a) (insert (i,b) rest)
        have count := (Finset.card_le_card cover).trans (ih fresh av va)
        change _ ≤ (insert (i,a) (insert (i,b) rest)).card + k at count
        omega
      · have av (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ q) : p.2 ∈ bank ∨ p.2.card ≤ 1 := by
          rcases available p hp with h | h
          · rcases Finset.mem_insert.mp h with e | h
            · right
              by_contra! large
              apply present
              exact ⟨p.1, by simpa [← e] using hp, by rw [← e]; omega⟩
            · exact Or.inl h
          · exact Or.inr h
        exact (ih q av valid).trans (by omega)
  let edges : Finset ((Fin 10) × (Fin 10)) :=
    {(0,1),(1,2),(2,3),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),
     (5,7),(7,9),(6,9),(6,8),(5,8)}
  let undirected (e : (Fin 10) × (Fin 10)) : (Fin 10) × (Fin 10) := (min e.1 e.2, max e.1 e.2)
  let neighbors (i : (Fin 10)) : (Finset (Fin 10)) := Finset.univ.filter fun j => undirected (i,j) ∈ edges
  have unique_star (i j : (Fin 10)) (s : (Finset (Fin 10))) (hi : s ⊆ neighbors i)
      (hj : s ⊆ neighbors j) (large : 2 ≤ s.card) : i = j := by
    have cap : ∀ u v : (Fin 10), u ≠ v → ((neighbors u) ∩ (neighbors v)).card ≤ 1 := by
      decide +kernel
    by_contra ne
    have le := Finset.card_le_card (Finset.subset_inter hi hj)
    have small := cap i j ne
    omega
  have cover_size : ∀ s : Finset (Fin 10), (∀ p ∈ edges, p.1 ∈ s ∨ p.2 ∈ s) → 6 ≤ s.card := by
    decide +kernel
  -- The stars cover fifteen edges and need at least six centers.
  have layer_cost {k bank} (reachable : SideBank k bank) (q : Finset (Fin 10 × Finset (Fin 10)))
      (available : ∀ p ∈ q, p.2 ∈ bank ∨ p.2.card ≤ 1)
      (valid : ∀ p ∈ q, p.2 ⊆ neighbors p.1)
      (covers : edges ⊆ (obligations q).image undirected) :
      20 ≤ k + q.card + (q.card - 1) := by
    have bound := shared_sides neighbors unique_star reachable q available valid
    have ecount : edges.card = 15 := by decide
    have e15 := (Finset.card_le_card covers).trans Finset.card_image_le
    have cc : ∀ p ∈ edges, p.1 ∈ q.image Prod.fst ∨ p.2 ∈ q.image Prod.fst := by
      intro p hp
      obtain ⟨⟨c,v⟩,hv,rfl⟩ := Finset.mem_image.mp (covers hp)
      obtain ⟨s,hs,_⟩ := (mem_obligations q c v).mp hv
      have h : c ∈ q.image Prod.fst := Finset.mem_image.mpr ⟨(c,s),hs,rfl⟩
      by_cases le : c ≤ v
      · left; simpa [undirected, min_eq_left le] using h
      · right; simpa [undirected, max_eq_left (le_of_not_ge le)] using h
    have six := (cover_size _ cc).trans Finset.card_image_le
    omega
  let onSide (a : (Finset (Fin 10) × Bool)) (x : (Finset (Fin 10))) : Prop :=
    (∃ i ∈ a.1, i ∈ x) ∨ (a.2 = true ∧ (0 : (Fin 10)) ∉ x)
  let onTerm (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (x : (Finset (Fin 10))) : Prop := onSide t.1 x ∧ onSide t.2 x
  let edgeOn (x : (Finset (Fin 10))) : Prop := ∃ e ∈ edges, e.1 ∈ x ∧ e.2 ∈ x
  let Safe (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) : Prop := ∀ x, onTerm t x → edgeOn x
  have pair_edge : ∀ i j : (Fin 10), edgeOn {i,j} ↔ undirected (i,j) ∈ edges := by
    unfold edgeOn; decide +kernel
  have no_single : ∀ i : (Fin 10), ¬ edgeOn {i} := by unfold edgeOn; decide +kernel
  have no_empty : ¬ edgeOn ∅ := by unfold edgeOn; decide
  -- The empty input and singleton inputs force every active product to have a positive witness
  -- in both factors, even when a factor can also read the complement of input zero.
  have drop_negative {a b : (Finset (Fin 10) × Bool)} {x : (Finset (Fin 10))} (good : Safe (a,b))
      (onA : onSide a x) (onB : onSide b x) : ∃ i ∈ a.1, i ∈ x := by
    rcases onA with h | ⟨na,nx⟩
    · exact h
    rcases onB with ⟨j,jb,jx⟩ | ⟨nb,_⟩
    · have ne : (0 : (Fin 10)) ≠ j := fun eq => nx (eq ▸ jx)
      exact False.elim (no_single j (good {j}
        ⟨Or.inr ⟨na,by simpa using ne⟩, Or.inl ⟨j,jb,by simp⟩⟩))
    · exact False.elim (no_empty (good ∅ ⟨Or.inr ⟨na,by simp⟩, Or.inr ⟨nb,by simp⟩⟩))
  have cross {t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))} (good : Safe t) {i j : (Fin 10)} (ia : i ∈ t.1.1) (jb : j ∈ t.2.1) :
      undirected (i,j) ∈ edges := (pair_edge i j).mp (good {i,j}
        ⟨Or.inl ⟨i,ia,by simp⟩, Or.inl ⟨j,jb,by simp⟩⟩)
  have swap_undirected (a b : (Fin 10)) : undirected (a,b) = undirected (b,a) := by
    simp [undirected, min_comm, max_comm]
  have factor_star (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (good : Safe t) (useful : ∃ x, onTerm t x) :
      (∃ i, t.1.1 = {i} ∧ t.2.1 ⊆ neighbors i) ∨
      (∃ i, t.2.1 = {i} ∧ t.1.1 ⊆ neighbors i) := by
    obtain ⟨x,hx⟩ := useful
    have back : Safe (t.2,t.1) := fun y hk => good y ⟨hk.2,hk.1⟩
    obtain ⟨a,ha,_⟩ := drop_negative good hx.1 hx.2
    obtain ⟨b,hb,_⟩ := drop_negative back hx.2 hx.1
    have rightN (u : (Fin 10)) (hu : u ∈ t.1.1) : t.2.1 ⊆ neighbors u := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross good hu hv⟩
    have leftN (v : (Fin 10)) (hv : v ∈ t.2.1) : t.1.1 ⊆ neighbors v := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [swap_undirected]; exact cross good hu hv⟩
    by_cases large : 2 ≤ t.2.1.card
    · left
      refine ⟨a,Finset.ext fun j => ?_,rightN a ha⟩
      simp only [Finset.mem_singleton]
      exact ⟨fun h => unique_star j a _ (rightN j h) (rightN a ha) large,fun e => e ▸ ha⟩
    · right
      obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show t.2.1.card = 1 by
        have := Finset.card_pos.mpr (show t.2.1.Nonempty from ⟨b,hb⟩)
        omega)
      exact ⟨v,hv,leftN v (by simp [hv])⟩
  let Star (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (d : (Fin 10 × Finset (Fin 10))) : Prop :=
    (t.1.1 = {d.1} ∧ t.2.1 = d.2) ∨ (t.2.1 = {d.1} ∧ t.1.1 = d.2)
  have star_exists (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (good : Safe t) (useful : ∃ x, onTerm t x) :
      ∃ d, Star t d ∧ d.2 ⊆ neighbors d.1 := by
    rcases factor_star t good useful with ⟨i,h,sub⟩ | ⟨i,h,sub⟩
    · exact ⟨(i,t.2.1), Or.inl ⟨h,rfl⟩, sub⟩
    · exact ⟨(i,t.1.1), Or.inr ⟨h,rfl⟩, sub⟩
  have edge_id : ∀ e ∈ edges, ∀ i ∈ ({e.1,e.2} : (Finset (Fin 10))), ∀ j ∈ ({e.1,e.2} : (Finset (Fin 10))),
      undirected (i,j) ∈ edges → undirected (i,j) = e := by decide +kernel
  have hit_star {t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))} {d : (Fin 10 × Finset (Fin 10))} (good : Safe t) (star : Star t d)
      {e : (Fin 10) × (Fin 10)} (he : e ∈ edges) (hit : onTerm t {e.1,e.2}) :
      ∃ v ∈ d.2, undirected (d.1,v) = e := by
    have back : Safe (t.2,t.1) := fun y hk => good y ⟨hk.2,hk.1⟩
    obtain ⟨a,ia,ha⟩ := drop_negative good hit.1 hit.2
    obtain ⟨b,ib,hb⟩ := drop_negative back hit.2 hit.1
    have eq := edge_id e he a ha b hb (cross good ia ib)
    rcases star with ⟨one,rest⟩ | ⟨one,rest⟩
    · have ac : a = d.1 := Finset.mem_singleton.mp (one ▸ ia)
      exact ⟨b,rest ▸ ib, ac ▸ eq⟩
    · have bc : b = d.1 := Finset.mem_singleton.mp (one ▸ ib)
      exact ⟨a,rest ▸ ia, bc ▸ ((swap_undirected b a).trans eq)⟩
  have signed_layer {k bank} (reachable : SideBank k bank) (terms : Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool)))
      (available : ∀ t ∈ terms, t.1.1 ∈ bank ∧ t.2.1 ∈ bank)
      (computes : ∀ x, (∃ t ∈ terms, onTerm t x) ↔ edgeOn x) :
      20 ≤ k + terms.card + (terms.card - 1) := by
    classical
    let used := terms.filter fun t => ∃ x, onTerm t x
    have useful (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (ht : t ∈ used) : ∃ x, onTerm t x := (Finset.mem_filter.mp ht).2
    have live (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (ht : t ∈ used) : t ∈ terms := (Finset.mem_filter.mp ht).1
    have good (t : ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (ht : t ∈ terms) : Safe t := fun x h => (computes x).mp ⟨t,ht,h⟩
    have existsD (t : used) := star_exists t.val (good _ (live _ t.property)) (useful _ t.property)
    choose rep hstar hsub using existsD
    let q : Finset (Fin 10 × Finset (Fin 10)) := used.attach.image rep
    have memQ (t : used) : rep t ∈ q := Finset.mem_image.mpr ⟨t,Finset.mem_attach _ _,rfl⟩
    have valid (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ q) : p.2 ⊆ neighbors p.1 := by
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hp
      exact hsub t
    have av (p : (Fin 10 × Finset (Fin 10))) (hp : p ∈ q) : p.2 ∈ bank ∨ p.2.card ≤ 1 := by
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hp
      have hv := available _ (live _ t.property)
      left
      rcases hstar t with ⟨_,h⟩ | ⟨_,h⟩
      · exact h ▸ hv.2
      · exact h ▸ hv.1
    have hits : edges ⊆ (obligations q).image undirected := by
      intro e he
      have edge : edgeOn {e.1,e.2} := ⟨e,he,by simp,by simp⟩
      obtain ⟨t,ht,hit⟩ := (computes _).mpr edge
      let w : used := ⟨t,Finset.mem_filter.mpr ⟨ht,_,hit⟩⟩
      obtain ⟨v,hv,eq⟩ := hit_star (good _ ht) (hstar w) he hit
      exact Finset.mem_image.mpr ⟨((rep w).1,v),
        (mem_obligations _ _ _).mpr ⟨(rep w).2,memQ w,hv⟩,eq⟩
    have cost := layer_cost reachable q av valid hits
    have le : q.card ≤ terms.card := by
      calc
        q.card ≤ used.attach.card := Finset.card_image_le
        _ = used.card := Finset.card_attach
        _ ≤ terms.card := Finset.card_filter_le _ _
    omega
  let OrBank (k : ℕ) (bank : Finset (Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool)))) : Prop :=
    ∀ P : ℕ → Finset (Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) → Prop,
      (∀ bank, (∀ s ∈ bank, s.card ≤ 1) → P 0 bank) →
      (∀ k bank, P k bank → ∀ (a b : Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))), a ∈ bank → b ∈ bank →
        P (k+1) (insert (a ∪ b) bank)) → P k bank
  have OBinputs (bank : Finset (Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool)))) (small : ∀ s ∈ bank, s.card ≤ 1) :
      OrBank 0 bank := fun P base step => base bank small
  have OBjoin {k bank} (prior : OrBank k bank) (a b : Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool)))
      (ha : a ∈ bank) (hb : b ∈ bank) : OrBank (k+1) (insert (a ∪ b) bank) :=
    fun P base step => step k bank (prior P base step) a b ha hb
  -- A shared upper network needs at least one fewer union than the number of products it joins.
  have or_union_bound {k bank} (reach : OrBank k bank)
      (q : Finset (Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool)))) (avail : ∀ s ∈ q, s ∈ bank ∨ s.card ≤ 1) :
      (q.biUnion id).card ≤ q.card + k := by
    revert q
    apply reach (fun k bank => ∀ q : Finset (Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))),
      (∀ s ∈ q, s ∈ bank ∨ s.card ≤ 1) → (q.biUnion id).card ≤ q.card + k)
    · intro bank small q avail
      calc
        (q.biUnion id).card ≤ ∑ s ∈ q, s.card := Finset.card_biUnion_le
        _ ≤ ∑ _s ∈ q, 1 := Finset.sum_le_sum fun s hs => (avail s hs).elim (small s) id
        _ = q.card + 0 := by simp
    · intro k bank ih a b ha hb q avail
      by_cases present : a ∪ b ∈ q
      · let rest := q.erase (a ∪ b)
        let replaced := insert a (insert b rest)
        have before : ∀ s ∈ replaced, s ∈ bank ∨ s.card ≤ 1 := by
          intro s h
          rcases Finset.mem_insert.mp h with rfl | h
          · exact Or.inl ha
          rcases Finset.mem_insert.mp h with rfl | h
          · exact Or.inl hb
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp h
          rcases avail s mem with h | h
          · exact Or.inl ((Finset.mem_insert.mp h).resolve_left ne)
          · exact Or.inr h
        have preserves : q.biUnion id ⊆ replaced.biUnion id := by
          intro v hv
          obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
          apply Finset.mem_biUnion.mpr
          by_cases eq : s = a ∪ b
          · subst s
            rcases Finset.mem_union.mp hv with h | h
            · exact ⟨a, by simp [replaced], h⟩
            · exact ⟨b, by simp [replaced], h⟩
          · exact ⟨s, by simp [replaced, rest, eq, hs], hv⟩
        have shrinks : rest.card + 1 = q.card := Finset.card_erase_add_one present
        have badds := Finset.card_insert_le b rest
        have aadds := Finset.card_insert_le a (insert b rest)
        have total := (Finset.card_le_card preserves).trans (ih replaced before)
        change _ ≤ (insert a (insert b rest)).card + k at total
        omega
      · have before : ∀ s ∈ q, s ∈ bank ∨ s.card ≤ 1 := by
          intro s hs
          rcases avail s hs with h | h
          · rcases Finset.mem_insert.mp h with rfl | h
            · exact False.elim (present hs)
            · exact Or.inl h
          · exact Or.inr h
        exact (ih q before).trans (by omega)
  have or_root_bound {k bank} (reach : OrBank k bank)
      (s : Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (out : s ∈ bank ∨ s.card ≤ 1) : s.card ≤ k + 1 := by
    have result := or_union_bound reach {s} (by simpa using out)
    simpa [Nat.add_comm] using result
  let bit (x : (Finset (Fin 10))) (i : (Fin 10)) : Bool := decide (i ∈ x)
  let raw (i : (Fin 10)) : (Finset (Fin 10) × Bool) := ({i},false)
  let auxiliary (f : Bool → Bool) : (Finset (Fin 10) × Bool) := (if f true then {0} else ∅,f false)
  let inputData (σ : (Fin 10) → (Fin 10)) (f : Bool → Bool) : List ((Finset (Fin 10) × Bool) × Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) :=
    List.ofFn (fun i => (raw (σ i), ∅)) ++ [(auxiliary f, ∅)]
  have raw_signal (x : (Finset (Fin 10))) (i : (Fin 10)) : onSide (raw i) x ↔ bit x i = true := by
    simp [onSide,raw,bit]
  have auxiliary_signal (x : (Finset (Fin 10))) (f : Bool → Bool) :
      onSide (auxiliary f) x ↔ f (bit x 0) = true := by
    by_cases h : (0 : (Fin 10)) ∈ x <;> cases hf : f true <;> cases hf' : f false <;>
      simp [onSide,auxiliary,bit,h,hf,hf']
  have inputs_pure (σ : (Fin 10) → (Fin 10)) (f : Bool → Bool) (w : (Finset (Fin 10) × Bool) × Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool)))
      (hw : w ∈ inputData σ f) : w.2 = ∅ ∧ w.1.1.card ≤ 1 := by
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      simp [raw]
    · obtain rfl : w = (auxiliary f,∅) := by simpa using h
      cases h : f true <;> simp [auxiliary,h]
  let target (x : (Fin 10) → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have target_eq : ∀ x : (Finset (Fin 10)), target (bit x) = true ↔ edgeOn x := by
    unfold edgeOn
    decide +kernel
  have root_cost {k j bank upper} (lo : SideBank k bank) (hi : OrBank j upper)
      (s : (Finset (Fin 10) × Bool)) (q t : Finset ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))) (hq : q ⊆ t) (out : q ∈ upper ∨ q.card ≤ 1)
      (available : ∀ w ∈ t, w.1.1 ∈ bank ∧ w.2.1 ∈ bank)
      (eval : ∀ x, (onSide s x ∨ ∃ w ∈ q, onTerm w x) ↔ edgeOn x) :
      20 ≤ k + t.card + j := by
    have noRaw (x : (Finset (Fin 10))) : ¬ onSide s x := by
      rintro (⟨i,hi,_⟩ | ⟨h,_⟩)
      · exact no_single i ((eval {i}).mp (Or.inl (Or.inl ⟨i,hi,by simp⟩)))
      · exact no_empty ((eval ∅).mp (Or.inl (Or.inr ⟨h,by simp⟩)))
    have computes (x : (Finset (Fin 10))) : (∃ w ∈ q, onTerm w x) ↔ edgeOn x := by
      simpa [noRaw x] using eval x
    have bound := signed_layer lo q (fun w hw => available w (hq hw)) computes
    have top := or_root_bound hi q out
    have terms := Finset.card_le_card hq
    omega
  let V := (Fin 10)
  let Side := (Finset (Fin 10))
  let Demand := (Fin 10 × Finset (Fin 10))
  let Signed := (Finset (Fin 10) × Bool)
  let Term := ((Finset (Fin 10) × Bool) × (Finset (Fin 10) × Bool))
  let Wire := Signed × Finset Term

  let zeroWire : Wire := ((∅, false), ∅)
  let oneWire : Wire := (({0}, true), ∅)

  let wireOn (w : Wire) (x : Side) : Prop :=
    onSide w.1 x ∨ ∃ t ∈ w.2, onTerm t x

  let joinWire (a b : Wire) : Wire :=
    ((a.1.1 ∪ b.1.1, a.1.2 || b.1.2), a.2 ∪ b.2)

  let termWire (a b : Wire) : Wire :=
    ((∅, false), {(a.1,b.1)})

  -- Interpret each wire as a disjunction of raw literals and products of two literal disjunctions.
  let flatOp (op : GateOp) (xs : List Wire) : Option Wire :=
    GateOp.casesOn (motive := fun _ => Option Wire) op
      (List.casesOn (motive := fun _ => Option Wire) xs (some oneWire) (fun a ys =>
      List.casesOn (motive := fun _ => Option Wire) ys (some a) (fun b zs =>
        List.casesOn (motive := fun _ => Option Wire) zs (if a.2 = ∅ ∧ b.2 = ∅ then some (termWire a b) else none) (fun _ _ => none))))
      (List.casesOn (motive := fun _ => Option Wire) xs (some zeroWire) (fun a ys =>
      List.casesOn (motive := fun _ => Option Wire) ys (some a) (fun b zs =>
        List.casesOn (motive := fun _ => Option Wire) zs (some (joinWire a b)) (fun _ _ => none)))) none (fun _ => none) none

  let flatGate (g : Gate) (w : List Wire) : Option Wire :=
    flatOp g.op (g.inputs.map fun i => w.getD i zeroWire)

  let runFlat (gs : List Gate) : List Wire → Option (List Wire) :=
    gs.foldr (fun g (tail : List Wire → Option (List Wire)) w =>
      (flatGate g w).bind (fun v => tail (w ++ [v]))) (fun w => some w)
  have runFlat_nil (w : List Wire) : runFlat [] w = some w := rfl
  have runFlat_cons (g : Gate) (gs : List Gate) (w : List Wire) :
      runFlat (g :: gs) w = (flatGate g w).bind (fun v => runFlat gs (w ++ [v])) := rfl

  have zero_off (x : Side) : ¬ wireOn zeroWire x := by
    simp [wireOn, zeroWire, onSide] <;> intro i hi <;> exact (Finset.notMem_empty _ hi).elim

  have one_on (x : Side) : wireOn oneWire x := by
    by_cases h : (0 : V) ∈ x <;> simp [wireOn, oneWire, onSide, h] <;> exact ⟨0,Finset.mem_singleton_self _,h⟩

  have raw_union (a b x : Side) : (∃ i ∈ a ∪ b, i ∈ x) ↔ (∃ i ∈ a, i ∈ x) ∨ ∃ i ∈ b, i ∈ x := by
    constructor
    · rintro ⟨i,hi,hx⟩
      rcases Finset.mem_union.mp hi with h | h
      · exact Or.inl ⟨i,h,hx⟩
      · exact Or.inr ⟨i,h,hx⟩
    · rintro (⟨i,h,hx⟩ | ⟨i,h,hx⟩)
      · exact ⟨i,Finset.mem_union_left _ h,hx⟩
      · exact ⟨i,Finset.mem_union_right _ h,hx⟩

  have join_on (a b : Wire) (x : Side) :
      wireOn (joinWire a b) x ↔ wireOn a x ∨ wireOn b x := by
    simp only [wireOn, joinWire, onSide, raw_union, Finset.mem_union, Bool.or_eq_true, or_and_right, exists_or]
    constructor
    · rintro (((ha | hb) | hc | hd) | he | hf)
      · exact Or.inl (Or.inl (Or.inl ha))
      · exact Or.inr (Or.inl (Or.inl hb))
      · exact Or.inl (Or.inl (Or.inr hc))
      · exact Or.inr (Or.inl (Or.inr hd))
      · exact Or.inl (Or.inr he)
      · exact Or.inr (Or.inr hf)
    · rintro (((ha | hc) | he) | (hb | hd) | hf)
      · exact Or.inl (Or.inl (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inl he)
      · exact Or.inl (Or.inl (Or.inr hb))
      · exact Or.inl (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr hf)

  have term_on (a b : Wire) (x : Side) (ha : a.2 = ∅) (hb : b.2 = ∅) :
      wireOn (termWire a b) x ↔ wireOn a x ∧ wireOn b x := by
    simp [wireOn, termWire, onSide, onTerm, ha, hb] <;> intro i hi <;> exact (Finset.notMem_empty _ hi).elim

  let wireVal (x : Side) (w : Wire) : Bool := by
    classical
    exact decide (wireOn w x)

  have wireVal_iff (x : Side) (w : Wire) : wireVal x w = true ↔ wireOn w x := by
    classical
    simp [wireVal]

  have zero_val (x : Side) : wireVal x zeroWire = false := by
    cases h : wireVal x zeroWire
    · rfl
    · exact False.elim (zero_off x ((wireVal_iff x _).mp h))

  have value_and (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have value_or (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl

  have flatOp_value {op : GateOp} {args : List Wire} {v : Wire}
      (h : flatOp op args = some v) (x : Side) :
      wireVal x v = op.eval (args.map (wireVal x)) := by
    classical
    cases args with
    | nil =>
      cases op <;> simp [flatOp] at h <;> subst v
      · simp [value_and, value_or, (wireVal_iff _ _).mpr (one_on x)]
      · simp [value_and, value_or, zero_val]
    | cons a rest =>
      cases rest with
      | nil =>
        cases op <;> simp [flatOp] at h <;> subst v <;> simp [value_and, value_or]
      | cons b rest =>
        cases rest with
        | nil =>
          cases op with
          | and =>
            by_cases pure : a.2 = ∅ ∧ b.2 = ∅
            · simp [flatOp, pure] at h
              subst v
              rw [Bool.eq_iff_iff,wireVal_iff, term_on _ _ _ pure.1 pure.2]
              simp [value_and, value_or, wireVal_iff]
            · simp [flatOp,pure] at h
          | or =>
            simp [flatOp] at h
            subst v
            rw [Bool.eq_iff_iff,wireVal_iff,join_on]
            simp [value_and, value_or,wireVal_iff]
          | _ => simp [flatOp] at h
        | cons c cs => cases op <;> simp [flatOp] at h

  have map_getD (w : List Wire) (x : Side) (i : ℕ) :
      (w.map (wireVal x)).getD i false = wireVal x (w.getD i zeroWire) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, ← zero_val x, Option.getD_map]

  have runFlat_value (gs : List Gate) (w w' : List Wire) (ok : runFlat gs w = some w')
      (x : Side) :
      (Circuit.mk gs 0).wires (w.map (wireVal x)) = w'.map (wireVal x) := by
    induction gs generalizing w w' with
    | nil =>
      change w.map (wireVal x) = w'.map (wireVal x)
      exact congrArg (List.map (wireVal x)) (Option.some.inj ok)
    | cons g gs ih =>
      cases hg : flatGate g w with
      | none => simp [runFlat,hg] at ok
      | some v =>
        simp [runFlat,hg] at ok
        have value := flatOp_value (op := g.op) (args := g.inputs.map (fun i => w.getD i zeroWire)) hg x
        change (Circuit.mk gs 0).wires ((w.map (wireVal x)) ++ [g.op.eval
          (g.inputs.map fun i => (w.map (wireVal x)).getD i false)]) = _
        rw [← ih _ _ ok]
        simp only [List.map_append,List.map_cons,List.map_nil,List.map_map, Function.comp_def] at value ⊢
        simp_rw [map_getD]
        rw [value]


  have coneAppend (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      ∃ rest, gs.foldl (coneStep n) cs = cs ++ rest := by
    induction gs generalizing cs with
    | nil => exact ⟨[], by simp⟩
    | cons g gs ih =>
      obtain ⟨t,ht⟩ := ih (coneStep n cs g)
      rw [List.foldl_cons, ht]
      unfold coneStep
      exact ⟨_, List.append_assoc ..⟩

  have snocOld {α : Type} (l : List α) (x d : α) (i : ℕ) (h : i ≠ l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    by_cases hi : i < l.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have noPair {C : Circuit} {n a b : ℕ} (none : PEqualNP.TopForm.andPairs n C = 0)
      (ha : a < C.gates.length) (hb : b < C.gates.length) (aa : (gateAt C a).op = .and)
      (ab : (gateAt C b).op = .and) (anc : InCone n C a b) : False := by
    letI : DecidableEq GateOp := gateOpDecEq
    unfold PEqualNP.TopForm.andPairs at none
    apply (Finset.eq_empty_iff_forall_notMem.mp (Finset.card_eq_zero.mp none)) (a,b)
    exact Finset.mem_filter.mpr ⟨by simp [ha,hb],aa,ab,anc⟩

  have flatProduces (g : Gate) (w : List Wire) (hop : g.op = .and ∨ g.op = .or)
      (size : g.inputs.length ≤ 2)
      (clean : g.op = .and → ∀ i ∈ g.inputs, (w.getD i zeroWire).2 = ∅) :
      ∃ a, flatGate g w = some a ∧ (a.2 ≠ ∅ → g.op = .and ∨ ∃ i ∈ g.inputs, (w.getD i zeroWire).2 ≠ ∅) := by
    obtain ⟨op,ins⟩ := g
    change op = .and ∨ op = .or at hop
    change op = .and → ∀ i ∈ ins, (w.getD i zeroWire).2 = ∅ at clean
    change ins.length ≤ 2 at size
    rcases hop with rfl | rfl
    · cases ins with
      | nil => exact ⟨_,rfl,fun _ => Or.inl rfl⟩
      | cons i is => cases is with
        | nil => exact ⟨_,rfl,fun _ => Or.inl rfl⟩
        | cons j js => cases js with
          | nil =>
            refine ⟨termWire (w.getD i zeroWire) (w.getD j zeroWire), ?_, fun _ => Or.inl rfl⟩
            change (if (w.getD i zeroWire).2 = ∅ ∧ (w.getD j zeroWire).2 = ∅ then _ else _) = _
            rw [if_pos ⟨clean rfl i (by simp),clean rfl j (by simp)⟩]
          | cons k ks => simp at size
    · cases ins with
      | nil => exact ⟨_,rfl,fun h => (h rfl).elim⟩
      | cons i is => cases is with
        | nil => exact ⟨_,rfl,fun h => Or.inr ⟨i,by simp,h⟩⟩
        | cons j js => cases js with
          | nil =>
            refine ⟨_,rfl,fun h => Or.inr ?_⟩
            by_cases hi : (w.getD i zeroWire).2 = ∅
            · exact ⟨j,by simp,fun hj => h (by
                change (w.getD i zeroWire).2 ∪ (w.getD j zeroWire).2 = ∅
                rw [hi,hj,Finset.empty_union])⟩
            · exact ⟨i,by simp,hi⟩
          | cons k ks => simp at size

  let prior (n : ℕ) (C : Circuit) (cs : List (List ℕ)) (w : List Wire) : Prop :=
    ∀ i, (w.getD i zeroWire).2 ≠ ∅ → n ≤ i ∧ i < n + cs.length ∧
      ∃ a < cs.length, (gateAt C a).op = .and ∧ (a = i - n ∨ a ∈ cs.getD (i - n) [])

  -- A failed product expansion would exhibit an earlier AND in the cone of the present AND.
  have flatFinish (n : ℕ) (C : Circuit) (fan : FanInTwo C)
      (mono : AndOrOnly C) (none : PEqualNP.TopForm.andPairs n C = 0) (gs : List Gate) :
      ∀ (pre : List Gate) (cs : List (List ℕ)) (w : List Wire),
      C.gates = pre ++ gs → cs = pre.foldl (coneStep n) [] →
      cs.length = pre.length → w.length = n + cs.length →
      prior n C cs w → ∃ out, runFlat gs w = some out := by
    induction gs with
    | nil => intro pre cs w _ _ _ _ _; exact ⟨_,rfl⟩
    | cons g gs ih =>
      intro pre cs w hfull hcs hlen hw hp
      have ing : g ∈ C.gates := by simp [hfull]
      have now : gateAt C cs.length = g := by
        change C.gates.getD cs.length _ = g
        simp [hlen,hfull,List.getD_eq_getElem?_getD]
      let ag := (g.inputs.filter fun i => decide (n ≤ i ∧ i < n + cs.length)).flatMap
        (fun i => (i - n) :: cs.getD (i - n) [])
      have extend : coneStep n cs g = cs ++ [ag] := rfl
      have closed : ∃ t, cones n C = (cs ++ [ag]) ++ t := by
        unfold cones
        rw [hfull, List.foldl_append, ←hcs, List.foldl_cons, ←extend]
        exact coneAppend n gs (coneStep n cs g)
      have transfer (a : ℕ) (ha : a ∈ ag) : InCone n C a cs.length := by
        obtain ⟨tail,ht⟩ := closed
        unfold InCone
        rw [ht, List.getD_append _ _ _ _ (by simp)]
        simpa using ha
      have source (i : ℕ) (hin : i ∈ g.inputs) (hit : (w.getD i zeroWire).2 ≠ ∅) :
          ∃ a < cs.length, (gateAt C a).op = .and ∧ a ∈ ag := by
        obtain ⟨lo,hi,a,ha,opa,mem⟩ := hp i hit
        refine ⟨a,ha,opa,List.mem_flatMap.mpr ⟨i, ?_, ?_⟩⟩
        · simp [hin,lo,hi]
        · exact List.mem_cons.mpr mem
      have clean (andG : g.op = .and) (i : ℕ) (hin : i ∈ g.inputs) : (w.getD i zeroWire).2 = ∅ := by
        by_contra hit
        obtain ⟨a,ha,opa,mem⟩ := source i hin hit
        have hj : cs.length < C.gates.length := by simp [hlen,hfull]
        exact noPair none (lt_trans ha hj) hj opa (now ▸ andG) (transfer a mem)
      obtain ⟨v,hv,taint⟩ := flatProduces g w (mono g ing) (fan g ing).2 clean
      have next : prior n C (cs ++ [ag]) (w ++ [v]) := by
        intro i hit
        by_cases new : i = w.length
        · subst i
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (le_refl _),
            Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] at hit
          have ev : v.2 ≠ ∅ := by simpa using hit
          have sub : w.length - n = cs.length := by omega
          refine ⟨by omega,by simp [hw],?_⟩
          rw [sub]
          rcases taint ev with op | ⟨r,hr,ht⟩
          · exact ⟨cs.length,by simp,now ▸ op,Or.inl rfl⟩
          · obtain ⟨a,ha,opa,mem⟩ := source r hr ht
            exact ⟨a,by simp; omega,opa,Or.inr (by simpa using mem)⟩
        · rw [snocOld _ _ _ _ new] at hit
          obtain ⟨lo,hi,a,ha,opa,mem⟩ := hp i hit
          refine ⟨lo,by simp; omega,a,by simp; omega,opa,?_⟩
          rw [List.getD_append _ _ _ _ (by omega)]
          exact mem
      have hpre : C.gates = (pre ++ [g]) ++ gs := by simpa [List.append_assoc] using hfull
      obtain ⟨out,hout⟩ := ih (pre ++ [g]) (cs ++ [ag]) (w ++ [v]) hpre
        (by simp [List.foldl_append, ← hcs, ← extend]) (by simp [hlen]) (by simp [hw, Nat.add_assoc]) next
      exact ⟨out,by simp [runFlat,hv,hout]⟩

  have ancestry_runFlat {n : ℕ} (C : Circuit) (fan : FanInTwo C) (mono : AndOrOnly C)
      (none : PEqualNP.TopForm.andPairs n C = 0) (inputs : List Wire) (hlen : inputs.length = n)
      (pure : ∀ a ∈ inputs, a.2 = ∅) : ∃ out, runFlat C.gates inputs = some out := by
    apply flatFinish n C fan mono none C.gates [] [] inputs (by simp) rfl rfl (by simpa using hlen)
    intro i hit
    by_cases hi : i < inputs.length
    · exact (hit (pure (inputs.getD i zeroWire) (by
        rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
        exact List.getElem_mem ..))).elim
    · rw [List.getD_eq_default _ _ (by omega)] at hit
      exact (hit rfl).elim


  -- Charge each gate to the lower unions, the individual products, or the upper unions.
  let Account := ℕ × ℕ × Finset Side × Finset (Finset Term) × Finset Term
  let cost (A : Account) := A.1 + A.2.2.2.2.card + A.2.1
  let Sound (A : Account) : Prop := SideBank A.1 A.2.2.1 ∧ OrBank A.2.1 A.2.2.2.1 ∧
    (∀ s : Side, s.card ≤ 1 → s ∈ A.2.2.1) ∧
    (∀ s : Finset Term, s.card ≤ 1 → s ∈ A.2.2.2.1) ∧
    (∀ t ∈ A.2.2.2.2, t.1.1 ∈ A.2.2.1 ∧ t.2.1 ∈ A.2.2.1)
  let Fits (A : Account) (v : Wire) : Prop :=
    (v.2 = ∅ → v.1.1 ∈ A.2.2.1) ∧ v.2 ∈ A.2.2.2.1 ∧ v.2 ⊆ A.2.2.2.2
  let Extends (B A : Account) : Prop :=
    A.2.2.1 ⊆ B.2.2.1 ∧ A.2.2.2.1 ⊆ B.2.2.2.1 ∧ A.2.2.2.2 ⊆ B.2.2.2.2
  have fit_move {A B : Account} {w : Wire} (h : Extends B A) (t : Fits A w) : Fits B w :=
    ⟨fun e => h.1 (t.1 e), h.2.1 t.2.1, t.2.2.trans h.2.2⟩

  have fit_small (A : Account) (snd : Sound A) (w : Wire) (h : w.1.1.card ≤ 1)
      (e : w.2 = ∅) : Fits A w := by
    exact ⟨fun _ => snd.2.2.1 _ h, e ▸ snd.2.2.2.1 ∅ (by simp), e ▸ Finset.empty_subset _⟩

  have keep_account {A : Account} (snd : Sound A) (w : Wire) (fit : Fits A w) :
      ∃ B : Account, Sound B ∧ Extends B A ∧ Fits B w ∧ cost B ≤ cost A + 1 :=
    ⟨A,snd,⟨fun _ h => h, fun _ h => h, fun _ h => h⟩,fit,by omega⟩

  have push_term {A : Account} (snd : Sound A) (a b : Wire) (fa : Fits A a) (fb : Fits A b)
      (pa : a.2 = ∅) (pb : b.2 = ∅) :
      ∃ B : Account, Sound B ∧ Extends B A ∧ Fits B (termWire a b) ∧ cost B ≤ cost A + 1 := by
    let t : Term := (a.1,b.1)
    let B : Account := (A.1,A.2.1,A.2.2.1,A.2.2.2.1,insert t A.2.2.2.2)
    refine ⟨B, ⟨snd.1,snd.2.1,snd.2.2.1,snd.2.2.2.1,?_⟩, ?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact ⟨fa.1 pa,fb.1 pb⟩
      · exact snd.2.2.2.2 _ hu
    · exact ⟨fun _ h => h,fun _ h => h,Finset.subset_insert _ _⟩
    · exact ⟨fun _ => snd.2.2.1 ∅ (by exact Nat.zero_le 1),snd.2.2.2.1 {t} (by simp),
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)⟩
    · have h := Finset.card_insert_le t A.2.2.2.2
      dsimp [cost,B]
      omega

  have push_join {A : Account} (snd : Sound A) (a b : Wire) (fa : Fits A a) (fb : Fits A b) :
      ∃ B : Account, Sound B ∧ Extends B A ∧ Fits B (joinWire a b) ∧ cost B ≤ cost A + 1 := by
    by_cases e : a.2 ∪ b.2 = ∅
    · have pa : a.2 = ∅ := (Finset.union_eq_empty.mp e).1
      have pb : b.2 = ∅ := (Finset.union_eq_empty.mp e).2
      let s := a.1.1 ∪ b.1.1
      let B : Account := (A.1+1,A.2.1,insert s A.2.2.1,A.2.2.2.1,A.2.2.2.2)
      refine ⟨B, ⟨SBjoin snd.1 _ _ (fa.1 pa) (fb.1 pb),snd.2.1,?_,snd.2.2.2.1,?_⟩, ?_, ?_, ?_⟩
      · intro u h
        exact Finset.mem_insert_of_mem (snd.2.2.1 u h)
      · intro t ht
        exact ⟨Finset.mem_insert_of_mem (snd.2.2.2.2 t ht).1,Finset.mem_insert_of_mem (snd.2.2.2.2 t ht).2⟩
      · exact ⟨Finset.subset_insert _ _,fun _ h => h,fun _ h => h⟩
      · exact ⟨fun _ => Finset.mem_insert_self _ _, (by change a.2 ∪ b.2 ∈ A.2.2.2.1; rw [e]; exact snd.2.2.2.1 ∅ (by simp)),
          Finset.union_subset fa.2.2 fb.2.2⟩
      · dsimp [cost,B]
        omega
    · let t := a.2 ∪ b.2
      let B : Account := (A.1,A.2.1+1,A.2.2.1,insert t A.2.2.2.1,A.2.2.2.2)
      refine ⟨B, ⟨snd.1,OBjoin snd.2.1 _ _ fa.2.1 fb.2.1,snd.2.2.1,?_,snd.2.2.2.2⟩, ?_, ?_, ?_⟩
      · intro u h
        exact Finset.mem_insert_of_mem (snd.2.2.2.1 u h)
      · exact ⟨fun _ h => h,Finset.subset_insert _ _,fun _ h => h⟩
      · exact ⟨fun eu => False.elim (e eu),Finset.mem_insert_self _ _,Finset.union_subset fa.2.2 fb.2.2⟩
      · dsimp [cost,B]
        omega

  have flat_account {A : Account} (snd : Sound A) {op : GateOp} {args : List Wire} {v : Wire}
      (valid : ∀ a ∈ args, Fits A a) (step : flatOp op args = some v) :
      ∃ B : Account, Sound B ∧ Extends B A ∧ Fits B v ∧ cost B ≤ cost A + 1 := by
    cases args with
    | nil =>
      cases op <;> simp [flatOp] at step <;> subst v <;> apply keep_account snd
      · exact fit_small A snd oneWire (by simp [oneWire]) rfl
      · exact fit_small A snd zeroWire (by simp [zeroWire]) rfl
    | cons a rest =>
      cases rest with
      | nil =>
        cases op <;> simp [flatOp] at step <;> subst v <;> exact keep_account snd a (valid a (by simp))
      | cons b rest =>
        cases rest with
        | nil =>
          cases op with
          | and =>
            by_cases p : a.2 = ∅ ∧ b.2 = ∅
            · simp [flatOp,p] at step
              subst v
              exact push_term snd _ _ (valid _ (by simp)) (valid _ (by simp)) p.1 p.2
            · simp [flatOp,p] at step
          | or =>
            simp [flatOp] at step
            subst v
            exact push_join snd _ _ (valid _ (by simp)) (valid _ (by simp))
          | _ => simp [flatOp] at step
        | cons c cs => cases op <;> simp [flatOp] at step

  have getD_fits (A : Account) (snd : Sound A) (ws : List Wire)
      (active : ∀ w ∈ ws, Fits A w) (i : ℕ) : Fits A (ws.getD i zeroWire) := by
    by_cases h : i < ws.length
    · rw [List.getD_eq_getElem _ _ h]
      exact active _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (show ws.length ≤ i by omega)]
      exact fit_small A snd zeroWire (by simp [zeroWire]) rfl

  have runFlat_account_aux (gs : List Gate) (w w' : List Wire) (ok : runFlat gs w = some w')
      (A : Account) (snd : Sound A) (fits : ∀ v ∈ w, Fits A v) :
      ∃ B : Account, Sound B ∧ (∀ v ∈ w', Fits B v) ∧ cost B ≤ cost A + gs.length := by
    induction gs generalizing w w' A with
    | nil =>
      have e : w = w' := Option.some.inj ok
      subst w'
      exact ⟨A,snd,fits,by simp⟩
    | cons g gs ih =>
      cases h : flatGate g w with
      | none => simp [runFlat,h] at ok
      | some v =>
        simp [runFlat,h] at ok
        have valid (z : Wire) (hz : z ∈ g.inputs.map (fun i => w.getD i zeroWire)) : Fits A z := by
          obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
          exact getD_fits A snd w fits i
        obtain ⟨B,bs,ext,fit,cost⟩ := flat_account snd valid h
        have newfits (z : Wire) (hz : z ∈ w ++ [v]) : Fits B z := by
          rcases List.mem_append.mp hz with old | last
          · exact fit_move ext (fits z old)
          · simpa using (List.mem_singleton.mp last) ▸ fit
        obtain ⟨C,cs,cf,cc⟩ := ih _ _ ok B bs newfits
        exact ⟨C,cs,cf,by simp only [List.length_cons]; omega⟩

  have runFlat_account (gs : List Gate) (w w' : List Wire) (ok : runFlat gs w = some w')
      (init : ∀ v ∈ w, v.1.1.card ≤ 1 ∧ v.2 = ∅) :
      ∃ B : Account, Sound B ∧ (∀ v ∈ w', Fits B v) ∧ cost B ≤ gs.length := by
    classical
    let sides := (Finset.univ : Finset Side).filter fun s => s.card ≤ 1
    let outs := (Finset.univ : Finset (Finset Term)).filter fun t => t.card ≤ 1
    let A : Account := ⟨0,0,sides,outs,∅⟩
    have snd : Sound A := by
      refine ⟨SBinputs _ ?_,OBinputs _ ?_,?_,?_,?_⟩ <;> simp [A,sides,outs]
    have fits (v : Wire) (hv : v ∈ w) := fit_small A snd v (init _ hv).1 (init _ hv).2
    obtain ⟨B,bs,bf,bc⟩ := runFlat_account_aux gs w w' ok A snd fits
    exact ⟨B,bs,bf,by simpa [A,cost] using bc⟩


  have input_eval (σ : V → V) (f : Bool → Bool) (x : Side) :
      (inputData σ f).map (wireVal x) = List.ofFn (bit x ∘ σ) ++ [f (bit x 0)] := by
    have r (i : V) : wireVal x (raw i, ∅) = bit x i := by
      apply Bool.eq_iff_iff.mpr
      simp [wireVal_iff,wireOn,raw_signal]
    have a : wireVal x (auxiliary f, ∅) = f (bit x 0) := by
      apply Bool.eq_iff_iff.mpr
      simp [wireVal_iff,wireOn,auxiliary_signal]
    simp [inputData,List.map_ofFn,Function.comp_def,r,a]

  -- Relate the symbolic output back to the actual circuit on all ten-bit inputs.
  have flat_twenty (C : Circuit) (σ : V → V) (f : Bool → Bool)
      (fan : FanInTwo C) (ao : AndOrOnly C) (flat : PEqualNP.TopForm.andPairs 11 C = 0)
      (yes : ∀ x : V → Bool, C.eval (List.ofFn (x ∘ σ) ++ [f (x 0)]) = target x) :
      20 ≤ C.size := by
    let w := inputData σ f
    have hi : w.length = 11 := by simp [w,inputData]
    have pure := inputs_pure σ f
    obtain ⟨out,run⟩ := ancestry_runFlat C fan ao flat w hi (fun v hv => (pure v hv).1)
    obtain ⟨B,good,fits,cost⟩ := runFlat_account C.gates w out run
      (fun v hv => ⟨(pure v hv).2,(pure v hv).1⟩)
    let o := out.getD C.output zeroWire
    have fit : Fits B o := getD_fits B good out fits C.output
    have correct (x : Side) : wireOn o x ↔ edgeOn x := by
      have h := yes (bit x)
      rw [← input_eval σ f x] at h
      change ((Circuit.mk C.gates 0).wires (w.map (wireVal x))).getD C.output false = _ at h
      rw [runFlat_value _ _ _ run x, map_getD] at h
      exact (wireVal_iff x o).symm.trans ((Bool.eq_iff_iff.mp h).trans (target_eq x))
    exact (root_cost good.1 good.2.1 o.1 o.2 B.2.2.2.2 fit.2.2 (Or.inl fit.2.1)
      good.2.2.2.2 correct).trans cost
  intro C σ f fan ao flat h
  apply flat_twenty C σ f fan ao flat
  intro x
  exact (h x).trans (same x).symm
