import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1990_17
    (h1 : ∀ F : Finset (Fin 13 × Fin 13), (∀ e ∈ F, (e.1.val + e.2.val) % 13 ∈ ([0,1,3,9] : List Nat)) →
      26 ≤ F.card → 17 ≤ (F.image Prod.fst).card + (F.image Prod.snd).card)
    (h2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Nat), PEqualNP.MetaComplexity.Monotone2 C →
      let near := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
      let w := fun (i : Nat) (s t : Finset (Fin 13)) => (C.wires (List.ofFn (vec s t))).getD i false
      let S := fun i => (Finset.univ : Finset (Fin 13 × Fin 13)).filter fun e => near e.1 e.2 ∧ w i {e.1} {e.2} = true
      (∀ e : Fin 13 × Fin 13, near e.1 e.2 → e ∈ S u ∨ e ∈ S v) →
      26 ≤ (S u).card → 17 ≤ ((S u).image Prod.fst).card + ((S u).image Prod.snd).card →
      (∀ s : Finset (Fin 13), s.card ≤ 3 →
        (w u s (off s) || w v s (off s)) = false ∧ (w u (off s) s || w v (off s) s) = false) →
      63 ≤ C.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C pins hm hp ht
  let near := fun (p l : Fin 13) => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List Nat)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
  let w := fun (i : Nat) (s t : Finset (Fin 13)) => (C.wires (List.ofFn (vec s t))).getD i false
  let S := fun i => (Finset.univ : Finset (Fin 13 × Fin 13)).filter fun e => near e.1 e.2 ∧ w i {e.1} {e.2} = true
  let read := fun s t => PEqualNP.CircuitLowerBounds.GateOp.or.eval (pins.map (fun i => w i s t))
  change (∀ p l, near p l → read {p} {l} = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false) at ht
  obtain ⟨u,v,hr⟩ : ∃ u v : Nat, ∀ s t, read s t = (w u s t || w v s t) := by
    cases pins with
    | nil =>
      have hh := ht.1 0 0 (by decide)
      exact Bool.noConfusion hh
    | cons a rest =>
      cases rest with
      | nil => exact ⟨a,a, fun s t => by change (w a s t || false) = (w a s t || w a s t); simp⟩
      | cons b rest =>
        have hz : rest = [] := by simpa using hp
        subst rest
        exact ⟨a,b, fun s t => by change (w a s t || (w b s t || false)) = _; simp⟩
  let all : Finset (Fin 13 × Fin 13) := Finset.univ.filter (fun e => near e.1 e.2)
  have hc : all.card = 52 := by decide +kernel
  have cover : S u ∪ S v = all := by
    ext e
    simp only [S,all,Finset.mem_union,Finset.mem_filter, Finset.mem_univ,true_and]
    constructor
    · rintro (⟨h,_⟩|⟨h,_⟩) <;> exact h
    · intro h
      have yes := ht.1 e.1 e.2 h
      rw [hr] at yes
      rcases Bool.or_eq_true_iff.mp yes with ha | hb
      · exact Or.inl ⟨h,ha⟩
      · exact Or.inr ⟨h,hb⟩
  have total := Finset.card_union_le (S u) (S v)
  rw [cover,hc] at total
  have finish (a b : Nat) (ha : 26 ≤ (S a).card) (cov : S a ∪ S b = all)
      (rr : ∀ s t, read s t = (w a s t || w b s t)) : 63 ≤ C.size := by
    have pos : ∀ e : Fin 13 × Fin 13, near e.1 e.2 → e ∈ S a ∨ e ∈ S b := by
      intro e he
      apply Finset.mem_union.mp
      rw [cov]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e,he⟩
    apply h2 C a b hm pos ha
    · apply h1 _ _ ha
      intro e he
      exact (Finset.mem_filter.mp he).2.1
    · intro s hs
      change (w a s (off s) || w b s (off s)) = false ∧ (w a (off s) s || w b (off s) s) = false
      rw [← rr, ← rr]
      exact ht.2 s hs
  by_cases hu : 26 ≤ (S u).card
  · exact finish u v hu cover hr
  · exact finish v u (by omega) (by rw [Finset.union_comm]; exact cover)
      (fun s t => (hr s t).trans (Bool.or_comm _ _))
