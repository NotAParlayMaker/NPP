import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1534

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def V (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gates.foldl stp (List.ofFn x)).getD i false

lemma getD_lt (w : List Bool) (v : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  first
    | exact List.getD_append _ _ _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  first
    | exact List.getD_eq_default _ _ h
    | simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma len_fold (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stp w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [stp, List.length_append, List.length_cons, List.length_nil]
    omega

lemma pre_fold (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have h1 : i < (stp w g).length := by
      simp only [stp, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [List.foldl_cons, ih (stp w g) i h1]
    exact getD_lt w _ i hi

lemma gate_fold (gs : List Gate) :
    ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl stp w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i => ((gs.take k).foldl stp w).getD i false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      have h1 : w.length < (stp w g).length := by
        simp only [stp, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, Nat.add_zero, pre_fold gs (stp w g) w.length h1]
      simp only [stp, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      exact getD_last w _
    | succ k =>
      have hk' : k < gs.length := by
        simp only [List.length_cons] at hk
        omega
      have h := ih (stp w g) k hk'
      have hl : (stp w g).length + k = w.length + (k + 1) := by
        simp only [stp, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hl] at h
      simpa only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ] using h

lemma V_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    V gates x i = x ⟨i, hi⟩ := by
  unfold V
  rw [pre_fold gates (List.ofFn x) i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma V_ge (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : n + gates.length ≤ i) :
    V gates x i = false := by
  unfold V
  apply getD_big
  rw [len_fold, List.length_ofFn]
  exact hi

lemma V_gate (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length) :
    V gates x (n + k) =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i => if i < n + k then V gates x i else false) := by
  unfold V
  have h := gate_fold gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  rw [h]
  have hlen : ((gates.take k).foldl stp (List.ofFn x)).length = n + k := by
    rw [len_fold, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hsplit : gates.foldl stp (List.ofFn x) =
      (gates.drop k).foldl stp ((gates.take k).foldl stp (List.ofFn x)) := by
    rw [← List.foldl_append, List.take_append_drop]
  have hmap : ((gates[k]).inputs.map fun i => ((gates.take k).foldl stp (List.ofFn x)).getD i false) =
      (gates[k]).inputs.map fun i =>
        if i < n + k then (gates.foldl stp (List.ofFn x)).getD i false else false := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < n + k
    · rw [if_pos hi, hsplit,
        pre_fold (gates.drop k) ((gates.take k).foldl stp (List.ofFn x)) i (by rw [hlen]; exact hi)]
    · rw [if_neg hi]
      exact getD_big _ i (by rw [hlen]; omega)
  rw [hmap]

lemma and_map {α : Type} (l : List α) (f : α → Bool) :
    GateOp.eval GateOp.and (l.map f) = true ↔ ∀ a ∈ l, f a = true := by
  simp [GateOp.eval]

lemma or_map {α : Type} (l : List α) (f : α → Bool) :
    GateOp.eval GateOp.or (l.map f) = true ↔ ∃ a ∈ l, f a = true := by
  simp [GateOp.eval]

lemma three_in_two (l : List ℕ) (hl : l.length ≤ 2) (a b c : ℕ)
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) : a = b ∨ a = c ∨ b = c := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    left
    rw [ha, hb]
  | [u, v], _ =>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> simp
  | _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

lemma mono_ao {n : ℕ} (G : List Gate)
    (hops : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ i : ℕ, V G x i = true → V G y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hv
    by_cases hin : i < n
    · rw [V_input G x i hin] at hv
      rw [V_input G y i hin]
      exact hxy _ hv
    · by_cases hlen : i < n + G.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < G.length := by omega
        rcases (hops (G[k]) (List.getElem_mem hk)).1 with hh | hh
        · rw [V_gate G x k hk, hh, and_map] at hv
          rw [V_gate G y k hk, hh, and_map]
          intro a ha
          have h2 := hv a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at h2 ⊢
            exact ih a hlt h2
          · rw [if_neg hlt] at h2
            exact Bool.noConfusion h2
        · rw [V_gate G x k hk, hh, or_map] at hv
          rw [V_gate G y k hk, hh, or_map]
          obtain ⟨a, ha, h2⟩ := hv
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at h2
            exact ⟨a, ha, by rw [if_pos hlt]; exact ih a hlt h2⟩
          · rw [if_neg hlt] at h2
            exact Bool.noConfusion h2
      · rw [V_ge G x i (by omega)] at hv
        exact Bool.noConfusion hv

lemma eq_decide_of_iff (b : Bool) (P : Prop) [Decidable P] (h : b = true ↔ P) : b = decide P := by
  by_cases hp : P
  · rw [h.mpr hp]
    simp [hp]
  · have hb : b = false := by
      cases hb : b
      · rfl
      · exact absurd (h.mp hb) hp
    rw [hb]
    simp [hp]

-- an OR gate listing input wires only is the OR of those inputs
lemma orl_val {n : ℕ} (G : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < G.length)
    (l : List (Fin n)) (hg : G[k] = ⟨GateOp.or, l.map Fin.val⟩) :
    V G x (n + k) = true ↔ ∃ a ∈ l, x a = true := by
  rw [V_gate G x k hk, hg]
  show GateOp.eval GateOp.or ((l.map Fin.val).map fun i => if i < n + k then V G x i else false) = true ↔ _
  rw [or_map]
  constructor
  · rintro ⟨i, hi, hv⟩
    rw [List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have hlt : (a : ℕ) < n + k := by
      have := a.isLt
      omega
    rw [if_pos hlt, V_input G x a a.isLt] at hv
    exact ⟨a, ha, hv⟩
  · rintro ⟨a, ha, hv⟩
    refine ⟨(a : ℕ), List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    have hlt : (a : ℕ) < n + k := by
      have := a.isLt
      omega
    rw [if_pos hlt, V_input G x a a.isLt]
    exact hv

-- the single inputs at which gate k is true
def supp (gates : List Gate) (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v : Fin n => V gates (fun u : Fin n => decide (u = v)) (n + k) = true)

lemma mem_supp (gates : List Gate) (n k : ℕ) (v : Fin n) :
    v ∈ supp gates n k ↔ V gates (fun u : Fin n => decide (u = v)) (n + k) = true := by
  simp [supp]

-- a gate true at no more than one single input is replaced by the OR of those inputs
noncomputable def newGate (gates : List Gate) (n : ℕ) (k : Fin gates.length) : Gate :=
  if (supp gates n k).card ≤ 1 then ⟨GateOp.or, (supp gates n k).toList.map Fin.val⟩
  else gates.get k

lemma core {n m : ℕ} (gates : List Gate) (out : Fin m → ℕ) (S : Fin m → Finset (Fin n))
    (D : Set (Fin n → Bool))
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hD : ∀ v : Fin n, (fun vk : Fin n => decide (vk = v)) ∈ D)
    (hright : ∀ (w : Fin m) (x : Fin n → Bool), x ∈ D →
      V gates x (out w) = decide (∃ v0 ∈ S w, x v0 = true)) :
    ∃ gates2 : List Gate, gates2.length ≤ gates.length ∧
      (∀ g2 ∈ gates2, (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2) ∧
      (∀ ak : ℕ, ak < gates2.length →
        (Finset.univ.filter (fun au : Fin n =>
          V gates2 (fun auk : Fin n => decide (auk = au)) (n + ak) = true)).card ≤ 1 →
        ∀ ax : Fin n → Bool, V gates2 ax (n + ak) =
          decide (∃ av : Fin n, V gates2 (fun avk : Fin n => decide (avk = av)) (n + ak) = true ∧
            ax av = true)) ∧
      ∀ (w2 : Fin m) (x2 : Fin n → Bool), x2 ∈ D →
        V gates2 x2 (out w2) = decide (∃ v2 ∈ S w2, x2 v2 = true) := by
  have hlen : (List.ofFn (fun k : Fin gates.length => newGate gates n k)).length = gates.length :=
    List.length_ofFn
  have hget : ∀ (k : ℕ) (hk : k < gates.length),
      (List.ofFn (fun k : Fin gates.length => newGate gates n k))[k]'(by rw [hlen]; exact hk) =
        newGate gates n ⟨k, hk⟩ := by
    intro k hk
    simp
  have hrepg : ∀ (k : ℕ) (hk : k < gates.length), (supp gates n k).card ≤ 1 →
      (List.ofFn (fun k : Fin gates.length => newGate gates n k))[k]'(by rw [hlen]; exact hk) =
        ⟨GateOp.or, (supp gates n k).toList.map Fin.val⟩ := by
    intro k hk hc
    rw [hget k hk]
    simp [newGate, hc]
  have hkeep : ∀ (k : ℕ) (hk : k < gates.length), ¬ (supp gates n k).card ≤ 1 →
      (List.ofFn (fun k : Fin gates.length => newGate gates n k))[k]'(by rw [hlen]; exact hk) =
        gates[k] := by
    intro k hk hc
    rw [hget k hk]
    simp [newGate, hc]
  have hops2 : ∀ g2 ∈ List.ofFn (fun k : Fin gates.length => newGate gates n k),
      (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2 := by
    intro g2 hg2
    rw [List.mem_ofFn] at hg2
    obtain ⟨k, rfl⟩ := hg2
    by_cases hc : (supp gates n k).card ≤ 1
    · have hg : newGate gates n k = ⟨GateOp.or, (supp gates n k).toList.map Fin.val⟩ := by
        simp [newGate, hc]
      rw [hg]
      refine ⟨Or.inr rfl, ?_⟩
      show ((supp gates n k).toList.map Fin.val).length ≤ 2
      rw [List.length_map, Finset.length_toList]
      omega
    · have hg : newGate gates n k = gates.get k := by
        simp [newGate, hc]
      rw [hg]
      exact hops _ (List.get_mem _ _)
  have hrep : ∀ (k : ℕ) (hk : k < gates.length), (supp gates n k).card ≤ 1 →
      ∀ x : Fin n → Bool,
        (V (List.ofFn (fun k : Fin gates.length => newGate gates n k)) x (n + k) = true ↔
          ∃ a ∈ supp gates n k, x a = true) := by
    intro k hk hc x
    rw [orl_val _ x k (by rw [hlen]; exact hk) _ (hrepg k hk hc)]
    simp [Finset.mem_toList]
  -- the single inputs keep their values
  have P1 : ∀ (i : ℕ) (v : Fin n),
      V (List.ofFn (fun k : Fin gates.length => newGate gates n k)) (fun u : Fin n => decide (u = v)) i =
        V gates (fun u : Fin n => decide (u = v)) i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro v
      by_cases hin : i < n
      · rw [V_input _ _ i hin, V_input gates _ i hin]
      · by_cases hl : i < n + gates.length
        · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
          have hk : k < gates.length := by omega
          by_cases hc : (supp gates n k).card ≤ 1
          · rw [Bool.eq_iff_iff, hrep k hk hc]
            constructor
            · rintro ⟨a, ha, hav⟩
              have hav' : a = v := by simpa using hav
              rw [← hav']
              exact (mem_supp gates n k a).mp ha
            · intro hv
              exact ⟨v, (mem_supp gates n k v).mpr hv, by simp⟩
          · rw [V_gate _ _ k (by rw [hlen]; exact hk), V_gate gates _ k hk, hkeep k hk hc]
            congr 1
            apply List.map_congr_left
            intro a _
            by_cases hlt : a < n + k
            · rw [if_pos hlt, if_pos hlt]
              exact ih a hlt v
            · rw [if_neg hlt, if_neg hlt]
        · rw [V_ge _ _ i (by rw [hlen]; omega), V_ge gates _ i (by omega)]
  -- every wire of the new list is below the old one
  have P2 : ∀ (i : ℕ) (x : Fin n → Bool),
      V (List.ofFn (fun k : Fin gates.length => newGate gates n k)) x i = true → V gates x i = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro x hv
      by_cases hin : i < n
      · rw [V_input _ _ i hin] at hv
        rw [V_input gates _ i hin]
        exact hv
      · by_cases hl : i < n + gates.length
        · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
          have hk : k < gates.length := by omega
          by_cases hc : (supp gates n k).card ≤ 1
          · rw [hrep k hk hc x] at hv
            obtain ⟨a, ha, hax⟩ := hv
            have hsa := (mem_supp gates n k a).mp ha
            refine mono_ao gates hops _ x ?_ (n + k) hsa
            intro u hu
            have hua : u = a := by simpa using hu
            rw [hua]
            exact hax
          · rw [V_gate _ _ k (by rw [hlen]; exact hk), hkeep k hk hc] at hv
            rw [V_gate gates x k hk]
            rcases (hops (gates[k]) (List.getElem_mem hk)).1 with hh | hh
            · rw [hh, and_map] at hv ⊢
              intro a ha
              have h2 := hv a ha
              by_cases hlt : a < n + k
              · rw [if_pos hlt] at h2 ⊢
                exact ih a hlt x h2
              · rw [if_neg hlt] at h2
                exact Bool.noConfusion h2
            · rw [hh, or_map] at hv ⊢
              obtain ⟨a, ha, h2⟩ := hv
              by_cases hlt : a < n + k
              · rw [if_pos hlt] at h2
                exact ⟨a, ha, by rw [if_pos hlt]; exact ih a hlt x h2⟩
              · rw [if_neg hlt] at h2
                exact Bool.noConfusion h2
        · rw [V_ge _ _ i (by rw [hlen]; omega)] at hv
          exact Bool.noConfusion hv
  refine ⟨List.ofFn (fun k : Fin gates.length => newGate gates n k), le_of_eq hlen, hops2, ?_, ?_⟩
  · intro ak hak hcard ax
    have hk : ak < gates.length := by
      rw [hlen] at hak
      exact hak
    have hsame : (Finset.univ.filter (fun au : Fin n =>
        V (List.ofFn (fun k : Fin gates.length => newGate gates n k))
          (fun auk : Fin n => decide (auk = au)) (n + ak) = true)) = supp gates n ak := by
      ext au
      rw [Finset.mem_filter, mem_supp, P1 (n + ak) au]
      simp
    rw [hsame] at hcard
    apply eq_decide_of_iff
    rw [hrep ak hk hcard ax]
    constructor
    · rintro ⟨a, ha, hax⟩
      refine ⟨a, ?_, hax⟩
      rw [P1 (n + ak) a]
      exact (mem_supp gates n ak a).mp ha
    · rintro ⟨a, ha, hax⟩
      rw [P1 (n + ak) a] at ha
      exact ⟨a, (mem_supp gates n ak a).mpr ha, hax⟩
  · intro w x hx
    apply eq_decide_of_iff
    constructor
    · intro hv
      have h1 := P2 (out w) x hv
      rw [hright w x hx] at h1
      exact of_decide_eq_true h1
    · rintro ⟨v, hvS, hxv⟩
      have h1 : V gates (fun u : Fin n => decide (u = v)) (out w) = true := by
        rw [hright w _ (hD v)]
        simp only [decide_eq_true_eq]
        exact ⟨v, hvS, by simp⟩
      have h2 : V (List.ofFn (fun k : Fin gates.length => newGate gates n k))
          (fun u : Fin n => decide (u = v)) (out w) = true := by
        rw [P1 (out w) v]
        exact h1
      refine mono_ao _ hops2 _ x ?_ (out w) h2
      intro u hu
      have huv : u = v := by simpa using hu
      rw [huv]
      exact hxv

end PEqualNP.Outside.L_meta_1534

theorem PEqualNP.Outside.L_meta_1534 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (S : Fin m → Finset (Fin n)) (D : Set (Fin n → Bool)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ v : Fin n, (fun vk : Fin n => decide (vk = v)) ∈ D) → (∀ (w : Fin m) (x : Fin n → Bool), x ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (out w) false = decide (∃ v0 ∈ S w, x v0 = true)) → ∃ gates2 : List PEqualNP.CircuitLowerBounds.Gate, gates2.length ≤ gates.length ∧ (∀ g2 ∈ gates2, (g2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g2.inputs.length ≤ 2) ∧ (∀ ak : ℕ, ak < gates2.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) ∧ ∀ (w2 : Fin m) (x2 : Fin n → Bool), x2 ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn x2)).getD (out w2) false = decide (∃ v2 ∈ S w2, x2 v2 = true) := by
  intro n m gates out S D hops hD hright
  exact PEqualNP.Outside.L_meta_1534.core gates out S D hops hD hright
