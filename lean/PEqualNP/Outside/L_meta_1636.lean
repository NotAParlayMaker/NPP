import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1636
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem up0 (N : ℕ) (gates : List Gate) (g : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  exact mono2 gates hleg _ _ (by simp) (ofFn_mono N x y hxy) g h

end PEqualNP.Outside.L_meta_1636

open PEqualNP.Outside.L_meta_1636 in
theorem PEqualNP.Outside.L_meta_1636 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ w : ℕ,
    (∀ m l : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p0 ∈ L l ∧ p1 ∉ L l) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (∃ p ∈ L l, ev w (T l p) = true) →
      ∀ l' : Fin N, (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ev w (fun v : Fin N => decide (v ∉ L l')) = true) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L l)) = false → (∃ p ∈ L m, ev w (T m p) = true) →
      ∀ m' : Fin N, (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ev w (fun v : Fin N => decide (v ∉ L m')) = true) ∧
    (∀ m M : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (p0 ∉ L M ∧ p1 ∉ L M) → ((L M).filter (fun p => ev w (T M p) = true)).card ≤ 1) := by
  intro q N L i0 p0 p1 _ _ _ hint _ _ _ _ T hT gates hleg _ _ ev hev w
  have up : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) → ev w x = true → ev w y = true := by
    intro x y hxy h
    rw [hev] at h ⊢
    exact up0 N gates w hleg x y hxy h
  have two : ∀ a b : Fin N, a ≠ b → ∀ p c : Fin N, p ≠ c → c ∈ L a → c ∈ L b → p ∈ L a → p ∈ L b → False := by
    intro a b hab p c hpc hca hcb hpa hpb
    have h1 := hint a b hab
    have hs : ({p, c} : Finset (Fin N)) ⊆ L a ∩ L b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.2 ⟨hpa, hpb⟩
      · exact Finset.mem_inter.2 ⟨hca, hcb⟩
    have h2 := Finset.card_le_card hs
    rw [Finset.card_pair hpc] at h2
    omega
  refine ⟨?_, ?_, ?_⟩
  · rintro m l ⟨hm1, hm0⟩ ⟨hl0, hl1⟩ hfalse ⟨p, hp, htrue⟩ l' ⟨hl'0, hl'1⟩ hne'
    by_cases hp0 : p = p0
    · exfalso
      have key := up _ (fun v : Fin N => decide (v ∉ L m)) (fun v hv => by
        have h := (hT l p v).1 hv
        have hv' : v ∉ L m := by
          rcases h with h | h | h | h
          · rw [h, hp0]; exact hm0
          · exact absurd hl0 h.1
          · exact absurd hp0 h.2.2.1
          · exact absurd h.2.1 hl1
        simpa using hv') htrue
      rw [key] at hfalse
      exact absurd hfalse (by simp)
    · refine up _ _ (fun v hv => ?_) htrue
      have h := (hT l p v).1 hv
      have hv' : v ∉ L l' := by
        rcases h with h | h | h | h
        · rw [h]; intro hpl'; exact two l l' (Ne.symm hne') p p0 hp0 hl0 hl'0 hp hpl'
        · exact absurd hl0 h.1
        · rw [h.2.2.2]; exact hl'1
        · exact absurd h.2.1 hl1
      simpa using hv'
  · rintro l m ⟨hl0, hl1⟩ ⟨hm1, hm0⟩ hfalse ⟨p, hp, htrue⟩ m' ⟨hm'1, hm'0⟩ hne'
    by_cases hp1 : p = p1
    · exfalso
      have key := up _ (fun v : Fin N => decide (v ∉ L l)) (fun v hv => by
        have h := (hT m p v).1 hv
        have hv' : v ∉ L l := by
          rcases h with h | h | h | h
          · rw [h, hp1]; exact hl1
          · exact absurd hp1 h.2.1
          · exact absurd h.1 hm0
          · exact absurd h.1 hm0
        simpa using hv') htrue
      rw [key] at hfalse
      exact absurd hfalse (by simp)
    · refine up _ _ (fun v hv => ?_) htrue
      have h := (hT m p v).1 hv
      have hv' : v ∉ L m' := by
        rcases h with h | h | h | h
        · rw [h]; intro hpm'; exact two m m' (Ne.symm hne') p p1 hp1 hm1 hm'1 hp hpm'
        · rw [h.2.2]; exact hm'0
        · exact absurd h.1 hm0
        · exact absurd h.1 hm0
      simpa using hv'
  · rintro m M ⟨hm1, hm0⟩ hfalse ⟨hM0, hM1⟩
    have hmM : m ≠ M := by
      rintro rfl
      exact hM1 hm1
    have hsub : (L M).filter (fun p => ev w (T M p) = true) ⊆ L m ∩ L M := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpM, htrue⟩ := hp
      rw [Finset.mem_inter]
      refine ⟨?_, hpM⟩
      by_contra hpm
      have key := up _ (fun v : Fin N => decide (v ∉ L m)) (fun v hv => by
        have h := (hT M p v).1 hv
        have hv' : v ∉ L m := by
          rcases h with h | h | h | h
          · rw [h]; exact hpm
          · rw [h.2.2]; exact hm0
          · exact absurd h.1 hM0
          · exact absurd h.1 hM0
        simpa using hv') htrue
      rw [key] at hfalse
      exact absurd hfalse (by simp)
    exact (Finset.card_le_card hsub).trans (hint m M hmM).le
