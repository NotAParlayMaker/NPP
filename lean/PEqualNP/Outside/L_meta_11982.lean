import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11982

open PEqualNP.CircuitLowerBounds

def Rn : ℕ → List ℕ → ℕ → Bool
  | 0, S, g => decide (g ∈ S)
  | k + 1, S, g => S.any fun a => S.any fun b =>
      [a &&& b, a ||| b, 255 ^^^ a].any fun h => Rn k (h :: S) g

theorem rn_false : Rn 3 [0, 255, 170, 204, 240] 232 = false := by decide +kernel

def enc : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, g => Nat.bit (g 0) (enc n (fun i => g i.succ))

theorem testBit_enc : ∀ (n : ℕ) (g : Fin n → Bool) (i : ℕ),
    (enc n g).testBit i = if h : i < n then g ⟨i, h⟩ else false := by
  intro n
  induction n with
  | zero => intro g i; simp [enc]
  | succ n ih =>
    intro g i
    cases i with
    | zero => simp [enc]
    | succ i =>
      rw [enc, Nat.testBit_bit_succ, ih]
      by_cases h : i < n
      · simp [h]
      · simp [h]

theorem enc_and (n : ℕ) (a b : Fin n → Bool) :
    enc n (fun p => a p && b p) = enc n a &&& enc n b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_enc, testBit_enc, testBit_enc]
  split_ifs <;> simp

theorem enc_or (n : ℕ) (a b : Fin n → Bool) :
    enc n (fun p => a p || b p) = enc n a ||| enc n b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_enc, testBit_enc, testBit_enc]
  split_ifs <;> simp

theorem enc_not (n : ℕ) (a : Fin n → Bool) :
    enc n (fun p => !a p) = (2 ^ n - 1) ^^^ enc n a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, testBit_enc, testBit_enc]
  split_ifs <;> simp_all

abbrev Fn := (Fin 7 → Bool) → Bool

def X (j : Fin 7) : Fn := fun x => x j

def cf : Fn := fun _ => false

def ct : Fn := fun _ => true

def rs (i : Fin 7) (g : Fn) : Fn := fun x => g (Function.update x i false)

def pt (p : Fin 8) : Fin 7 → Bool := fun j =>
  if j.val = 0 then p.val.testBit 0
  else if j.val = 4 then p.val.testBit 1
  else if j.val = 5 then p.val.testBit 2 else false

def tt (g : Fn) : ℕ := enc 8 (fun p => g (pt p))

theorem tt_and (a b : Fn) : tt (fun x => a x && b x) = tt a &&& tt b :=
  enc_and 8 (fun p => a (pt p)) (fun p => b (pt p))

theorem tt_or (a b : Fn) : tt (fun x => a x || b x) = tt a ||| tt b :=
  enc_or 8 (fun p => a (pt p)) (fun p => b (pt p))

theorem tt_not (a : Fn) : tt (fun x => !a x) = 255 ^^^ tt a :=
  enc_not 8 (fun p => a (pt p))

def Reach : ℕ → Set Fn → Fn → Prop
  | 0, S, g => g ∈ S
  | k + 1, S, g => ∃ a ∈ S, ∃ b ∈ S, ∃ h : Fn,
      (h = (fun x => a x && b x) ∨ h = (fun x => a x || b x) ∨ h = (fun x => !a x)) ∧
      Reach k (insert h S) g

theorem lift : ∀ (k : ℕ) (S : Set Fn) (Sn : List ℕ) (g : Fn), Reach k S g →
    (∀ s ∈ S, tt s ∈ Sn) → Rn k Sn (tt g) = true
  | 0, S, Sn, g, r, hs => by
    simp only [Rn, decide_eq_true_eq]
    exact hs g r
  | k + 1, S, Sn, g, ⟨a, ha, b, hb, h, hh, r⟩, hs => by
    have ih := lift k (insert h S) (tt h :: Sn) g r (by
      rintro s (rfl | hs')
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs s hs'))
    simp only [Rn, List.any_eq_true]
    refine ⟨tt a, hs a ha, tt b, hs b hb, tt h, ?_, ih⟩
    rcases hh with rfl | rfl | rfl
    · simp [tt_and]
    · simp [tt_or]
    · simp [tt_not]

theorem reach_mono_S : ∀ (k : ℕ) (S S' : Set Fn) (g : Fn), S ⊆ S' → Reach k S g → Reach k S' g
  | 0, S, S', g, hS, r => hS r
  | k + 1, S, S', g, hS, ⟨a, ha, b, hb, h, hh, r⟩ =>
    ⟨a, hS ha, b, hS hb, h, hh, reach_mono_S k _ _ g (Set.insert_subset_insert hS) r⟩

theorem reach_succ : ∀ (k : ℕ) (S : Set Fn) (g : Fn), Reach k S g → Reach (k + 1) S g
  | 0, S, g, r => ⟨g, r, g, r, g, Or.inl (by funext x; simp), Set.mem_insert _ _⟩
  | k + 1, S, g, ⟨a, ha, b, hb, h, hh, r⟩ => ⟨a, ha, b, hb, h, hh, reach_succ k _ g r⟩

theorem reach_le (k n : ℕ) (hkn : k ≤ n) (S : Set Fn) (g : Fn) (r : Reach k S g) :
    Reach n S g := by
  induction n, hkn using Nat.le_induction with
  | base => exact r
  | succ n _ ih => exact reach_succ n S g ih

theorem reach_rs (i : Fin 7) : ∀ (k : ℕ) (S : Set Fn) (g : Fn), Reach k S g →
    Reach k (rs i '' S) (rs i g)
  | 0, S, g, r => Set.mem_image_of_mem _ r
  | k + 1, S, g, ⟨a, ha, b, hb, h, hh, r⟩ => by
    refine ⟨rs i a, Set.mem_image_of_mem _ ha, rs i b, Set.mem_image_of_mem _ hb, rs i h, ?_, ?_⟩
    · rcases hh with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · have := reach_rs i k _ g r
      rwa [Set.image_insert_eq] at this

theorem elim (i : Fin 7) : ∀ (k : ℕ) (S : Set Fn) (g : Fn),
    (∀ s ∈ S, s ≠ X i → rs i s = s) → cf ∈ S → ct ∈ S → rs i g ≠ g → g ≠ X i →
    Reach k S g → ∃ k', k = k' + 1 ∧ Reach k' (rs i '' S) (rs i g)
  | 0, S, g, hinv, _, _, hd, hx, r => absurd (hinv g r hx) hd
  | k + 1, S, g, hinv, hcf, hct, hd, hx, ⟨a, ha, b, hb, h, hh, r⟩ => by
    by_cases hind : h = X i ∨ rs i h = h
    · have hinv' : ∀ s ∈ insert h S, s ≠ X i → rs i s = s := by
        intro s hs hsx
        rcases hs with rfl | hs
        · rcases hind with h1 | h1
          · exact absurd h1 hsx
          · exact h1
        · exact hinv s hs hsx
      obtain ⟨k', hk, r'⟩ := elim i k (insert h S) g hinv' (Set.mem_insert_of_mem _ hcf)
        (Set.mem_insert_of_mem _ hct) hd hx r
      refine ⟨k' + 1, by omega, rs i a, Set.mem_image_of_mem _ ha, rs i b,
        Set.mem_image_of_mem _ hb, rs i h, ?_, ?_⟩
      · rcases hh with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · rwa [Set.image_insert_eq] at r'
    · have hmem : rs i h ∈ rs i '' S := by
        rw [not_or] at hind
        obtain ⟨hn1, hn2⟩ := hind
        rcases hh with rfl | rfl | rfl
        · by_cases ha' : a = X i
          · subst ha'
            exact ⟨cf, hcf, by funext x; simp [rs, X, cf]⟩
          · by_cases hb' : b = X i
            · subst hb'
              exact ⟨cf, hcf, by funext x; simp [rs, X, cf]⟩
            · exfalso
              apply hn2
              have ea : ∀ x, a (Function.update x i false) = a x := fun x => congrFun (hinv a ha ha') x
              have eb : ∀ x, b (Function.update x i false) = b x := fun x => congrFun (hinv b hb hb') x
              funext x
              show (a (Function.update x i false) && b (Function.update x i false)) = (a x && b x)
              rw [ea x, eb x]
        · by_cases ha' : a = X i
          · subst ha'
            exact ⟨b, hb, by funext x; simp [rs, X]⟩
          · by_cases hb' : b = X i
            · subst hb'
              exact ⟨a, ha, by funext x; simp [rs, X]⟩
            · exfalso
              apply hn2
              have ea : ∀ x, a (Function.update x i false) = a x := fun x => congrFun (hinv a ha ha') x
              have eb : ∀ x, b (Function.update x i false) = b x := fun x => congrFun (hinv b hb hb') x
              funext x
              show (a (Function.update x i false) || b (Function.update x i false)) = (a x || b x)
              rw [ea x, eb x]
        · by_cases ha' : a = X i
          · subst ha'
            exact ⟨ct, hct, by funext x; simp [rs, X, ct]⟩
          · exfalso
            apply hn2
            have ea : ∀ x, a (Function.update x i false) = a x := fun x => congrFun (hinv a ha ha') x
            funext x
            show (!a (Function.update x i false)) = !a x
            rw [ea x]
      refine ⟨k, rfl, ?_⟩
      have := reach_rs i k _ g r
      rw [Set.image_insert_eq, Set.insert_eq_of_mem hmem] at this
      exact this

def Q (D : List (Fin 7)) : Set Fn := {s | (∃ j, j ∉ D ∧ s = X j) ∨ s = cf ∨ s = ct}

theorem Q_cf (D : List (Fin 7)) : cf ∈ Q D := Or.inr (Or.inl rfl)

theorem Q_ct (D : List (Fin 7)) : ct ∈ Q D := Or.inr (Or.inr rfl)

theorem Q_inv (D : List (Fin 7)) (i : Fin 7) : ∀ s ∈ Q D, s ≠ X i → rs i s = s := by
  rintro s (⟨j, hj, rfl⟩ | rfl | rfl) hsx
  · have hji : j ≠ i := fun h => hsx (by rw [h])
    funext x
    simp [rs, X, Function.update_of_ne hji]
  · rfl
  · rfl

theorem Q_img (D : List (Fin 7)) (i : Fin 7) : rs i '' Q D ⊆ Q (i :: D) := by
  rintro _ ⟨s, (⟨j, hj, rfl⟩ | rfl | rfl), rfl⟩
  · by_cases hji : j = i
    · subst hji
      right; left
      funext x
      simp [rs, X, cf]
    · left
      refine ⟨j, ?_, ?_⟩
      · simp [hji]
        exact hj
      · funext x
        simp [rs, X, Function.update_of_ne hji]
  · right; left; rfl
  · right; right; rfl

def wF (w : List Fn) (gs : List Gate) : List Fn :=
  gs.foldl (fun w g => w ++ [fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)]) w

theorem getD_map (w : List Fn) (i : ℕ) (x : Fin 7 → Bool) :
    (w.map fun s => s x).getD i false = (w.getD i cf) x := by
  induction w generalizing i with
  | nil => simp [cf]
  | cons s w ih =>
    cases i with
    | zero => simp only [List.map_cons, List.getD_cons_zero]
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih i

theorem wF_map : ∀ (gs : List Gate) (w : List Fn) (x : Fin 7 → Bool),
    (wF w gs).map (fun s => s x) = gs.foldl
      (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) (w.map fun s => s x)
  | [], w, x => rfl
  | g :: gs, w, x => by
    have h1 := wF_map gs (w ++ [fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)]) x
    have h2 : (w ++ [fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)]).map
        (fun s => s x) = (w.map fun s => s x) ++
        [g.op.eval (g.inputs.map fun i => (w.map fun s => s x).getD i false)] := by
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil, getD_map]
    rw [h2] at h1
    exact h1

theorem circ_eval (gates : List Gate) (o : ℕ) (x : Fin 7 → Bool) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = ((wF (List.ofFn X) gates).getD o cf) x := by
  have h0 : List.ofFn x = (List.ofFn X).map (fun s => s x) := by
    rw [List.map_ofFn]; rfl
  rw [← getD_map, wF_map, ← h0]
  rfl

theorem getD_mem (S : Set Fn) (w : List Fn) (hw : ∀ s ∈ w, s ∈ S) (hcf : cf ∈ S) (o : ℕ) :
    w.getD o cf ∈ S := by
  by_cases h : o < w.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hcf

theorem gate_step (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (S : Set Fn) (w : List Fn) (hw : ∀ s ∈ w, s ∈ S) (hcf : cf ∈ S) :
    ∃ a ∈ S, ∃ b ∈ S,
      ((fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)) = (fun x => a x && b x) ∨
       (fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)) = (fun x => a x || b x) ∨
       (fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)) = (fun x => !a x)) := by
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen ⊢
  rcases inputs with _ | ⟨i, _ | ⟨j, _ | ⟨l, ls⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact ⟨cf, hcf, cf, hcf, Or.inr (Or.inr (by funext x; simp [GateOp.eval, cf]))⟩
    · exact ⟨cf, hcf, cf, hcf, Or.inl (by funext x; simp [GateOp.eval, cf])⟩
    · exact ⟨cf, hcf, cf, hcf, Or.inr (Or.inr (by funext x; simp [GateOp.eval, cf]))⟩
  · have hi := getD_mem S w hw hcf i
    rcases hop with rfl | rfl | rfl
    · exact ⟨_, hi, _, hi, Or.inl (by funext x; simp [GateOp.eval])⟩
    · exact ⟨_, hi, _, hi, Or.inr (Or.inl (by funext x; simp [GateOp.eval]))⟩
    · exact ⟨_, hi, _, hi, Or.inr (Or.inr (by funext x; simp [GateOp.eval]))⟩
  · have hi := getD_mem S w hw hcf i
    have hj := getD_mem S w hw hcf j
    rcases hop with rfl | rfl | rfl
    · exact ⟨_, hi, _, hj, Or.inl (by funext x; simp [GateOp.eval])⟩
    · exact ⟨_, hi, _, hj, Or.inr (Or.inl (by funext x; simp [GateOp.eval]))⟩
    · exact ⟨_, hi, _, hj, Or.inr (Or.inr (by funext x; simp [GateOp.eval]))⟩
  · simp at hlen

theorem reach_circuit : ∀ (gs : List Gate) (w : List Fn) (S : Set Fn),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) → (∀ s ∈ w, s ∈ S) → cf ∈ S → ∀ o,
    Reach gs.length S ((wF w gs).getD o cf)
  | [], w, S, _, hw, hcf, o => getD_mem S w hw hcf o
  | g :: gs, w, S, hg, hw, hcf, o => by
    obtain ⟨a, ha, b, hb, hh⟩ := gate_step g (hg g List.mem_cons_self) S w hw hcf
    refine ⟨a, ha, b, hb,
      (fun x => g.op.eval (g.inputs.map fun i => (w.getD i cf) x)), hh, ?_⟩
    refine reach_circuit gs _ (insert _ S)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ (Set.mem_insert_of_mem _ hcf) o
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact Set.mem_insert_of_mem _ (hw s h)
    · rw [List.mem_singleton] at h
      rw [h]
      exact Set.mem_insert _ _

def gates8 : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.or, [9, 3]⟩,
   ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [11, 10]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [12, 13]⟩]

def f : Fn := fun x =>
  ((x 5 || x 6) && (x 0 || x 1 || x 2 || x 3 || x 4)) || (x 4 && (x 0 || x 1))

theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

theorem upper (x : Fin 7 → Bool) : Circuit.eval ⟨gates8, 14⟩ (List.ofFn x) = f x := by
  have key : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool, Circuit.eval ⟨gates8, 14⟩ [a0, a1, a2, a3, a4, a5, a6] =
      (((a5 || a6) && (a0 || a1 || a2 || a3 || a4)) || (a4 && (a0 || a1))) := by
    decide +kernel
  rw [ofFn7]
  exact key _ _ _ _ _ _ _

theorem spec_f (x : Fin 7 → Bool) :
    decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = f x := by
  have key : ∀ a0 a1 a2 a3 a4 a5 a6 : Bool,
      decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, [a0, a1, a2, a3, a4, a5, a6].getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ [a0, a1, a2, a3, a4, a5, a6].getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) =
      (((a5 || a6) && (a0 || a1 || a2 || a3 || a4)) || (a4 && (a0 || a1))) := by
    decide +kernel
  rw [ofFn7]
  exact key _ _ _ _ _ _ _

theorem dep2 : rs 2 f ≠ f := fun h => by
  have := congrFun h (fun j => decide (j = 2 ∨ j = 5))
  revert this
  decide +kernel

theorem dep3 : rs 3 (rs 2 f) ≠ rs 2 f := fun h => by
  have := congrFun h (fun j => decide (j = 3 ∨ j = 5))
  revert this
  decide +kernel

theorem dep1 : rs 1 (rs 3 (rs 2 f)) ≠ rs 3 (rs 2 f) := fun h => by
  have := congrFun h (fun j => decide (j = 1 ∨ j = 5))
  revert this
  decide +kernel

theorem dep6 : rs 6 (rs 1 (rs 3 (rs 2 f))) ≠ rs 1 (rs 3 (rs 2 f)) := fun h => by
  have := congrFun h (fun j => decide (j = 6 ∨ j = 0))
  revert this
  decide +kernel

theorem nx2 : f ≠ X 2 := fun h => by
  have := congrFun h (fun j => decide (j = 2))
  revert this
  decide +kernel

theorem nx3 : rs 2 f ≠ X 3 := fun h => by
  have := congrFun h (fun j => decide (j = 3))
  revert this
  decide +kernel

theorem nx1 : rs 3 (rs 2 f) ≠ X 1 := fun h => by
  have := congrFun h (fun j => decide (j = 1))
  revert this
  decide +kernel

theorem nx6 : rs 1 (rs 3 (rs 2 f)) ≠ X 6 := fun h => by
  have := congrFun h (fun j => decide (j = 6))
  revert this
  decide +kernel

theorem tt_final : tt (rs 6 (rs 1 (rs 3 (rs 2 f)))) = 232 := by decide +kernel

theorem tt_Q : ∀ s ∈ Q [6, 1, 3, 2], tt s ∈ [0, 255, 170, 204, 240] := by
  have h1 : ∀ j : Fin 7, j ∉ [6, 1, 3, 2] → tt (X j) ∈ [0, 255, 170, 204, 240] := by
    decide +kernel
  have h2 : tt cf ∈ [0, 255, 170, 204, 240] := by decide +kernel
  have h3 : tt ct ∈ [0, 255, 170, 204, 240] := by decide +kernel
  rintro s (⟨j, hj, rfl⟩ | rfl | rfl)
  · exact h1 j hj
  · exact h2
  · exact h3

theorem lower (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x)
    (hk : gates.length ≤ 7) : False := by
  have hf : (wF (List.ofFn X) gates).getD o cf = f := by
    funext x
    rw [← circ_eval]
    exact hc x
  have R0 : Reach gates.length (Q []) f := by
    rw [← hf]
    refine reach_circuit gates (List.ofFn X) (Q []) hops ?_ (Q_cf _) o
    intro s hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hs
    exact Or.inl ⟨j, by simp, rfl⟩
  obtain ⟨k1, hk1, R1⟩ := elim 2 7 (Q []) f (Q_inv _ _) (Q_cf _) (Q_ct _) dep2 nx2
    (reach_le _ _ hk _ _ R0)
  have R1' := reach_mono_S _ _ _ _ (Q_img [] 2) R1
  obtain ⟨k2, hk2, R2⟩ := elim 3 k1 (Q [2]) (rs 2 f) (Q_inv _ _) (Q_cf _) (Q_ct _) dep3 nx3 R1'
  have R2' := reach_mono_S _ _ _ _ (Q_img [2] 3) R2
  obtain ⟨k3, hk3, R3⟩ := elim 1 k2 (Q [3, 2]) (rs 3 (rs 2 f)) (Q_inv _ _) (Q_cf _) (Q_ct _)
    dep1 nx1 R2'
  have R3' := reach_mono_S _ _ _ _ (Q_img [3, 2] 1) R3
  obtain ⟨k4, hk4, R4⟩ := elim 6 k3 (Q [1, 3, 2]) (rs 1 (rs 3 (rs 2 f))) (Q_inv _ _) (Q_cf _)
    (Q_ct _) dep6 nx6 R3'
  have R4' := reach_mono_S _ _ _ _ (Q_img [1, 3, 2] 6) R4
  have hk4' : k4 = 3 := by omega
  subst hk4'
  have := lift 3 _ _ _ R4' tt_Q
  rw [tt_final, rn_false] at this
  exact Bool.false_ne_true this

end PEqualNP.Outside.L_meta_11982

theorem PEqualNP.Outside.L_meta_11982 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hops _ hcomp
  by_cases h8 : 8 ≤ gates.length
  · refine ⟨PEqualNP.Outside.L_meta_11982.gates8, 14, ?_, h8, fun x =>
      (PEqualNP.Outside.L_meta_11982.upper x).trans (PEqualNP.Outside.L_meta_11982.spec_f x).symm⟩
    intro g hg
    simp only [PEqualNP.Outside.L_meta_11982.gates8, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exfalso
    exact PEqualNP.Outside.L_meta_11982.lower gates o hops
      (fun x => (hcomp x).trans (PEqualNP.Outside.L_meta_11982.spec_f x)) (by omega)
