import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_214

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD, List.getElem?_append_left hi]

lemma run_last (gs : List Gate) (g : Gate) (w : List Bool) :
    (run (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs w).getD i false) := by
  rw [run_append]
  change ((run gs w) ++ [_]).getD _ false = _
  rw [← run_length]
  simp [List.getD]

def good (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def countAnd (gs : List Gate) : ℕ :=
  gs.countP fun g => match g.op with | .and => true | _ => false

lemma good_append (gs hs : List Gate) : good (gs ++ hs) ↔ good gs ∧ good hs := by
  constructor
  · intro h
    exact ⟨fun g hg => h g (List.mem_append_left _ hg),
      fun g hg => h g (List.mem_append_right _ hg)⟩
  · rintro ⟨hg, hh⟩ g h
    exact (List.mem_append.mp h).elim (hg g) (hh g)

lemma countAnd_append (gs hs : List Gate) :
    countAnd (gs ++ hs) = countAnd gs + countAnd hs := by
  simp [countAnd]

def orChain (m : ℕ) : List ℕ → List Gate
  | [] => [⟨.or, []⟩]
  | i :: is => orChain m is ++ [⟨.or, [i, m + is.length]⟩]

lemma orChain_length (m : ℕ) (is : List ℕ) : (orChain m is).length = is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [orChain, ih]

lemma orChain_good (m : ℕ) (is : List ℕ) : good (orChain m is) := by
  induction is with
  | nil => simp [orChain, good]
  | cons i is ih =>
    rw [orChain, good_append]
    exact ⟨ih, by simp [good]⟩

lemma orChain_count (m : ℕ) (is : List ℕ) : countAnd (orChain m is) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [orChain, countAnd_append, ih]
    rfl

lemma orChain_eval (m : ℕ) (is : List ℕ) (w : List Bool) (hw : w.length = m)
    (hi : ∀ i ∈ is, i < m) :
    (run (orChain m is) w).getD (m + is.length) false =
      is.any (fun i => w.getD i false) := by
  induction is with
  | nil => simp [orChain, run, GateOp.eval, ← hw, List.getD]
  | cons i is ih =>
    have hlast : m + (i :: is).length = w.length + (orChain m is).length := by
      simp [hw, orChain_length]
    rw [orChain, hlast, run_last]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [run_old _ _ _ (by rw [hw]; exact hi i (by simp)),
      ih (fun j hj => hi j (by simp [hj]))]

def stars {n : ℕ} (neighbors : Fin n → List (Fin n)) : List (Fin n) → List Gate
  | [] => [⟨.or, []⟩]
  | v :: vs =>
      let gs := stars neighbors vs
      let ns := orChain (n + gs.length) ((neighbors v).map Fin.val)
      gs ++ ns ++ [⟨.and, [v.val, n + gs.length + (neighbors v).length]⟩,
        ⟨.or, [n + gs.length - 1, n + gs.length + ns.length]⟩]

lemma stars_nonempty {n : ℕ} (neighbors : Fin n → List (Fin n)) (vs : List (Fin n)) :
    0 < (stars neighbors vs).length := by
  cases vs <;> simp [stars]

lemma stars_good {n : ℕ} (neighbors : Fin n → List (Fin n)) (vs : List (Fin n)) :
    good (stars neighbors vs) := by
  induction vs with
  | nil => simp [stars, good]
  | cons v vs ih =>
    simp only [stars, good_append]
    exact ⟨⟨ih, orChain_good _ _⟩, by simp [good]⟩

lemma stars_count {n : ℕ} (neighbors : Fin n → List (Fin n)) (vs : List (Fin n)) :
    countAnd (stars neighbors vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [stars, countAnd_append, ih, orChain_count]
    simp [countAnd]

lemma stars_eval {n : ℕ} (neighbors : Fin n → List (Fin n)) (vs : List (Fin n))
    (x : Fin n → Bool) :
    (run (stars neighbors vs) (List.ofFn x)).getD (n + (stars neighbors vs).length - 1) false =
      vs.any (fun v => x v && (neighbors v).any x) := by
  induction vs with
  | nil => simp [stars, run, GateOp.eval, List.getD]
  | cons v vs ih =>
    let gs := stars neighbors vs
    let ns := orChain (n + gs.length) ((neighbors v).map Fin.val)
    let ag : Gate := ⟨.and, [v.val, n + gs.length + (neighbors v).length]⟩
    let og : Gate := ⟨.or, [n + gs.length - 1, n + gs.length + ns.length]⟩
    have hgpos : 0 < gs.length := stars_nonempty neighbors vs
    have hnlen : ns.length = (neighbors v).length + 1 := by
      simp [ns, orChain_length]
    have hprev : (run (gs ++ ns ++ [ag]) (List.ofFn x)).getD
        (n + gs.length - 1) false = vs.any (fun v => x v && (neighbors v).any x) := by
      rw [run_append, run_old _ _ _ (by simp [run_length]; omega),
        run_append, run_old _ _ _ (by simp [run_length]; omega)]
      exact ih
    have hvertex : (run (gs ++ ns) (List.ofFn x)).getD v.val false = x v := by
      rw [run_old _ _ _ (by simpa using v.isLt)]
      simp [List.getD, v.isLt]
    have hneigh : (run (gs ++ ns) (List.ofFn x)).getD
        (n + gs.length + (neighbors v).length) false = (neighbors v).any x := by
      rw [run_append]
      have h := orChain_eval (n + gs.length) ((neighbors v).map Fin.val)
        (run gs (List.ofFn x)) (by simp [run_length]) (by
          intro i hi
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
          exact j.isLt.trans_le (Nat.le_add_right _ _))
      simp only [List.length_map, List.any_map] at h
      rw [h]
      apply List.any_congr rfl
      intro j
      change (run gs (List.ofFn x)).getD j.val false = x j
      rw [run_old _ _ _ (by simpa using j.isLt)]
      simp [List.getD, j.isLt]
    have hand : (run (gs ++ ns ++ [ag]) (List.ofFn x)).getD
        (n + gs.length + ns.length) false = (x v && (neighbors v).any x) := by
      have hidx : n + gs.length + ns.length =
          (List.ofFn x).length + (gs ++ ns).length := by simp [Nat.add_assoc]
      rw [hidx, run_last]
      simp only [ag, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, hvertex, hneigh]
    change (run (gs ++ ns ++ [ag, og]) (List.ofFn x)).getD
      (n + (gs ++ ns ++ [ag, og]).length - 1) false = _
    have hsplit : gs ++ ns ++ [ag, og] = (gs ++ ns ++ [ag]) ++ [og] := by
      simp
    rw [hsplit]
    have hidx : n + ((gs ++ ns ++ [ag]) ++ [og]).length - 1 =
        (List.ofFn x).length + (gs ++ ns ++ [ag]).length := by simp; omega
    rw [hidx, run_last]
    simp only [og, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, hprev, hand]
    exact Bool.or_comm _ _

lemma and_positions (gs : List Gate) :
    ∃ A : Finset ℕ, A.card ≤ countAnd gs ∧
      ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .and → j ∈ A := by
  classical
  induction gs with
  | nil => exact ⟨∅, by simp [countAnd], by simp⟩
  | cons g gs ih =>
    obtain ⟨A, hcard, hA⟩ := ih
    by_cases hg : g.op = .and
    · refine ⟨insert 0 (A.image Nat.succ), ?_, ?_⟩
      · calc
          (insert 0 (A.image Nat.succ)).card ≤ (A.image Nat.succ).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ countAnd gs + 1 := Nat.add_le_add_right
            ((Finset.card_image_le).trans hcard) 1
          _ = countAnd (g :: gs) := by simp [countAnd, hg, Nat.add_comm]
      · intro j h hj hop
        cases j with
        | zero => exact Finset.mem_insert_self _ _
        | succ j =>
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
            ⟨j, hA j h hj hop, rfl⟩)
    · refine ⟨A.image Nat.succ, ?_, ?_⟩
      · have hc : countAnd (g :: gs) = countAnd gs := by
          cases he : g.op <;> simp_all [countAnd]
        rw [hc]
        exact (Finset.card_image_le).trans hcard
      · intro j h hj hop
        cases j with
        | zero =>
          have he : g = h := Option.some.inj hj
          exact (hg (he ▸ hop)).elim
        | succ j => exact Finset.mem_image.mpr ⟨j, hA j h hj hop, rfl⟩

end PEqualNP.Outside.L_meta_214

theorem PEqualNP.Outside.L_meta_214 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ T.card ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
  classical
  intro n G T hcover
  let neighbors : Fin n → List (Fin n) :=
    fun v => (Finset.univ.filter (G.Adj v)).toList
  let vs := T.toList
  let gs := PEqualNP.Outside.L_meta_214.stars neighbors vs
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, n + gs.length - 1⟩
  refine ⟨C, PEqualNP.Outside.L_meta_214.stars_good neighbors vs, ?_, ?_⟩
  · obtain ⟨A, hcard, hA⟩ := PEqualNP.Outside.L_meta_214.and_positions gs
    refine ⟨A, ?_, hA⟩
    simpa [gs, PEqualNP.Outside.L_meta_214.stars_count, vs] using hcard
  · intro x
    change (PEqualNP.Outside.L_meta_214.run gs (List.ofFn x)).getD
      (n + gs.length - 1) false = true ↔ _
    rw [PEqualNP.Outside.L_meta_214.stars_eval]
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨u, hu, hxu, v, hv, hxv⟩
      have hadj : G.Adj u v := by simpa [neighbors] using hv
      exact ⟨u, v, hadj, hxu, hxv⟩
    · rintro ⟨u, v, hadj, hxu, hxv⟩
      rcases hcover u v hadj with hu | hv
      · exact ⟨u, by simpa [vs] using hu, hxu,
          v, by simpa [neighbors] using hadj, hxv⟩
      · exact ⟨v, by simpa [vs] using hv, hxv,
          u, by simpa [neighbors] using hadj.symm, hxu⟩
