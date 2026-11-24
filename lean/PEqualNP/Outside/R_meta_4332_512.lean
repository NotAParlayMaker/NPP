import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_4332_512
    (monotone :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ (C : Circuit) (wOut : ℕ),
        Monotone2 C → C.size ≤ 15 →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x ++ [false])).getD wOut false = f9 x) →
        False)
    (binaryLow :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      let seed9 : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [false]
      let validG : ℕ → BinaryGate → Prop := fun n t =>
        (∃ a b : Bool, t.op = fun x y => (x == a) && (y == b)) ∧
        t.left < n ∧ t.right < n ∧ t.left ≠ 9 ∧ t.right ≠ 9 ∧ t.left ≠ t.right
      ∀ (gs : List BinaryGate) (g : BinaryGate) (q : Bool),
        let p := (gs ++ [g]).flatMap fun t => [t.left, t.right]
        8 ≤ gs.length → gs.length ≤ 10 →
        (∀ (j : ℕ) (hj : j < gs.length), validG (10 + j) gs[j]) →
        validG (10 + gs.length) g →
        10 ≤ g.left → 10 ≤ g.right →
        (∀ i < gs.length, ∃ t ∈ (gs ++ [g]).drop (i + 1), t.left = 10 + i ∨ t.right = 10 + i) →
        16 ≤ gs.length + ((Finset.range 9).filter fun i => p.count i = 1).card →
        (∀ h ∈ gs ++ [g], h.left < 9 → h.right < 9 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1) →
        (∀ x : Fin 9 → Bool, (BinaryCircuit.eval ⟨gs ++ [g], 10 + gs.length⟩ (seed9 x) != q) = f9 x) →
        False)
    (binaryMid :
      let f9 : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      let seed9 : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [false]
      let validG : ℕ → BinaryGate → Prop := fun n t =>
        (∃ a b : Bool, t.op = fun x y => (x == a) && (y == b)) ∧
        t.left < n ∧ t.right < n ∧ t.left ≠ 9 ∧ t.right ≠ 9 ∧ t.left ≠ t.right
      ∀ (gs : List BinaryGate) (g : BinaryGate) (q : Bool),
        let p := (gs ++ [g]).flatMap fun t => [t.left, t.right]
        11 ≤ gs.length → gs.length ≤ 13 →
        (∀ (j : ℕ) (hj : j < gs.length), validG (10 + j) gs[j]) →
        validG (10 + gs.length) g →
        10 ≤ g.left → 10 ≤ g.right →
        (∀ i < gs.length, ∃ t ∈ (gs ++ [g]).drop (i + 1), t.left = 10 + i ∨ t.right = 10 + i) →
        16 ≤ gs.length + ((Finset.range 9).filter fun i => p.count i = 1).card →
        (∀ h ∈ gs ++ [g], h.left < 9 → h.right < 9 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1) →
        (∀ x : Fin 9 → Bool, (BinaryCircuit.eval ⟨gs ++ [g], 10 + gs.length⟩ (seed9 x) != q) = f9 x) →
        False) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8 := by
  intro f10 C wOut pol hfan hsz x7
  by_contra hAll
  push Not at hAll
  let f9 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let seed9 : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [false]
  let ext9 : (Fin 9 → Bool) → Fin 10 → Bool := fun x i =>
    if h : i.val < 9 then x ⟨i.val, h⟩ else false
  have hext9_list : ∀ x : Fin 9 → Bool, List.ofFn (ext9 x) = seed9 x := by
    intro x
    apply List.ext_getElem
    · simp [seed9]
    · intro i hi1 hi2
      simp only [List.getElem_ofFn, seed9]
      by_cases hlt : i < 9
      · rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn]; simp [ext9, hlt]
      · have hi9 : i = 9 := by simp at hi1; omega
        subst hi9
        rw [List.getElem_append_right (by simp)]; simp [ext9]
  have hfun9 : ∀ x : Fin 9 → Bool, ((C.wires (seed9 x)).getD wOut false != pol) = f9 x := by
    intro x
    have h1 := hAll (ext9 x) (by simp [ext9])
    dsimp only [x7, f10] at h1
    rw [hext9_list x] at h1
    have hf : (ext9 x 0 && ext9 x 1 || ext9 x 1 && ext9 x 2 || ext9 x 2 && ext9 x 3 || ext9 x 3 && ext9 x 4 || ext9 x 4 && ext9 x 0 ||
        ext9 x 0 && ext9 x 5 || ext9 x 1 && ext9 x 6 || ext9 x 2 && ext9 x 7 || ext9 x 3 && ext9 x 8 || ext9 x 4 && ext9 x 9 ||
        ext9 x 5 && ext9 x 7 || ext9 x 7 && ext9 x 9 || ext9 x 9 && ext9 x 6 || ext9 x 6 && ext9 x 8 || ext9 x 8 && ext9 x 5) = f9 x := by
      simp [ext9, f9]
    rw [hf] at h1
    cases hpol : pol
    · simp [hpol] at h1 ⊢; exact h1
    · simp [hpol] at h1 ⊢; exact h1
  let isNot : Gate → Bool := fun g => match g.op with | .not => true | _ => false
  by_cases hnoNot : C.gates.countP isNot = 0
  · have hmono : Monotone2 C := by
      intro g hg
      have hfg := hfan g hg
      refine ⟨?_, hfg.2⟩
      rcases hfg.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        rw [Set.mem_singleton_iff] at h
        have hpos : 0 < C.gates.countP isNot :=
          List.countP_pos_iff.mpr ⟨g, hg, by simp [isNot, h]⟩
        omega
    cases hpol : pol
    · exact monotone C wOut hmono hsz (fun x => by have := hfun9 x; rw [hpol, Bool.bne_false] at this; exact this)
    · -- Monotone circuit cannot compute !f9!
      let leW : List Bool → List Bool → Prop := fun a b =>
        a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
      have fold_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
          ∀ (a b : List Bool), leW a b →
          leW (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
              (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
        intro gs; induction gs with
        | nil => intro _ a b hab; exact hab
        | cons g r ih =>
          intro hgs a b hab
          simp only [List.foldl_cons]
          apply ih (fun t ht => hgs t (by simp [ht]))
          refine ⟨by simp [hab.1], fun i hi => ?_⟩
          by_cases hlt : i < a.length
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < b.length)]
            exact hab.2 i (by simpa [List.getD_eq_getElem?_getD] using hi)
          · by_cases heq : i = a.length
            · subst heq
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some] at hi
              simp only [List.getD_eq_getElem?_getD, hab.1, List.getElem?_append_right le_rfl, Nat.sub_self,
                List.getElem?_cons_zero, Option.getD_some]
              rcases hgs g (by simp) with h | h <;> rw [h] at hi ⊢
              · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hi ⊢
                rintro y ⟨k, hk, rfl⟩; exact hab.2 k (hi (a.getD k false) ⟨k, hk, rfl⟩)
              · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hi ⊢
                obtain ⟨_, ⟨k, hk, rfl⟩, hbk⟩ := hi; exact ⟨true, ⟨k, hk, hab.2 k hbk⟩, rfl⟩
            · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi; cases hi
      have h0 : (C.wires (seed9 (fun _ => false))).getD wOut false = true := by
        have := hfun9 (fun _ => false); rw [hpol] at this
        have hf0 : f9 (fun _ => false) = false := by decide
        rw [hf0] at this
        cases h : (C.wires (seed9 (fun _ => false))).getD wOut false with
        | false => rw [h] at this; simp at this
        | true => rfl
      have h1 : (C.wires (seed9 (fun _ => true))).getD wOut false = false := by
        have := hfun9 (fun _ => true); rw [hpol] at this
        have hf1 : f9 (fun _ => true) = true := by decide
        rw [hf1] at this
        cases h : (C.wires (seed9 (fun _ => true))).getD wOut false with
        | false => rfl
        | true => rw [h] at this; simp at this
      have hle01 : leW (seed9 (fun _ => false)) (seed9 (fun _ => true)) := by
        refine ⟨by simp [seed9], fun i hi => ?_⟩
        have hrep : seed9 (fun _ => false) = List.replicate 10 false := by decide
        rw [hrep, List.getD_eq_getElem?_getD, List.getElem?_replicate] at hi
        split_ifs at hi <;> simp at hi
      have hres := fold_mono C.gates (fun g hg => by
        have := (hmono g hg).1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; exact this)
        _ _ hle01
      have ht := hres.2 wOut h0
      unfold Circuit.wires at h1
      rw [h1] at ht; cases ht
  · have hposNot : 1 ≤ C.gates.countP isNot := by omega
    let validG : ℕ → BinaryGate → Prop := fun n t =>
      (∃ a b : Bool, t.op = fun x y => (x == a) && (y == b)) ∧
      t.left < n ∧ t.right < n ∧ t.left ≠ 9 ∧ t.right ≠ 9 ∧ t.left ≠ t.right
    let isNonNot : Gate → Bool := fun g => match g.op with | .not => false | _ => true
    have hcnt : C.gates.countP isNonNot ≤ 14 := by
      have hsum : ∀ (l : List Gate), l.countP isNonNot + l.countP isNot = l.length := by
        intro l
        induction l with
        | nil => rfl
        | cons g r ih =>
          rw [List.countP_cons, List.countP_cons, List.length_cons]
          cases h : g.op <;> simp [isNonNot, isNot, h] at ih ⊢ <;> omega
      have h1 := hsum C.gates
      unfold Circuit.size at hsz
      omega
    let upd2 : (Fin 9 → Bool) → Fin 9 → Fin 9 → Bool → Bool → Fin 9 → Bool :=
      fun x u v bu bv => Function.update (Function.update x u bu) v bv
    let maskVec : List (Fin 9) → Fin 9 → Bool := fun s w => decide (w ∈ s)
    have hpet_adj : ∀ u v : Fin 9, u ≠ v →
        ∃ a : Fin 9, a ≠ u ∧ a ≠ v ∧ f9 (maskVec [u, a]) = true ∧ f9 (maskVec [v, a]) = false := by
      decide
    have f9_nonconst_fix : ∀ (u : Fin 9) (b : Bool),
        ∃ (s1 s2 : List (Fin 9)), maskVec s1 u = b ∧ maskVec s2 u = b ∧ f9 (maskVec s1) ≠ f9 (maskVec s2) := by
      intro u b
      cases b
      · fin_cases u
        · exact ⟨[], [2, 3], by decide, by decide, by decide⟩
        · exact ⟨[], [2, 3], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[], [0, 1], by decide, by decide, by decide⟩
      · fin_cases u
        · exact ⟨[0], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[1], [0, 1], by decide, by decide, by decide⟩
        · exact ⟨[2], [1, 2], by decide, by decide, by decide⟩
        · exact ⟨[3], [2, 3], by decide, by decide, by decide⟩
        · exact ⟨[4], [3, 4], by decide, by decide, by decide⟩
        · exact ⟨[5], [0, 5], by decide, by decide, by decide⟩
        · exact ⟨[6], [1, 6], by decide, by decide, by decide⟩
        · exact ⟨[7], [2, 7], by decide, by decide, by decide⟩
        · exact ⟨[8], [3, 8], by decide, by decide, by decide⟩
    have f9_dep : ∀ u : Fin 9, ∃ s : List (Fin 9),
        f9 (maskVec s) ≠ f9 (Function.update (maskVec s) u (!maskVec s u)) := by
      intro u
      have h1 : ∀ w : Fin 9, ∃ v : Fin 9, v ≠ w ∧ f9 (maskVec [v]) = false ∧ f9 (maskVec [w, v]) = true := by decide
      obtain ⟨v, hne, hf, ht⟩ := h1 u
      refine ⟨[v], ?_⟩
      have heq : Function.update (maskVec [v]) u (!maskVec [v] u) = maskVec [u, v] := by
        funext w
        by_cases hwu : w = u
        · subst hwu; simp only [Function.update_self, maskVec, List.mem_cons, List.not_mem_nil, or_false,
            decide_eq_true_eq, true_or, decide_true, Bool.not_eq_true', decide_eq_false_iff_not]; exact hne.symm
        · rw [Function.update_of_ne hwu]
          simp only [maskVec, List.mem_cons, List.not_mem_nil, or_false, hwu, false_or]
      rw [heq, hf, ht]; decide
    have f9_pair_three : ∀ (u v : Fin 9), u ≠ v →
        ∃ (s1 s2 : List (Fin 9)),
          3 ≤ ({(f9 (upd2 (maskVec s1) u v false false), f9 (upd2 (maskVec s2) u v false false)),
                (f9 (upd2 (maskVec s1) u v false true),  f9 (upd2 (maskVec s2) u v false true)),
                (f9 (upd2 (maskVec s1) u v true false),  f9 (upd2 (maskVec s2) u v true false)),
                (f9 (upd2 (maskVec s1) u v true true),   f9 (upd2 (maskVec s2) u v true true))} : Finset (Bool × Bool)).card := by
      intro u v hne
      obtain ⟨a, hau, hav, hua, hva⟩ := hpet_adj u v hne
      obtain ⟨b, hbv, hbu, hvb, hub⟩ := hpet_adj v u hne.symm
      have hf9_one : ∀ c : Fin 9, f9 (maskVec [c]) = false := by decide
      have hupd_ff : ∀ c : Fin 9, c ≠ u → c ≠ v → upd2 (maskVec [c]) u v false false = maskVec [c] := by
        intro c hcu hcv; funext w; dsimp only [upd2, maskVec]
        by_cases hwv : w = v
        · subst hwv; rw [Function.update_self]; simp [hcv.symm]
        · rw [Function.update_of_ne hwv]
          by_cases hwu : w = u
          · subst hwu; rw [Function.update_self]; simp [hcu.symm]
          · rw [Function.update_of_ne hwu]
      have hupd_ft : ∀ c : Fin 9, c ≠ u → c ≠ v → upd2 (maskVec [c]) u v false true = maskVec [v, c] := by
        intro c hcu hcv; funext w; dsimp only [upd2, maskVec]
        by_cases hwv : w = v
        · subst hwv; rw [Function.update_self]; simp
        · rw [Function.update_of_ne hwv]
          by_cases hwu : w = u
          · subst hwu; rw [Function.update_self]; simp [hne, hcu.symm]
          · rw [Function.update_of_ne hwu]; simp [hwv]
      have hupd_tf : ∀ c : Fin 9, c ≠ u → c ≠ v → upd2 (maskVec [c]) u v true false = maskVec [u, c] := by
        intro c hcu hcv; funext w; dsimp only [upd2, maskVec]
        by_cases hwv : w = v
        · subst hwv; rw [Function.update_self]; simp [hne.symm, hcv.symm]
        · rw [Function.update_of_ne hwv]
          by_cases hwu : w = u
          · subst hwu; rw [Function.update_self]; simp
          · rw [Function.update_of_ne hwu]; simp [hwu]
      refine ⟨[a], [b], ?_⟩
      have hff1 : f9 (upd2 (maskVec [a]) u v false false) = false := by rw [hupd_ff a hau hav]; exact hf9_one a
      have hft1 : f9 (upd2 (maskVec [a]) u v false true) = false := by rw [hupd_ft a hau hav]; exact hva
      have htf1 : f9 (upd2 (maskVec [a]) u v true false) = true := by rw [hupd_tf a hau hav]; exact hua
      have hff2 : f9 (upd2 (maskVec [b]) u v false false) = false := by rw [hupd_ff b hbu hbv]; exact hf9_one b
      have hft2 : f9 (upd2 (maskVec [b]) u v false true) = true := by rw [hupd_ft b hbu hbv]; exact hvb
      have htf2 : f9 (upd2 (maskVec [b]) u v true false) = false := by rw [hupd_tf b hbu hbv]; exact hub
      rw [hff1, hft1, htf1, hff2, hft2, htf2]
      cases f9 (upd2 (maskVec [a]) u v true true) <;> cases f9 (upd2 (maskVec [b]) u v true true) <;> decide
    have pigeonhole_bool : ∀ (h : Bool → Bool → Bool) (F : Bool → Bool → Bool × Bool),
        3 ≤ ({F false false, F false true, F true false, F true true} : Finset (Bool × Bool)).card →
        ∃ p1 p2 : Bool × Bool, h p1.1 p1.2 = h p2.1 p2.2 ∧ F p1.1 p1.2 ≠ F p2.1 p2.2 := by
      intro h F hcard
      by_contra hno; push Not at hno
      let S : Finset (Bool × Bool) := {F false false, F false true, F true false, F true true}
      have hsub : S ⊆ ({false, true} : Finset Bool).image (fun b =>
          if h0 : ∃ p : Bool × Bool, h p.1 p.2 = b then F h0.choose.1 h0.choose.2 else (false, false)) := by
        intro y hy
        have hex : ∃ p : Bool × Bool, F p.1 p.2 = y := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl | rfl
          · exact ⟨(false, false), rfl⟩
          · exact ⟨(false, true), rfl⟩
          · exact ⟨(true, false), rfl⟩
          · exact ⟨(true, true), rfl⟩
        obtain ⟨p, rfl⟩ := hex
        rw [Finset.mem_image]
        refine ⟨h p.1 p.2, by cases h p.1 p.2 <;> simp, ?_⟩
        have h0 : ∃ q : Bool × Bool, h q.1 q.2 = h p.1 p.2 := ⟨p, rfl⟩
        rw [dif_pos h0]
        exact hno h0.choose p h0.choose_spec
      have hle := Finset.card_le_card hsub
      dsimp only [S] at hle
      have him := Finset.card_image_le (s := ({false, true} : Finset Bool))
        (f := fun b => if h0 : ∃ p : Bool × Bool, h p.1 p.2 = b then F h0.choose.1 h0.choose.2 else (false, false))
      have h2 : ({false, true} : Finset Bool).card = 2 := by decide
      omega
    have bcWires_len : ∀ (gs : List BinaryGate) (acc : List Bool),
        (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) acc).length =
          acc.length + gs.length := by
      intro gs; induction gs with
      | nil => intro acc; simp
      | cons g r ih => intro acc; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega
    have bcWires_prefix : ∀ (gs : List BinaryGate) (acc : List Bool) (w : ℕ), w < acc.length →
        (gs.foldl (fun ws g => ws ++ [g.op (ws.getD g.left false) (ws.getD g.right false)]) acc).getD w false = acc.getD w false := by
      intro gs; induction gs with
      | nil => intro acc w _; rfl
      | cons g r ih =>
        intro acc w hw; simp only [List.foldl_cons]
        have hlen : w < (acc ++ [g.op (acc.getD g.left false) (acc.getD g.right false)]).length := by simp; omega
        rw [ih _ w hlen]; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]
    have bcWires_append : ∀ (gs1 gs2 : List BinaryGate) (x : List Bool),
        BinaryCircuit.wires ⟨gs1 ++ gs2, 0⟩ x =
          gs2.foldl (fun ws g => ws ++ [g.op (ws.getD g.left false) (ws.getD g.right false)])
            (BinaryCircuit.wires ⟨gs1, 0⟩ x) := by
      intro gs1 gs2 x; unfold BinaryCircuit.wires; exact List.foldl_append
    have bcWires_gate : ∀ (gs : List BinaryGate) (j : ℕ) (hj : j < gs.length) (x : Fin 9 → Bool),
        gs[j].left < 10 + j → gs[j].right < 10 + j →
        (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (10 + j) false =
          gs[j].op ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD gs[j].left false)
                   ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD gs[j].right false) := by
      intro gs j hj x hleft hright
      let step : List Bool → BinaryGate → List Bool := fun ws g => ws ++ [g.op (ws.getD g.left false) (ws.getD g.right false)]
      have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
        have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
        have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
        calc gs = gs.take j ++ gs.drop j := h1.symm
          _ = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by rw [h2]
          _ = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by simp
      set acc := (gs.take j).foldl step (seed9 x)
      have haccLen : acc.length = 10 + j := by
        dsimp only [acc]; rw [bcWires_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; simp [seed9]
      have haccAt : ∀ u < 10 + j, (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD u false = acc.getD u false := by
        intro u hu; unfold BinaryCircuit.wires; conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hu2 : u < (step acc gs[j]).length := by simp [step]; omega
        rw [bcWires_prefix (gs.drop (j + 1)) _ u hu2]
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : u < acc.length)]
      conv_lhs => unfold BinaryCircuit.wires; rw [hsplit]
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hjlt : 10 + j < (step acc gs[j]).length := by simp [step, haccLen]
      rw [bcWires_prefix (gs.drop (j + 1)) _ (10 + j) hjlt]
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
      simp only [haccLen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      simp only [List.getD_eq_getElem?_getD] at haccAt
      rw [haccAt gs[j].left hleft, haccAt gs[j].right hright]
    have seed9_len : ∀ x : Fin 9 → Bool, (seed9 x).length = 10 := by
      intro x; simp [seed9]
    have seed9_getD : ∀ (x : Fin 9 → Bool) (w : ℕ) (hw : w < 9), (seed9 x).getD w false = x ⟨w, hw⟩ := by
      intro x w hw; dsimp only [seed9]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hw]), List.getElem?_ofFn]; simp [hw]
    have seed9_getD_nine : ∀ (x : Fin 9 → Bool), (seed9 x).getD 9 false = false := by
      intro x; dsimp only [seed9]; simp [List.getD_eq_getElem?_getD]
    have compile_step : ∀ (gs : List BinaryGate) (wireMap : List (ℕ × Bool)) (g : Gate),
        (g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ (j : ℕ) (hj : j < gs.length), validG (10 + j) gs[j]) →
        (∀ p ∈ wireMap, p.1 < 10 + gs.length) →
        ∃ (gs' : List BinaryGate) (p : ℕ × Bool),
          gs.length ≤ gs'.length ∧
          gs'.length ≤ gs.length + (if isNonNot g then 1 else 0) ∧
          (∀ (j : ℕ) (hj : j < gs'.length), validG (10 + j) gs'[j]) ∧
          p.1 < 10 + gs'.length ∧
          (∀ (x : Fin 9 → Bool) (w : ℕ), w < 10 + gs.length →
            (BinaryCircuit.wires ⟨gs', 0⟩ (seed9 x)).getD w false = (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD w false) ∧
          (∀ (x : Fin 9 → Bool) (ws : List Bool), ws.length = wireMap.length →
            (∀ w < wireMap.length, ws.getD w false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (wireMap.getD w (9, false)).1 false != (wireMap.getD w (9, false)).2)) →
            g.op.eval (g.inputs.map fun i => ws.getD i false) =
              ((BinaryCircuit.wires ⟨gs', 0⟩ (seed9 x)).getD p.1 false != p.2)) := by
      intro gs wireMap g hfg hvalid haliasBound
      have h9val : ∀ x : Fin 9 → Bool, (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD 9 false = false := by
        intro x; unfold BinaryCircuit.wires; rw [bcWires_prefix gs (seed9 x) 9 (by simp [seed9]), seed9_getD_nine]
      have hread : ∀ (u : ℕ) (x : Fin 9 → Bool) (ws : List Bool), ws.length = wireMap.length →
          (∀ w < wireMap.length, ws.getD w false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (wireMap.getD w (9, false)).1 false != (wireMap.getD w (9, false)).2)) →
          ws.getD u false = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (wireMap.getD u (9, false)).1 false != (wireMap.getD u (9, false)).2) := by
        intro u x ws hlen hws
        by_cases hu : u < wireMap.length
        · exact hws u hu
        · have h1 : ws.getD u false = false := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ u)]
          have h2 : wireMap.getD u (9, false) = (9, false) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wireMap.length ≤ u)]
          rw [h1, h2, h9val x]; rfl
      have haliasGet : ∀ u, (wireMap.getD u (9, false)).1 < 10 + gs.length := by
        intro u
        by_cases hu : u < wireMap.length
        · have hmem : wireMap.getD u (9, false) ∈ wireMap := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]; exact List.getElem_mem hu
          exact haliasBound _ hmem
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : wireMap.length ≤ u), Option.getD_none]; omega
      rcases hfg.1 with hop | hop | hop
      · have hnn : isNonNot g = true := by simp [isNonNot, hop]
        cases hgin : g.inputs with
        | nil => refine ⟨gs, (9, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws _ _ => by rw [hop, h9val x]; rfl⟩
        | cons u1 tl =>
          cases tl with
          | nil =>
            refine ⟨gs, wireMap.getD u1 (9, false), le_rfl, by simp [hnn], hvalid, haliasGet u1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
            simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hread u1 x ws hlen hws
          | cons u2 tl2 =>
            cases tl2 with
            | nil =>
              let p1 := wireMap.getD u1 (9, false)
              let p2 := wireMap.getD u2 (9, false)
              have hp1 : p1.1 < 10 + gs.length := haliasGet u1
              have hp2 : p2.1 < 10 + gs.length := haliasGet u2
              by_cases h9 : p1.1 = 9
              · by_cases hf1 : p1.2 = false
                · refine ⟨gs, (9, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1 x ws hlen hws]
                  change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false != p1.2) && _) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD 9 false != false)
                  rw [h9, hf1, h9val x]; rfl
                · refine ⟨gs, p2, le_rfl, by simp [hnn], hvalid, hp2, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  have hf1t : p1.2 = true := by cases h : p1.2 with | false => exact False.elim (hf1 h) | true => rfl
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                  change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false != p1.2) && _) = _
                  rw [h9, hf1t, h9val x]; rfl
              · by_cases h20 : p2.1 = 9
                · by_cases hf2 : p2.2 = false
                  · refine ⟨gs, (9, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                    simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u2 x ws hlen hws]
                    change (_ && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2)) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD 9 false != false)
                    rw [h20, hf2, h9val x]; simp
                  · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                    have hf2t : p2.2 = true := by cases h : p2.2 with | false => exact False.elim (hf2 h) | true => rfl
                    simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                    change (_ && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2)) = _
                    rw [h20, hf2t, h9val x]; simp [p1]
                · by_cases heq : p1.1 = p2.1
                  · by_cases hf : p1.2 = p2.2
                    · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                      simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                      rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                      change ((_ != p1.2) && (_ != p2.2)) = (_ != p1.2)
                      rw [heq, hf]; cases ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2) <;> rfl
                    · refine ⟨gs, (9, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                      simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                      rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws, h9val x]
                      change ((_ != p1.2) && (_ != p2.2)) = false
                      rw [heq]; cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false <;> cases h1 : p1.2 <;> cases h2 : p2.2 <;> first | rfl | exact False.elim (hf (h1.trans h2.symm))
                  · let ng : BinaryGate := ⟨fun a b => (a == !p1.2) && (b == !p2.2), p1.1, p2.1⟩
                    refine ⟨gs ++ [ng], (10 + gs.length, false), by simp, by simp [hnn], ?_, by simp, ?_, ?_⟩
                    · intro j hj; rw [List.length_append, List.length_singleton] at hj
                      by_cases hltj : j < gs.length
                      · rw [List.getElem_append_left hltj]; exact hvalid j hltj
                      · have hjeq : j = gs.length := by omega
                        subst hjeq; rw [List.getElem_append_right le_rfl]; simp only [Nat.sub_self, List.getElem_cons_zero]
                        exact ⟨⟨!p1.2, !p2.2, rfl⟩, hp1, hp2, h9, h20, heq⟩
                    · intro x w hw; rw [bcWires_append]; simp only [List.foldl_cons, List.foldl_nil]
                      have hlen : w < (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).length := by
                        unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed9]; omega
                      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
                    · intro x ws hlen hws
                      simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.bne_false]
                      rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws, bcWires_append]
                      simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
                      have hlenW : (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).length = 10 + gs.length := by
                        unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed9]
                      rw [List.getElem?_append_right (by omega)]
                      simp only [hlenW, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ng, ← List.getD_eq_getElem?_getD]
                      change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false != p1.2) && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2)) =
                        (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false == !p1.2) && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false == !p2.2))
                      cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false <;>
                        cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false <;>
                        cases p1.2 <;> cases p2.2 <;> rfl
            | cons _ _ => have := hfg.2; rw [hgin] at this; simp at this
      · have hnn : isNonNot g = true := by simp [isNonNot, hop]
        cases hgin : g.inputs with
        | nil => refine ⟨gs, (9, false), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws _ _ => by rw [hop, h9val x]; rfl⟩
        | cons u1 tl =>
          cases tl with
          | nil =>
            refine ⟨gs, wireMap.getD u1 (9, false), le_rfl, by simp [hnn], hvalid, haliasGet u1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
            simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hread u1 x ws hlen hws
          | cons u2 tl2 =>
            cases tl2 with
            | nil =>
              let p1 := wireMap.getD u1 (9, false)
              let p2 := wireMap.getD u2 (9, false)
              have hp1 : p1.1 < 10 + gs.length := haliasGet u1
              have hp2 : p2.1 < 10 + gs.length := haliasGet u2
              by_cases h9 : p1.1 = 9
              · by_cases hf1 : p1.2 = true
                · refine ⟨gs, (9, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1 x ws hlen hws]
                  change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false != p1.2) || _) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD 9 false != true)
                  rw [h9, hf1, h9val x]; rfl
                · refine ⟨gs, p2, le_rfl, by simp [hnn], hvalid, hp2, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                  have hf1f : p1.2 = false := by cases h : p1.2 with | false => rfl | true => exact False.elim (hf1 h)
                  simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                  change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false != p1.2) || _) = _
                  rw [h9, hf1f, h9val x]; rfl
              · by_cases h20 : p2.1 = 9
                · by_cases hf2 : p2.2 = true
                  · refine ⟨gs, (9, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                    simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u2 x ws hlen hws]
                    change (_ || ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2)) = ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD 9 false != true)
                    rw [h20, hf2, h9val x]; simp
                  · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                    have hf2f : p2.2 = false := by cases h : p2.2 with | false => rfl | true => exact False.elim (hf2 h)
                    simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                    change (_ || ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2)) = _
                    rw [h20, hf2f, h9val x]; simp [p1]
                · by_cases heq : p1.1 = p2.1
                  · by_cases hf : p1.2 = p2.2
                    · refine ⟨gs, p1, le_rfl, by simp [hnn], hvalid, hp1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                      simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws]
                      change ((_ != p1.2) || (_ != p2.2)) = (_ != p1.2)
                      rw [heq, hf]; cases ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2) <;> rfl
                    · refine ⟨gs, (9, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
                      simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws, h9val x]
                      change ((_ != p1.2) || (_ != p2.2)) = true
                      rw [heq]; cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false <;> cases h1 : p1.2 <;> cases h2 : p2.2 <;> first | rfl | exact False.elim (hf (h1.trans h2.symm))
                  · let ng : BinaryGate := ⟨fun a b => (a == p1.2) && (b == p2.2), p1.1, p2.1⟩
                    refine ⟨gs ++ [ng], (10 + gs.length, true), by simp, by simp [hnn], ?_, by simp, ?_, ?_⟩
                    · intro j hj; rw [List.length_append, List.length_singleton] at hj
                      by_cases hltj : j < gs.length
                      · rw [List.getElem_append_left hltj]; exact hvalid j hltj
                      · have hjeq : j = gs.length := by omega
                        subst hjeq; rw [List.getElem_append_right le_rfl]; simp only [Nat.sub_self, List.getElem_cons_zero]
                        exact ⟨⟨p1.2, p2.2, rfl⟩, hp1, hp2, h9, h20, heq⟩
                    · intro x w hw; rw [bcWires_append]; simp only [List.foldl_cons, List.foldl_nil]
                      have hlen : w < (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).length := by
                        unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed9]; omega
                      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
                    · intro x ws hlen hws
                      simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                      rw [hread u1 x ws hlen hws, hread u2 x ws hlen hws, bcWires_append]
                      simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
                      have hlenW : (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).length = 10 + gs.length := by
                        unfold BinaryCircuit.wires; rw [bcWires_len]; simp [seed9]
                      rw [List.getElem?_append_right (by omega)]
                      simp only [hlenW, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, ng, ← List.getD_eq_getElem?_getD]
                      change (((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false != p1.2) || ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false != p2.2)) =
                        ((((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false == p1.2) && ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false == p2.2)) != true)
                      cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false <;>
                        cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p2.1 false <;>
                        cases p1.2 <;> cases p2.2 <;> rfl
            | cons _ _ => have := hfg.2; rw [hgin] at this; simp at this
      · rw [Set.mem_singleton_iff] at hop
        have hnn : isNonNot g = false := by simp [isNonNot, hop]
        cases hgin : g.inputs with
        | nil => refine ⟨gs, (9, true), le_rfl, by simp [hnn], hvalid, by omega, fun _ _ _ => rfl, fun x ws _ _ => by rw [hop, h9val x]; rfl⟩
        | cons u1 tl =>
          let p1 := wireMap.getD u1 (9, false)
          refine ⟨gs, (p1.1, !p1.2), le_rfl, by simp [hnn], hvalid, haliasGet u1, fun _ _ _ => rfl, fun x ws hlen hws => ?_⟩
          simp only [hop, GateOp.eval, List.map_cons, List.headD_cons]
          rw [hread u1 x ws hlen hws]
          cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p1.1 false <;> cases p1.2 <;> rfl
    have compile_list : ∀ (cgs : List Gate),
        (∀ g ∈ cgs, g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        ∃ (gs : List BinaryGate) (wireMap : List (ℕ × Bool)),
          gs.length ≤ cgs.countP isNonNot ∧ wireMap.length = 10 + cgs.length ∧
          (∀ (j : ℕ) (hj : j < gs.length), validG (10 + j) gs[j]) ∧
          (∀ p ∈ wireMap, p.1 < 10 + gs.length) ∧
          ∀ (x : Fin 9 → Bool) (w : ℕ), w < 10 + cgs.length →
            (cgs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (seed9 x)).getD w false =
              ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (wireMap.getD w (9, false)).1 false != (wireMap.getD w (9, false)).2) := by
      intro cgs
      induction cgs using List.reverseRecOn with
      | nil =>
        intro _
        refine ⟨[], (List.range 10).map fun i => (i, false), by simp, by simp, by simp, ?_, ?_⟩
        · intro p hp; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; have := List.mem_range.mp hi; omega
        · intro x w hw
          have hw10 : w < 10 := by simp at hw; omega
          simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
          have h2 : ((List.range 10).map fun i => (i, false))[w]?.getD (9, false) = (w, false) := by
            simp [List.getElem?_map, List.getElem?_range hw10]
          rw [h2]
          simp only [BinaryCircuit.wires, List.foldl_nil, Bool.bne_false]
      | append_singleton cgs g ih =>
        intro hfc
        have hfan1 : ∀ g' ∈ cgs, g'.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
          fun g' hg' => hfc g' (List.mem_append_left _ hg')
        have hfanG := hfc g (List.mem_append_right _ (List.mem_singleton_self g))
        obtain ⟨gs, wireMap, hlen, halen, hvalid, hbound, heval⟩ := ih hfan1
        obtain ⟨gs', p, hge, hlen', hvalid', hp, hpres, hstep⟩ := compile_step gs wireMap g hfanG hvalid hbound
        refine ⟨gs', wireMap ++ [p], ?_, by simp [halen]; omega, hvalid', ?_, ?_⟩
        · rw [List.countP_append, List.countP_singleton]; omega
        · intro q hq; rcases List.mem_append.mp hq with h1 | h2
          · have := hbound q h1; omega
          · rw [List.mem_singleton.mp h2]; exact hp
        · intro x w hw
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          set ws := cgs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (seed9 x)
          have hwsLen : ws.length = 10 + cgs.length := by
            suffices h : ∀ (l : List Gate) (acc : List Bool),
                (l.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).length = acc.length + l.length by
              rw [h, seed9_len]
            intro l; induction l with
            | nil => intro acc; simp
            | cons a r ihr => intro acc; simp only [List.foldl_cons, ihr, List.length_append, List.length_cons, List.length_nil]; omega
          by_cases hltw : w < 10 + cgs.length
          · have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD w false = ws.getD w false := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < ws.length)]
            have h2 : (wireMap ++ [p]).getD w (9, false) = wireMap.getD w (9, false) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : w < wireMap.length)]
            rw [h1, h2, heval x w hltw]
            have hpw : (wireMap.getD w (9, false)).1 < 10 + gs.length := by
              have hmem : wireMap.getD w (9, false) ∈ wireMap := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : w < wireMap.length), Option.getD_some]
                exact List.getElem_mem _
              exact hbound _ hmem
            rw [hpres x _ hpw]
          · have hweq : w = 10 + cgs.length := by simp at hw; omega
            subst hweq
            have h1 : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD (10 + cgs.length) false =
                g.op.eval (g.inputs.map fun i => ws.getD i false) := by
              simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right (by omega)]; simp [hwsLen]
            have h2 : (wireMap ++ [p]).getD (10 + cgs.length) (9, false) = p := by
              simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_right (by omega)]; simp [halen]
            rw [h1, h2]; exact hstep x ws (by omega) (fun u hu => heval x u (by omega))
    have hexValid : ∃ k : ℕ, k ≤ 14 ∧ ∃ (all : List BinaryGate) (q : Bool),
        all.length = k ∧ 1 ≤ k ∧ (∀ (j : ℕ) (hj : j < all.length), validG (10 + j) all[j]) ∧
        ∀ x : Fin 9 → Bool, (BinaryCircuit.eval ⟨all, 10 + (k - 1)⟩ (seed9 x) != q) = f9 x := by
      obtain ⟨gs, wireMap, hlen, halen, hvalid, hbound, heval⟩ := compile_list C.gates hfan
      have hnotConst : ∀ c : Bool, ¬ ∀ x : Fin 9 → Bool, f9 x = c := by
        intro c hc; have h0 := hc (maskVec []); have h1 := hc (maskVec [0, 1])
        have : f9 (maskVec []) ≠ f9 (maskVec [0, 1]) := by decide
        exact this (h0.trans h1.symm)
      have hnotInput : ∀ (i : Fin 9) (q : Bool), ¬ ∀ x : Fin 9 → Bool, (x i != q) = f9 x := by
        intro i q hq; obtain ⟨s1, s2, hs1, hs2, hne⟩ := f9_nonconst_fix i false
        have h1 := hq (maskVec s1); have h2 := hq (maskVec s2)
        rw [hs1] at h1; rw [hs2] at h2; exact hne (h1.symm.trans h2)
      by_cases hout : wOut < 10 + C.gates.length
      · let p := wireMap.getD wOut (9, false)
        have hp : p.1 < 10 + gs.length := by
          have hmem : p ∈ wireMap := by
            dsimp only [p]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : wOut < wireMap.length), Option.getD_some]
            exact List.getElem_mem _
          exact hbound _ hmem
        have hceval : ∀ x : Fin 9 → Bool, ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p.1 false != (p.2 != pol)) = f9 x := by
          intro x
          have h1 : ((C.wires (seed9 x)).getD wOut false != pol) = f9 x := hfun9 x
          unfold Circuit.wires at h1
          rw [← h1, heval x wOut hout]
          cases (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD p.1 false <;> cases p.2 <;> cases pol <;> rfl
        by_cases hp9 : p.1 < 9
        · exfalso; apply hnotInput ⟨p.1, hp9⟩ (p.2 != pol); intro x; rw [← hceval x]
          unfold BinaryCircuit.wires; rw [bcWires_prefix gs (seed9 x) p.1 (by simp [seed9]; omega), seed9_getD x p.1 hp9]
        · by_cases hpeq9 : p.1 = 9
          · exfalso; apply hnotConst (p.2 != pol); intro x; rw [← hceval x, hpeq9]
            unfold BinaryCircuit.wires; rw [bcWires_prefix gs (seed9 x) 9 (by simp [seed9]), seed9_getD_nine]; simp
          · let idx := p.1 - 10
            have hidx : idx < gs.length := by omega
            let all := gs.take (idx + 1)
            have hallLen : all.length = idx + 1 := by rw [List.length_take, Nat.min_eq_left (by omega)]
            refine ⟨idx + 1, by omega, all, p.2 != pol, hallLen, by omega, ?_, ?_⟩
            · intro j hj; have hget : all[j] = gs[j] := List.getElem_take; rw [hget]; exact hvalid j (by omega)
            · intro x; rw [← hceval x]; have hpeq : p.1 = 10 + idx := by omega
              rw [hpeq, show idx + 1 - 1 = idx by omega]
              change ((BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).getD (10 + idx) false != (p.2 != pol)) =
                ((BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (10 + idx) false != (p.2 != pol))
              have hsplit : gs = all ++ gs.drop (idx + 1) := (List.take_append_drop (idx + 1) gs).symm
              have hsame : (BinaryCircuit.wires ⟨gs, 0⟩ (seed9 x)).getD (10 + idx) false =
                  (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).getD (10 + idx) false := by
                conv_lhs => rw [hsplit]; rw [bcWires_append]
                have hlenAll : 10 + idx < (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).length := by
                  unfold BinaryCircuit.wires; rw [bcWires_len, hallLen]; simp [seed9]
                exact bcWires_prefix (gs.drop (idx + 1)) _ (10 + idx) hlenAll
              rw [hsame]
      · exfalso; apply hnotConst pol; intro x
        have h1 : ((C.wires (seed9 x)).getD wOut false != pol) = f9 x := hfun9 x
        unfold Circuit.wires at h1; rw [← h1]
        have hlenW : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (seed9 x)).length = 10 + C.gates.length := by
          suffices h : ∀ (l : List Gate) (acc : List Bool),
              (l.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) acc).length = acc.length + l.length by
            rw [h, seed9_len]
          intro l; induction l with
          | nil => intro acc; simp
          | cons a r ihr => intro acc; simp only [List.foldl_cons, ihr, List.length_append, List.length_cons, List.length_nil]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenW]; omega)]; simp
    let shiftWire : ℕ → ℕ → ℕ := fun cut w => if w > cut then w - 1 else w
    let shiftGate : ℕ → BinaryGate → BinaryGate := fun cut t => ⟨t.op, shiftWire cut t.left, shiftWire cut t.right⟩
    have delete_unused : ∀ (all : List BinaryGate) (i : ℕ) (hi : i + 1 < all.length),
        (∀ (j : ℕ) (hj : j < all.length), validG (10 + j) all[j]) →
        (∀ t ∈ all.drop (i + 1), t.left ≠ 10 + i ∧ t.right ≠ 10 + i) →
        let all' := all.take i ++ (all.drop (i + 1)).map (shiftGate (10 + i))
        all'.length = all.length - 1 ∧
        (∀ (j : ℕ) (hj : j < all'.length), validG (10 + j) all'[j]) ∧
        ∀ x : Fin 9 → Bool,
          BinaryCircuit.eval ⟨all', 10 + (all.length - 2)⟩ (seed9 x) =
          BinaryCircuit.eval ⟨all, 10 + (all.length - 1)⟩ (seed9 x) := by
      intro all i hi hvalid hunused
      let all' := all.take i ++ (all.drop (i + 1)).map (shiftGate (10 + i))
      have hlen' : all'.length = all.length - 1 := by
        dsimp only [all']; rw [List.length_append, List.length_take, List.length_map, List.length_drop]; omega
      refine ⟨hlen', ?_, ?_⟩
      · intro j hj
        by_cases hltj : j < i
        · have hget : all'[j] = all[j] := by
            dsimp only [all']; rw [List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take]
          rw [hget]; exact hvalid j (by omega)
        · have hj' : j < all.length - 1 := hlen' ▸ hj
          have hj1 : j + 1 < all.length := by omega
          have hget : all'[j] = shiftGate (10 + i) all[j + 1] := by
            dsimp only [all']; have htl : (all.take i).length = i := by rw [List.length_take]; omega
            rw [List.getElem_append_right (by omega)]; simp only [List.getElem_map, List.getElem_drop, htl]; congr 2; omega
          rw [hget]
          obtain ⟨hop, hl, hr, hl10, hr10, hne⟩ := hvalid (j + 1) hj1
          have hmem : all[j + 1] ∈ all.drop (i + 1) := by
            have : all[j + 1] = (all.drop (i + 1))[j - i]'(by rw [List.length_drop]; omega) := by
              simp only [List.getElem_drop]; congr 1; omega
            rw [this]; exact List.getElem_mem _
          obtain ⟨hln, hrn⟩ := hunused _ hmem
          refine ⟨hop, ?_, ?_, ?_, ?_, ?_⟩ <;> (dsimp only [shiftGate, shiftWire]; split_ifs <;> omega)
      · intro x
        have hwire : ∀ w < 10 + all'.length,
            (BinaryCircuit.wires ⟨all', 0⟩ (seed9 x)).getD w false =
              (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).getD (if w ≥ 10 + i then w + 1 else w) false := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hw
            by_cases hlt9 : w < 9
            · rw [if_neg (by omega : ¬ w ≥ 10 + i)]; unfold BinaryCircuit.wires
              rw [bcWires_prefix all' (seed9 x) w (by simp [seed9]; omega),
                  bcWires_prefix all (seed9 x) w (by simp [seed9]; omega)]
            · by_cases h9 : w = 9
              · subst h9; rw [if_neg (by omega : ¬ 9 ≥ 10 + i)]; unfold BinaryCircuit.wires
                rw [bcWires_prefix all' (seed9 x) 9 (by simp [seed9]),
                    bcWires_prefix all (seed9 x) 9 (by simp [seed9])]
              · let j := w - 10
                have hj : j < all'.length := by omega
                have hwj : w = 10 + j := by omega
                rw [hwj]
                by_cases hji : j < i
                · rw [if_neg (by omega : ¬ 10 + j ≥ 10 + i)]
                  have hget : all'[j] = all[j] := by
                    dsimp only [all']; rw [List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take]
                  obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j (by omega)
                  rw [bcWires_gate all' j hj x (by rw [hget]; exact hl) (by rw [hget]; exact hr),
                      bcWires_gate all j (by omega) x hl hr, hget]
                  have hL := ih all[j].left (by omega) (by omega); rw [if_neg (by omega)] at hL
                  have hR := ih all[j].right (by omega) (by omega); rw [if_neg (by omega)] at hR
                  rw [hL, hR]
                · rw [if_pos (by omega : 10 + j ≥ 10 + i), show 10 + j + 1 = 10 + (j + 1) by omega]
                  have hget : all'[j] = shiftGate (10 + i) all[j + 1] := by
                    dsimp only [all']; have htl : (all.take i).length = i := by rw [List.length_take]; omega
                    rw [List.getElem_append_right (by omega)]; simp only [List.getElem_map, List.getElem_drop, htl]; congr 2; omega
                  obtain ⟨_, hl, hr, _, _, _⟩ := hvalid (j + 1) (by omega)
                  have hmem : all[j + 1] ∈ all.drop (i + 1) := by
                    have : all[j + 1] = (all.drop (i + 1))[j - i]'(by rw [List.length_drop]; omega) := by
                      simp only [List.getElem_drop]; congr 1; omega
                    rw [this]; exact List.getElem_mem _
                  obtain ⟨hln, hrn⟩ := hunused _ hmem
                  have hl' : (shiftGate (10 + i) all[j + 1]).left < 10 + j := by dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
                  have hr' : (shiftGate (10 + i) all[j + 1]).right < 10 + j := by dsimp only [shiftGate, shiftWire]; split_ifs <;> omega
                  rw [bcWires_gate all' j hj x (by rw [hget]; exact hl') (by rw [hget]; exact hr'),
                      bcWires_gate all (j + 1) (by omega) x hl hr, hget]
                  dsimp only [shiftGate] at hl' hr' ⊢
                  have hihL := ih (shiftWire (10 + i) all[j + 1].left) (by omega) (by omega)
                  have hihR := ih (shiftWire (10 + i) all[j + 1].right) (by omega) (by omega)
                  have hinvL : (if shiftWire (10 + i) all[j + 1].left ≥ 10 + i then shiftWire (10 + i) all[j + 1].left + 1 else shiftWire (10 + i) all[j + 1].left) = all[j + 1].left := by
                    dsimp only [shiftWire]; split_ifs <;> omega
                  have hinvR : (if shiftWire (10 + i) all[j + 1].right ≥ 10 + i then shiftWire (10 + i) all[j + 1].right + 1 else shiftWire (10 + i) all[j + 1].right) = all[j + 1].right := by
                    dsimp only [shiftWire]; split_ifs <;> omega
                  rw [hinvL] at hihL; rw [hinvR] at hihR; rw [hihL, hihR]
        unfold BinaryCircuit.eval
        have hres := hwire (10 + (all.length - 2)) (by omega)
        rw [if_pos (by omega : 10 + (all.length - 2) ≥ 10 + i), show 10 + (all.length - 2) + 1 = 10 + (all.length - 1) by omega] at hres
        exact hres
    have eval_indep_of_unread : ∀ (all : List BinaryGate) (u : Fin 9),
        (∀ (j : ℕ) (hj : j < all.length), validG (10 + j) all[j]) →
        (∀ t ∈ all, t.left ≠ u.val ∧ t.right ≠ u.val) →
        ∀ (x y : Fin 9 → Bool), (∀ w : Fin 9, w ≠ u → x w = y w) →
        ∀ w < 10 + all.length, w ≠ u.val →
          (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).getD w false =
          (BinaryCircuit.wires ⟨all, 0⟩ (seed9 y)).getD w false := by
      intro all u hvalid hunread x y hxy w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hwu
        by_cases hlt9 : w < 9
        · unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed9 x) w (by simp [seed9]; omega),
              bcWires_prefix all (seed9 y) w (by simp [seed9]; omega),
              seed9_getD x w hlt9, seed9_getD y w hlt9]
          exact hxy ⟨w, hlt9⟩ (fun h => hwu (congrArg Fin.val h))
        · by_cases h9 : w = 9
          · subst h9; unfold BinaryCircuit.wires
            rw [bcWires_prefix all (seed9 x) 9 (by simp [seed9]),
                bcWires_prefix all (seed9 y) 9 (by simp [seed9]),
                seed9_getD_nine, seed9_getD_nine]
          · let j := w - 10
            have hj : j < all.length := by omega
            have hwj : w = 10 + j := by omega
            obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
            obtain ⟨hlu, hru⟩ := hunread all[j] (List.getElem_mem hj)
            rw [hwj, bcWires_gate all j hj x hl hr, bcWires_gate all j hj y hl hr]
            rw [ih all[j].left (by omega) (by omega) hlu, ih all[j].right (by omega) (by omega) hru]
    have eval_bottleneck : ∀ (all : List BinaryGate) (k : ℕ) (hk : k < all.length) (u v : Fin 9),
        (∀ (j : ℕ) (hj : j < all.length), validG (10 + j) all[j]) →
        (∀ (j : ℕ) (hj : j < all.length), j ≠ k →
          all[j].left ≠ u.val ∧ all[j].right ≠ u.val ∧ all[j].left ≠ v.val ∧ all[j].right ≠ v.val) →
        ∀ (x y : Fin 9 → Bool), (∀ w : Fin 9, w ≠ u → w ≠ v → x w = y w) →
        (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).getD (10 + k) false =
          (BinaryCircuit.wires ⟨all, 0⟩ (seed9 y)).getD (10 + k) false →
        ∀ w < 10 + all.length, w ≠ u.val → w ≠ v.val →
          (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x)).getD w false =
          (BinaryCircuit.wires ⟨all, 0⟩ (seed9 y)).getD w false := by
      intro all k hk u v hvalid hsole x y hxy hk_eq w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hwu hwv
        by_cases hlt9 : w < 9
        · unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed9 x) w (by simp [seed9]; omega),
              bcWires_prefix all (seed9 y) w (by simp [seed9]; omega),
              seed9_getD x w hlt9, seed9_getD y w hlt9]
          exact hxy ⟨w, hlt9⟩ (fun h => hwu (congrArg Fin.val h)) (fun h => hwv (congrArg Fin.val h))
        · by_cases h9 : w = 9
          · subst h9; unfold BinaryCircuit.wires
            rw [bcWires_prefix all (seed9 x) 9 (by simp [seed9]),
                bcWires_prefix all (seed9 y) 9 (by simp [seed9]),
                seed9_getD_nine, seed9_getD_nine]
          · let j := w - 10
            have hj : j < all.length := by omega
            have hwj : w = 10 + j := by omega
            by_cases hjk : j = k
            · rw [hwj, hjk]; exact hk_eq
            · obtain ⟨_, hl, hr, _, _, _⟩ := hvalid j hj
              obtain ⟨hlu, hru, hlv, hrv⟩ := hsole j hj hjk
              rw [hwj, bcWires_gate all j hj x hl hr, bcWires_gate all j hj y hl hr]
              rw [ih all[j].left (by omega) (by omega) hlu hlv, ih all[j].right (by omega) (by omega) hru hrv]
    let Good : ℕ → Prop := fun k =>
      1 ≤ k ∧ ∃ (all : List BinaryGate) (q : Bool),
        all.length = k ∧
        (∀ (j : ℕ) (hj : j < all.length), validG (10 + j) all[j]) ∧
        ∀ x : Fin 9 → Bool, (BinaryCircuit.eval ⟨all, 10 + (k - 1)⟩ (seed9 x) != q) = f9 x
    classical
    have hex : ∃ k, Good k := by
      obtain ⟨k, _, all, q, hall, hk1, hv, hev⟩ := hexValid
      exact ⟨k, hk1, all, q, hall, hv, hev⟩
    have hle14 : Nat.find hex ≤ 14 := by
      obtain ⟨k, hk14, all, q, hall, hk1, hv, hev⟩ := hexValid
      exact le_trans (Nat.find_min' hex ⟨hk1, all, q, hall, hv, hev⟩) hk14
    obtain ⟨hk1, all, q, hall, hvalid, heval⟩ := Nat.find_spec hex
    have hmin : ∀ k < all.length, ¬ Good k := fun k hk => Nat.find_min hex (hall ▸ hk)
    have hall_ne : all ≠ [] := by intro h; rw [h] at hall; simp at hall; omega
    let gs := all.dropLast
    let g := all.getLast hall_ne
    have hsplit : all = gs ++ [g] := (List.dropLast_append_getLast hall_ne).symm
    have hgs_len : gs.length = all.length - 1 := List.length_dropLast
    have hgs_le13 : gs.length ≤ 13 := by omega
    have hgs_valid : ∀ (j : ℕ) (hj : j < gs.length), validG (10 + j) gs[j] := by
      intro j hj
      have hltj : j < all.length := by omega
      have hget : gs[j] = all[j] := by
        conv_rhs => simp only [hsplit]
        exact (List.getElem_append_left hj).symm
      rw [hget]; exact hvalid j hltj
    have hg_eq : all[gs.length]'(by omega) = g := by
      conv_lhs => simp only [hsplit]
      rw [List.getElem_append_right le_rfl]; simp
    have hg_valid : validG (10 + gs.length) g := by
      rw [← hg_eq]; exact hvalid gs.length (by omega)
    have heval' : ∀ x : Fin 9 → Bool,
        (BinaryCircuit.eval ⟨gs ++ [g], 10 + gs.length⟩ (seed9 x) != q) = f9 x := by
      intro x; have := heval x; rw [hsplit] at this
      rwa [show Nat.find hex - 1 = gs.length by omega] at this
    have hg_inputs : 10 ≤ g.left ∧ 10 ≤ g.right := by
      obtain ⟨⟨a, b, hop⟩, hl, hr, hl10, hr10, _⟩ := hg_valid
      constructor
      · by_contra hltL
        have hlt9 : g.left < 9 := by omega
        obtain ⟨s1, s2, hs1, hs2, hne⟩ := f9_nonconst_fix ⟨g.left, hlt9⟩ (!a)
        have hev : ∀ s : List (Fin 9), maskVec s ⟨g.left, hlt9⟩ = !a → f9 (maskVec s) = (false != q) := by
          intro s hs; rw [← heval' (maskVec s)]
          change ((BinaryCircuit.wires ⟨gs ++ [g], 0⟩ (seed9 (maskVec s))).getD (10 + gs.length) false != q) = (false != q)
          rw [← hsplit, bcWires_gate all gs.length (by omega) (maskVec s) (by rw [hg_eq]; exact hl) (by rw [hg_eq]; exact hr), hg_eq, hop]
          unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed9 (maskVec s)) g.left (by simp [seed9]; omega), seed9_getD (maskVec s) g.left hlt9, hs]
          cases a <;> rfl
        exact hne ((hev s1 hs1).trans (hev s2 hs2).symm)
      · by_contra hltR
        have hlt9 : g.right < 9 := by omega
        obtain ⟨s1, s2, hs1, hs2, hne⟩ := f9_nonconst_fix ⟨g.right, hlt9⟩ (!b)
        have hev : ∀ s : List (Fin 9), maskVec s ⟨g.right, hlt9⟩ = !b → f9 (maskVec s) = (false != q) := by
          intro s hs; rw [← heval' (maskVec s)]
          change ((BinaryCircuit.wires ⟨gs ++ [g], 0⟩ (seed9 (maskVec s))).getD (10 + gs.length) false != q) = (false != q)
          rw [← hsplit, bcWires_gate all gs.length (by omega) (maskVec s) (by rw [hg_eq]; exact hl) (by rw [hg_eq]; exact hr), hg_eq, hop]
          unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed9 (maskVec s)) g.right (by simp [seed9]; omega), seed9_getD (maskVec s) g.right hlt9, hs]
          cases b <;> simp
        exact hne ((hev s1 hs1).trans (hev s2 hs2).symm)
    have hused : ∀ i < gs.length, ∃ t ∈ (gs ++ [g]).drop (i + 1), t.left = 10 + i ∨ t.right = 10 + i := by
      intro i hi; by_contra hun; push Not at hun
      rw [← hsplit] at hun
      obtain ⟨hlen', hval', hev'⟩ := delete_unused all i (by omega) hvalid hun
      apply hmin (all.length - 1) (by omega)
      refine ⟨by omega, _, q, hlen', hval', fun x => ?_⟩
      rw [show all.length - 1 - 1 = all.length - 2 by omega, hev' x, show all.length - 1 = Nat.find hex - 1 by omega]
      exact heval x
    let p := all.flatMap fun t => [t.left, t.right]
    have hp_len : p.length = 2 * gs.length + 2 := by
      have h1 : ∀ l : List BinaryGate, (l.flatMap fun t => [t.left, t.right]).length = 2 * l.length := by
        intro l; induction l with
        | nil => simp
        | cons t r ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
      have := h1 all; dsimp only [p]; omega
    have hp_in_pos : ∀ i < 9, 1 ≤ p.count i := by
      intro i hi; by_contra h0
      have hcount0 : p.count i = 0 := by omega
      have hnotmem : i ∉ p := List.count_eq_zero.mp hcount0
      have hunread : ∀ t ∈ all, t.left ≠ i ∧ t.right ≠ i := by
        intro t ht; constructor
        · intro h; apply hnotmem; rw [List.mem_flatMap]; exact ⟨t, ht, by simp [h]⟩
        · intro h; apply hnotmem; rw [List.mem_flatMap]; exact ⟨t, ht, by simp [h]⟩
      obtain ⟨s, hs⟩ := f9_dep ⟨i, hi⟩
      have hsame := eval_indep_of_unread all ⟨i, hi⟩ hvalid hunread (maskVec s)
        (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩))
        (fun w hw => by simp [Function.update, hw]) (10 + gs.length) (by omega) (by omega)
      have e1 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed9 (maskVec s))).getD (10 + gs.length) false != q) = f9 (maskVec s) := by
        have := heval' (maskVec s); rw [← hsplit] at this; exact this
      have e2 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed9 (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩)))).getD (10 + gs.length) false != q) =
          f9 (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩)) := by
        have := heval' (Function.update (maskVec s) ⟨i, hi⟩ (!maskVec s ⟨i, hi⟩)); rw [← hsplit] at this; exact this
      rw [hsame] at e1; exact hs (e1.symm.trans e2)
    have hp_gate_pos : ∀ i < gs.length, 1 ≤ p.count (10 + i) := by
      intro i hi; obtain ⟨t, ht, hread⟩ := hused i hi
      have hmem : t ∈ all := by rw [hsplit]; exact List.mem_of_mem_drop ht
      have hmemP : 10 + i ∈ p := by rw [List.mem_flatMap]; exact ⟨t, hmem, by rcases hread with h | h <;> simp [h]⟩
      exact List.count_pos_iff.mpr hmemP
    have hsum_count : ∀ (S : Finset ℕ), ∑ w ∈ S, p.count w ≤ p.length := by
      intro S
      have h1 : ∀ l : List ℕ, ∑ w ∈ S, l.count w ≤ l.length := by
        intro l; induction l with
        | nil => simp
        | cons a r ih =>
          simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
          have hstep : ∑ w ∈ S, (if a == w then 1 else 0) ≤ 1 := by
            by_cases ha : a ∈ S
            · rw [Finset.sum_eq_single a]
              · simp
              · intro b _ hba; simp [beq_false_of_ne hba.symm]
              · intro h; exact False.elim (h ha)
            · rw [Finset.sum_eq_zero]; · omega
              · intro b hb; have hne : a ≠ b := fun h => ha (h ▸ hb); simp [beq_false_of_ne hne]
          omega
      exact h1 p
    let R1 := (Finset.range 9).filter fun i => p.count i = 1
    let R2 := (Finset.range 9).filter fun i => p.count i ≠ 1
    let Gset := (Finset.range gs.length).image fun i => 10 + i
    have hR12_card : R1.card + R2.card = 9 := by
      have hu : R1 ∪ R2 = Finset.range 9 := by
        ext w; simp only [R1, R2, Finset.mem_union, Finset.mem_filter]; by_cases hc : p.count w = 1 <;> simp [hc]
      have hd : Disjoint R1 R2 := by
        rw [Finset.disjoint_left]; intro w h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]
    have hDisj_9_G : Disjoint (Finset.range 9) Gset := by
      rw [Finset.disjoint_left]; intro w hw1 hw2
      have := Finset.mem_range.mp hw1; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw2; omega
    have hCountBound : 16 ≤ gs.length + R1.card := by
      have hsumAll := hsum_count (Finset.range 9 ∪ Gset)
      rw [Finset.sum_union hDisj_9_G] at hsumAll
      have hsumG : gs.length ≤ ∑ w ∈ Gset, p.count w := by
        rw [Finset.sum_image (fun _ _ _ _ h => by omega)]
        calc gs.length = ∑ _i ∈ Finset.range gs.length, 1 := by simp
          _ ≤ ∑ i ∈ Finset.range gs.length, p.count (10 + i) := Finset.sum_le_sum fun i hi => hp_gate_pos i (Finset.mem_range.mp hi)
      have hpart9 : ∑ w ∈ Finset.range 9, p.count w = ∑ w ∈ R1, p.count w + ∑ w ∈ R2, p.count w := by
        have hu : R1 ∪ R2 = Finset.range 9 := by
          ext w; simp only [R1, R2, Finset.mem_union, Finset.mem_filter]; by_cases hc : p.count w = 1 <;> simp [hc]
        have hd : Disjoint R1 R2 := by
          rw [Finset.disjoint_left]; intro w h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        rw [← hu, Finset.sum_union hd]
      have hsumR1 : ∑ w ∈ R1, p.count w = R1.card := by
        calc ∑ w ∈ R1, p.count w = ∑ _w ∈ R1, 1 := Finset.sum_congr rfl fun w hw => (Finset.mem_filter.mp hw).2
          _ = R1.card := by simp
      have hsumR2 : 2 * R2.card ≤ ∑ w ∈ R2, p.count w := by
        calc 2 * R2.card = ∑ _w ∈ R2, 2 := by simp [mul_comm]
          _ ≤ ∑ w ∈ R2, p.count w := Finset.sum_le_sum fun w hw => by
              have hw9 := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
              have hne1 := (Finset.mem_filter.mp hw).2
              have hpos := hp_in_pos w hw9; omega
      omega
    have hNoPairR1 : ∀ h ∈ all, h.left < 9 → h.right < 9 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1 := by
      intro h hmem hltL hltR
      by_contra hboth; push Not at hboth
      obtain ⟨hcL, hcR⟩ := hboth
      obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
      have hneLR_n : h.left ≠ h.right := by
        have := (hvalid k hk).2.2.2.2.2; rwa [hget] at this
      let u : Fin 9 := ⟨h.left, hltL⟩
      let v : Fin 9 := ⟨h.right, hltR⟩
      have hneLR : u ≠ v := fun heq => hneLR_n (congrArg Fin.val heq)
      have hsole : ∀ (j : ℕ) (hj : j < all.length), j ≠ k →
          all[j].left ≠ u.val ∧ all[j].right ≠ u.val ∧ all[j].left ≠ v.val ∧ all[j].right ≠ v.val := by
        have hcount_ge2 : ∀ (z a b : ℕ) (ha : a < all.length) (hb : b < all.length), a ≠ b →
            (all[a].left = z ∨ all[a].right = z) → (all[b].left = z ∨ all[b].right = z) → 2 ≤ p.count z := by
          intro z
          suffices hrec : ∀ (l : List BinaryGate) (a b : ℕ) (ha : a < l.length) (hb : b < l.length), a ≠ b →
              (l[a].left = z ∨ l[a].right = z) → (l[b].left = z ∨ l[b].right = z) →
              2 ≤ (l.flatMap fun t => [t.left, t.right]).count z from hrec all
          intro l; induction l with
          | nil => intro a b ha; simp at ha
          | cons t r ih =>
            intro a b ha hb hab hza hzb
            simp only [List.flatMap_cons, List.count_append]
            have h1 : ∀ u : BinaryGate, (u.left = z ∨ u.right = z) → 1 ≤ [u.left, u.right].count z := by
              intro u hu; simp only [List.count_cons, List.count_nil, beq_iff_eq]; rcases hu with rfl | rfl <;> split_ifs <;> omega
            cases a with
            | zero =>
              cases b with
              | zero => exact False.elim (hab rfl)
              | succ b' =>
                have hza' := h1 t hza
                have hzb' : 0 < (r.flatMap fun t => [t.left, t.right]).count z := by
                  rw [List.count_pos_iff, List.mem_flatMap]
                  refine ⟨r[b']'(by simp at hb; omega), List.getElem_mem _, ?_⟩
                  simp only [List.getElem_cons_succ] at hzb; rcases hzb with h | h <;> simp [h]
                omega
            | succ a' =>
              cases b with
              | zero =>
                have hzb' := h1 t hzb
                have hza' : 0 < (r.flatMap fun t => [t.left, t.right]).count z := by
                  rw [List.count_pos_iff, List.mem_flatMap]
                  refine ⟨r[a']'(by simp at ha; omega), List.getElem_mem _, ?_⟩
                  simp only [List.getElem_cons_succ] at hza; rcases hza with h | h <;> simp [h]
                omega
              | succ b' =>
                have := ih a' b' (by simp at ha; omega) (by simp at hb; omega) (by omega) hza hzb; omega
        intro j hj hjk
        have hL1' : p.count u.val = 1 := hcL
        have hR1' : p.count v.val = 1 := hcR
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro heq; have := hcount_ge2 u.val k j hk hj hjk.symm (Or.inl (by rw [hget])) (Or.inl heq); omega
        · intro heq; have := hcount_ge2 u.val k j hk hj hjk.symm (Or.inl (by rw [hget])) (Or.inr heq); omega
        · intro heq; have := hcount_ge2 v.val k j hk hj hjk.symm (Or.inr (by rw [hget])) (Or.inl heq); omega
        · intro heq; have := hcount_ge2 v.val k j hk hj hjk.symm (Or.inr (by rw [hget])) (Or.inr heq); omega
      obtain ⟨s1, s2, hcard3⟩ := f9_pair_three u v hneLR
      let F : Bool → Bool → Bool × Bool := fun bu bv =>
        (f9 (upd2 (maskVec s1) u v bu bv), f9 (upd2 (maskVec s2) u v bu bv))
      obtain ⟨p1, p2, hopEq, hFne⟩ := pigeonhole_bool h.op F hcard3
      have hagree : ∀ s : List (Fin 9), f9 (upd2 (maskVec s) u v p1.1 p1.2) = f9 (upd2 (maskVec s) u v p2.1 p2.2) := by
        intro s
        let x1 := upd2 (maskVec s) u v p1.1 p1.2
        let x2 := upd2 (maskVec s) u v p2.1 p2.2
        have hxy : ∀ w : Fin 9, w ≠ u → w ≠ v → x1 w = x2 w := by
          intro w hwu hwv; simp [x1, x2, upd2, Function.update, hwu, hwv]
        have hk_eq : (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x1)).getD (10 + k) false =
            (BinaryCircuit.wires ⟨all, 0⟩ (seed9 x2)).getD (10 + k) false := by
          obtain ⟨_, hl, hr, _, _, _⟩ := hvalid k hk
          rw [bcWires_gate all k hk x1 hl hr, bcWires_gate all k hk x2 hl hr, hget]
          unfold BinaryCircuit.wires
          rw [bcWires_prefix all (seed9 x1) h.left (by simp [seed9]; omega),
              bcWires_prefix all (seed9 x1) h.right (by simp [seed9]; omega),
              bcWires_prefix all (seed9 x2) h.left (by simp [seed9]; omega),
              bcWires_prefix all (seed9 x2) h.right (by simp [seed9]; omega),
              seed9_getD x1 h.left hltL, seed9_getD x1 h.right hltR,
              seed9_getD x2 h.left hltL, seed9_getD x2 h.right hltR]
          have hu1 : x1 u = p1.1 := by dsimp only [x1, upd2]; rw [Function.update_of_ne hneLR, Function.update_self]
          have hv1 : x1 v = p1.2 := by dsimp only [x1, upd2]; rw [Function.update_self]
          have hu2 : x2 u = p2.1 := by dsimp only [x2, upd2]; rw [Function.update_of_ne hneLR, Function.update_self]
          have hv2 : x2 v = p2.2 := by dsimp only [x2, upd2]; rw [Function.update_self]
          change h.op (x1 u) (x1 v) = h.op (x2 u) (x2 v)
          rw [hu1, hv1, hu2, hv2]; exact hopEq
        have hsame := eval_bottleneck all k hk u v hvalid hsole x1 x2 hxy hk_eq (10 + gs.length) (by omega) (by omega) (by omega)
        have e1 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed9 x1)).getD (10 + gs.length) false != q) = f9 x1 := by
          have := heval' x1; rw [← hsplit] at this; exact this
        have e2 : ((BinaryCircuit.wires ⟨all, 0⟩ (seed9 x2)).getD (10 + gs.length) false != q) = f9 x2 := by
          have := heval' x2; rw [← hsplit] at this; exact this
        rw [hsame] at e1; exact e1.symm.trans e2
      exact hFne (Prod.ext (hagree s1) (hagree s2))
    have hR1_le_gs : R1.card ≤ gs.length := by
      have hmap : ∀ i ∈ R1, ∃ j, ∃ hj : j < gs.length, gs[j].left = i ∨ gs[j].right = i := by
        intro i hi
        have hc1 : p.count i = 1 := (Finset.mem_filter.mp hi).2
        have hmem : i ∈ p := List.count_pos_iff.mp (by omega)
        rw [List.mem_flatMap] at hmem
        obtain ⟨t, ht, hti⟩ := hmem
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
        have hjlt : j < gs.length := by
          by_contra hge
          have hjeq : j = gs.length := by omega
          subst hjeq; rw [hg_eq] at hti
          have hi10 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
          rcases hti with rfl | rfl <;> omega
        have hget : gs[j] = all[j] := by
          conv_rhs => simp only [hsplit]
          exact (List.getElem_append_left hjlt).symm
        refine ⟨j, hjlt, ?_⟩; rw [hget]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
        exact hti.imp Eq.symm Eq.symm
      let f : ℕ → ℕ := fun i => if h : i ∈ R1 then (hmap i h).choose else 0
      have hsub : R1.image f ⊆ Finset.range gs.length := by
        intro j hj; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        dsimp only [f]; rw [dif_pos hi]; exact Finset.mem_range.mpr (hmap i hi).choose_spec.1
      have hinj : Set.InjOn f (R1 : Set ℕ) := by
        intro i1 hi1' i2 hi2' heq
        have hi1 : i1 ∈ R1 := Finset.mem_coe.mp hi1'
        have hi2 : i2 ∈ R1 := Finset.mem_coe.mp hi2'
        dsimp only [f] at heq; rw [dif_pos hi1, dif_pos hi2] at heq
        set j := (hmap i1 hi1).choose
        have hj : j < gs.length := (hmap i1 hi1).choose_spec.1
        have h1 : gs[j].left = i1 ∨ gs[j].right = i1 := (hmap i1 hi1).choose_spec.2
        have h2 : gs[j].left = i2 ∨ gs[j].right = i2 := by
          have h2' := (hmap i2 hi2).choose_spec.2; simpa only [← heq] using h2'
        by_contra hne
        have hmem : gs[j] ∈ all := by rw [hsplit]; exact List.mem_append_left _ (List.getElem_mem hj)
        have hi1lt := Finset.mem_range.mp (Finset.mem_filter.mp hi1).1
        have hi2lt := Finset.mem_range.mp (Finset.mem_filter.mp hi2).1
        have hc1 := (Finset.mem_filter.mp hi1).2
        have hc2 := (Finset.mem_filter.mp hi2).2
        rcases h1 with hL1 | hR1 <;> rcases h2 with hL2 | hR2
        · exact hne (hL1.symm.trans hL2)
        · rcases hNoPairR1 gs[j] hmem (by omega) (by omega) with h | h
          · rw [hL1] at h; exact h hc1
          · rw [hR2] at h; exact h hc2
        · rcases hNoPairR1 gs[j] hmem (by omega) (by omega) with h | h
          · rw [hL2] at h; exact h hc2
          · rw [hR1] at h; exact h hc1
        · exact hne (hR1.symm.trans hR2)
      calc R1.card = (R1.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range gs.length).card := Finset.card_le_card hsub
        _ = gs.length := Finset.card_range _
    have hgs_ge8 : 8 ≤ gs.length := by omega
    have hCountBound' : 16 ≤ gs.length + ((Finset.range 9).filter fun i => ((gs ++ [g]).flatMap fun t => [t.left, t.right]).count i = 1).card := by
      have hR1eq : R1 = (Finset.range 9).filter fun i => ((gs ++ [g]).flatMap fun t => [t.left, t.right]).count i = 1 := by
        ext w; simp only [R1, p, Finset.mem_filter, hsplit]
      rw [← hR1eq]; exact hCountBound
    have hNoPairR1' : ∀ h ∈ gs ++ [g], h.left < 9 → h.right < 9 →
        ((gs ++ [g]).flatMap fun t => [t.left, t.right]).count h.left ≠ 1 ∨
        ((gs ++ [g]).flatMap fun t => [t.left, t.right]).count h.right ≠ 1 := by
      intro h hh hl hr
      have h1 := hNoPairR1 h (hsplit.symm ▸ hh) hl hr
      dsimp only [p] at h1; rw [hsplit] at h1; exact h1
    by_cases hle10 : gs.length ≤ 10
    · exact binaryLow gs g q hgs_ge8 hle10 hgs_valid hg_valid hg_inputs.1 hg_inputs.2 hused hCountBound' hNoPairR1' heval'
    · exact binaryMid gs g q (by omega) hgs_le13 hgs_valid hg_valid hg_inputs.1 hg_inputs.2 hused hCountBound' hNoPairR1' heval'
