import PEqualNP.Defs

def Bridge8247.SameOff (a b : List Bool) (k : Nat) :=
  a.length = b.length ∧ ∀ j, j ≠ k → a[j]? = b[j]?

theorem Bridge8247.sameOff_append {a b : List Bool} {k : Nat} (h : Bridge8247.SameOff a b k) (v : Bool) :
    Bridge8247.SameOff (a ++ [v]) (b ++ [v]) k := by
  refine ⟨by simp [h.1], ?_⟩
  intro j hj
  by_cases hlt : j < a.length
  · have hlt' : j < b.length := h.1 ▸ hlt
    rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt', h.2 j hj]
  · have hge : a.length ≤ j := Nat.le_of_not_gt hlt
    have hge' : b.length ≤ j := h.1 ▸ hge
    rw [List.getElem?_append_right hge, List.getElem?_append_right hge', h.1]

def Bridge8247.gate (xs : List Nat) (op : List Bool → Bool) (w : List Bool) :=
  op (xs.map fun i => w.getD i false)

theorem Bridge8247.gate_sameOff {a b : List Bool} {k : Nat} {xs : List Nat} {op : List Bool → Bool}
    (h : Bridge8247.SameOff a b k) (hk : k ∉ xs) : Bridge8247.gate xs op a = Bridge8247.gate xs op b := by
  unfold Bridge8247.gate
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h.2 j]
  exact fun he => hk (he ▸ hj)

theorem Bridge8247.getD_append_old {a : List Bool} (v : Bool) {j : Nat} (h : j < a.length) :
    (a ++ [v]).getD j false = a.getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

def Bridge8247.step (w : List Bool) (g : List Nat × (List Bool → Bool)) : List Bool :=
  w ++ [Bridge8247.gate g.1 g.2 w]

theorem Bridge8247.fold_masked {gs : List (List Nat × (List Bool → Bool))}
    {a b : List Bool} {k j : Nat} (hs : Bridge8247.SameOff a b k)
    (haj : j < a.length) (hbj : j < b.length)
    (ha0 : a.getD j false = false) (hb0 : b.getD j false = false)
    (hg : ∀ g ∈ gs, k ∉ g.1 ∨
      (g.1 = [k, j] ∨ g.1 = [j, k]) ∧ ∀ ys, g.2 ys = ys.all id) :
    Bridge8247.SameOff (gs.foldl Bridge8247.step a) (gs.foldl Bridge8247.step b) k := by
  induction gs generalizing a b with
  | nil => exact hs
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hval : Bridge8247.gate g.1 g.2 a = Bridge8247.gate g.1 g.2 b := by
      rcases hg g (by simp) with hn | ⟨hx, hop⟩
      · exact Bridge8247.gate_sameOff hs hn
      · rw [List.getD_eq_getElem?_getD] at ha0 hb0
        rcases hx with hx | hx <;> simp [Bridge8247.gate, hx, hop, ha0, hb0]
    have hs' : Bridge8247.SameOff (Bridge8247.step a g) (Bridge8247.step b g) k := by
      unfold Bridge8247.step
      rw [hval]
      exact Bridge8247.sameOff_append hs _
    refine ih hs' (by simp [Bridge8247.step]; omega) (by simp [Bridge8247.step]; omega) ?_ ?_ ?_
    · unfold Bridge8247.step
      rw [Bridge8247.getD_append_old _ haj]
      exact ha0
    · unfold Bridge8247.step
      rw [Bridge8247.getD_append_old _ hbj]
      exact hb0
    · intro x hx
      exact hg x (by simp [hx])


def Bridge8247.pete9 (w : List Bool) : Bool :=
  let x := fun i => w.getD i false
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

theorem Bridge8247.pete9_distinct_bare_aux {gs : List (List Nat × (List Bool → Bool))}
    {output j : Nat} (hj : j < 9) (hjne : j ≠ 4)
    (hg : ∀ g ∈ gs, 4 ∉ g.1 ∨
      (g.1 = [4, j] ∨ g.1 = [j, 4]) ∧ ∀ ys, g.2 ys = ys.all id) :
    ¬ (∀ xs : List Bool, xs.length = 9 →
        (gs.foldl Bridge8247.step xs).getD output false = Bridge8247.pete9 xs) := by
  intro hf
  have different (a b : List Bool)
      (ha : a.length = 9) (hb : b.length = 9) (hab : Bridge8247.SameOff a b 4)
      (ha0 : a.getD j false = false) (hb0 : b.getD j false = false)
      (hn : Bridge8247.pete9 a ≠ Bridge8247.pete9 b) (hr : output ≠ 4) : False := by
    have hy := (Bridge8247.fold_masked hab (ha ▸ hj) (hb ▸ hj) ha0 hb0 hg).2 output hr
    have he : (gs.foldl Bridge8247.step a).getD output false = (gs.foldl Bridge8247.step b).getD output false := by
      simp only [List.getD_eq_getElem?_getD, hy]
    exact hn ((hf a ha).symm.trans (he.trans (hf b hb)))
  by_cases hr : output = 4
  · subst output
    let w : List Bool := [false,false,false,false,true,false,false,false,false]
    have inputGet (gs' : List (List Nat × (List Bool → Bool))) (p : List Bool)
        (hp : 4 < p.length) :
        (gs'.foldl Bridge8247.step p).getD 4 false = p.getD 4 false := by
      induction gs' generalizing p with
      | nil => rfl
      | cons g rest ih =>
        rw [List.foldl_cons, ih (Bridge8247.step p g) (by simp [Bridge8247.step] <;> omega)]
        exact Bridge8247.getD_append_old _ hp
    have hbad := hf w rfl
    rw [inputGet gs w (by decide)] at hbad
    exact Bool.noConfusion hbad
  · by_cases jzero : j = 0
    · subst j
      let a : List Bool := [false,false,false,true,false,false,false,false,false]
      let b : List Bool := [false,false,false,true,true,false,false,false,false]
      refine different a b rfl rfl ⟨rfl, ?_⟩ (by decide) (by decide) (by decide) hr
      intro i hi
      by_cases big : 9 ≤ i
      · rw [List.getElem?_eq_none (show a.length ≤ i from big), List.getElem?_eq_none (show b.length ≤ i from big)]
      · have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
        rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · let a : List Bool := [true,false,false,false,false,false,false,false,false]
      let b : List Bool := [true,false,false,false,true,false,false,false,false]
      have j_cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
      have ha : a.getD j false = false := by
        rcases j_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hb : b.getD j false = false := by
        rcases j_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      refine different a b rfl rfl ⟨rfl, ?_⟩ ha hb (by decide) hr
      intro i hi
      by_cases big : 9 ≤ i
      · rw [List.getElem?_eq_none (show a.length ≤ i from big), List.getElem?_eq_none (show b.length ≤ i from big)]
      · have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
        rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide



theorem PEqualNP.Outside.BarePin8247 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i : Fin C.size) (j : ℕ), j < 9 → j ≠ 4 → (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ l : Fin C.size, 4 ∈ (C.gates.get l).inputs → l = i) → ((C.gates.get i).inputs = [4,j] ∨ (C.gates.get i).inputs = [j,4]) → PEqualNP.MetaComplexity.circuitFun 9 C ≠ (fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C i j hj hj4 hop hread hp hC
  let src := fun g : PEqualNP.CircuitLowerBounds.Gate => (g.inputs, g.op.eval)
  have hm : ∀ g ∈ C.gates.map src, 4 ∉ g.1 ∨
      (g.1 = [4,j] ∨ g.1 = [j,4]) ∧ ∀ ys, g.2 ys = ys.all id := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hz
    by_cases hg4 : 4 ∈ g.inputs
    · obtain ⟨l, hl⟩ := List.mem_iff_get.mp hg
      have he := hread l (hl ▸ hg4)
      have hig : C.gates.get i = g := he ▸ hl
      apply Or.inr
      refine ⟨?_, ?_⟩
      · simpa [src, hig] using hp
      · intro ys
        change g.op.eval ys = ys.all id
        have ha : g.op = PEqualNP.CircuitLowerBounds.GateOp.and := hig ▸ hop
        rw [ha]
        rfl
    · exact Or.inl hg4
  apply Bridge8247.pete9_distinct_bare_aux hj hj4 hm
  intro xs hlen
  let x : Fin 9 → Bool := fun k => xs.getD k.val false
  have hxs : List.ofFn x = xs := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro a h₁ h₂
      rw [List.getElem_ofFn]
      change xs.getD a false = xs[a]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
      rfl
  have hv := congrFun hC x
  change C.eval (List.ofFn x) = Bridge8247.pete9 xs at hv
  rw [hxs] at hv
  rw [List.foldl_map]
  exact hv
