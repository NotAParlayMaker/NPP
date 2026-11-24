import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- The 58 boundary rows and their evaluation certificate follow R_meta_2278_58 (PR #4990).
theorem PEqualNP.Outside.R_meta_2278_473
    (normalize : let W := BitVec 58
    let G := Bool × ℕ × ℕ
    let step := fun (w : List W) (g : G) => w++[if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]
    ∀ (B : List W) (C : Circuit), Monotone2 C → ∃ S : List G, S.length≤C.size ∧ (∀ g∈S,g.2.1<g.2.2) ∧
    ∃ t : W, (t=0 ∨ t=BitVec.allOnes 58 ∨ t∈S.foldl step B) ∧ ∀ k : Fin 58, t.getLsbD k=C.eval (B.map fun a => a.getLsbD k))
    (quota : let W := BitVec 58
    let G := Bool × ℕ × ℕ
    let step := fun (w : List W) (g : G) => w++[if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]
    let B : List W := List.ofFn (fun i : Fin 14 => BitVec.ofNat 58 ((27305519102644583149665226792277652155481711537918085168871095508135184176334603431239330874229324051701409612879344006668756009334260402552987786561760844676127080938240233073956043201016893889908026053332369881365537826095879983719911885111303 : ℕ) >>> (58*i.val)))
    ∀ S : List G, S.length≤25 → (∀ g∈S,g.2.1<g.2.2) →
    let F := (false,0,1)::S
    let T := F.foldl step B
    let pick : G × W → Option W := fun (p : G × W) => if p.1.1 then (none : Option W) else some p.2
    let O := List.filterMap pick (F.zip (T.drop 14))
    (2097151 : W) ∈ T → (11≤O.length ∧ O.length≤20 ∧
    (∀ r : Fin 37, B.countP (fun w => !w.getLsbD (r.val+21)) + O.countP (fun w => w.getLsbD (r.val+21)) ≤ O.length+1)))
    (obstruct : let W := BitVec 58
    let G := Bool × ℕ × ℕ
    let step := fun (w : List W) (g : G) => w++[if g.1 then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]
    let B : List W := List.ofFn (fun i : Fin 14 => BitVec.ofNat 58 ((27305519102644583149665226792277652155481711537918085168871095508135184176334603431239330874229324051701409612879344006668756009334260402552987786561760844676127080938240233073956043201016893889908026053332369881365537826095879983719911885111303 : ℕ) >>> (58*i.val)))
    ∀ S : List G, S.length≤25 → (∀ g∈S,g.2.1<g.2.2) →
    let F := (false,0,1)::S
    let T := F.foldl step B
    let pick : G × W → Option W := fun (p : G × W) => if p.1.1 then (none : Option W) else some p.2
    let O := List.filterMap pick (F.zip (T.drop 14))
    (11≤O.length ∧ O.length≤20 ∧
    (∀ r : Fin 37, B.countP (fun w => !w.getLsbD (r.val+21)) + O.countP (fun w => w.getLsbD (r.val+21)) ≤ O.length+1)) → (2097151 : W) ∉ T) :
have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x6)) → (26 : ℕ) ≤ x4.size := by
  let cols : List (BitVec 58) := [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
      8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
      155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
      270286071508633728, 288160007407550752]
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
      (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
      (6, 8), (6, 9), (6, 11)]
  let hit := fun x : Fin 14 → Bool =>
    ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
  let ext := fun x : Fin 14 → Bool =>
    (hit x ∧ ∀ i : Fin 14, x i = true → ¬ hit (Function.update x i false)) ∨
    (¬ hit x ∧ ∀ i : Fin 14, x i = false → hit (Function.update x i true))
  let row := fun (k : Fin 58) (i : Fin 14) => (cols.getD i 0).getLsbD k
  let test := fun x : Fin 14 → Bool => edges.any fun e =>
    x (Fin.ofNat 14 e.1) && x (Fin.ofNat 14 e.2)
  have bounds : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by
    unfold edges
    decide
  have reflect (x : Fin 14 → Bool) : hit x ↔ test x = true := by
    simp only [hit, test, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨(a.val,b.val), hab, by simpa using ha, by simpa using hb⟩
    · rintro ⟨⟨a,b⟩, hab, ha,hb⟩
      obtain ⟨hal,hbl⟩ := bounds (a,b) hab
      exact ⟨⟨a,hal⟩, ⟨b,hbl⟩, hab, by simpa [Fin.ofNat, Nat.mod_eq_of_lt hal] using ha,
        by simpa [Fin.ofNat, Nat.mod_eq_of_lt hbl] using hb⟩
  let target : BitVec 58 := 2097151
  let verify := fun (k : Fin 58) =>
    let x := row k
    let p := target.getLsbD k
    (test x == p) && (List.finRange 14).all fun i =>
      if x i = p then test (Function.update x i (!p)) == !p else true
  have allRows : (List.finRange 58).all verify = true := by
    dsimp only [verify, test, target, row, cols, edges]
    decide +kernel
  have cert : ∀ k : Fin 58, ext (row k) ∧ (hit (row k) ↔ (2097151 : BitVec 58).getLsbD k = true) := by
    intro k
    have hk := List.all_eq_true.mp allRows k (by simp)
    change (_ && _) = true at hk
    obtain ⟨hp, hflip⟩ := Bool.and_eq_true_iff.mp hk
    have heq : test (row k) = target.getLsbD k := beq_iff_eq.mp hp
    change _ ∧ (hit (row k) ↔ target.getLsbD k = true)
    refine ⟨?_, by rw [reflect, heq]⟩
    have flips (i : Fin 14) (hi : row k i = target.getLsbD k) :
        test (Function.update (row k) i (!(target.getLsbD k))) = !(target.getLsbD k) := by
      have h := List.all_eq_true.mp hflip i (by simp)
      change (if row k i = target.getLsbD k then _ else true) = true at h
      simpa [hi] using h
    cases hp : target.getLsbD k with
    | false =>
      right
      refine ⟨by rw [reflect, heq, hp]; decide, ?_⟩
      intro i hi
      have hf := flips i (hi.trans hp.symm)
      rw [hp] at hf
      exact (reflect _).2 hf
    | true =>
      left
      refine ⟨(reflect _).2 (heq.trans hp), ?_⟩
      intro i hi
      have hf := flips i (hi.trans hp.symm)
      rw [hp] at hf
      change test (Function.update (row k) i false) = false at hf
      rw [reflect, hf]
      decide
  let inputs := cols ++ [(cols.getD 0 0) ||| (cols.getD 1 0)]
  have inputRows (k : Fin 58) :
      inputs.map (fun v => v.getLsbD k) =
        List.ofFn (row k) ++ [GateOp.or.eval [row k 0, row k 1]] := by
    have h : cols.map (fun v => v.getLsbD k) = List.ofFn (row k) := by
      apply List.ext_getElem
      · simp [cols]
      · intro i hi hi'
        have hi14 : i < 14 := by simpa using hi'
        have hic : i < cols.length := by simpa using hi
        simp only [List.getElem_map, List.getElem_ofFn, row, List.getD_eq_getElem _ _ hic]
    simp only [inputs, List.map_append, List.map_cons, List.map_nil, h, BitVec.getLsbD_or]
    change _ ++ [row k 0 || row k 1] = _ ++ [row k 0 || (row k 1 || false)]
    simp only [Bool.or_false]
  change ∀ C : Circuit, Monotone2 C →
    (∀ x : Fin 14 → Bool, ext x → (C.eval (List.ofFn x ++ [GateOp.or.eval [x 0,x 1]])=true ↔ hit x)) → 26≤C.size
  intro C hm hc
  by_contra! small
  obtain ⟨S,size,sorted,t,ht,bits⟩ := normalize inputs C hm
  have et : t=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let r : Fin 58 := ⟨k,hk⟩
    change t.getLsbD r = target.getLsbD r
    rw [bits,inputRows]
    exact Bool.eq_iff_iff.2 ((hc _ (cert r).1).trans (cert r).2)
  subst t
  have live := ht.resolve_left (by decide)
  have existsTarget := live.resolve_left (by decide)
  have sz : S.length≤25 := by omega
  exact (obstruct S sz sorted (quota S sz sorted existsTarget)) existsTarget
