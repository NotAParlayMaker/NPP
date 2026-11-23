import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.Pasch1042
open CircuitLowerBounds
abbrev W := BitVec 6
def base : List W := [0,63,1,2,4,8,16,32]
def can (xs : List W) (g : W) : Bool :=
  xs.any fun a => (g == ~~~a) || xs.any fun b => (g == (a &&& b)) || (g == (a ||| b))
def hits (xs : List W) : Bool := [7,25,42,52].all fun t => xs.contains t
def raw : List W := [1,2,4,8,16,32]
def coord (j : Fin 6) (b : W) := b.getLsbD j.val
def inputs (j : Fin 6) : Fin 6 → Bool := fun i => decide (i = j)
theorem start (j : Fin 6) : raw.map (coord j) = List.ofFn (inputs j) := by
  fin_cases j <;> decide
def step (w : List W) (g : Gate) : W :=
  let x := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => x.foldr (.&&&.) 63
  | .or => x.foldr (.|||.) 0
  | .not => ~~~(x.headD 0)
  | _ => 0
def valid (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
theorem read_co (w : List W) (i : Nat) (j : Fin 6) :
  coord j (w.getD i 0) = (w.map (coord j)).getD i false := by
  simp only [List.getD,List.getElem?_map]
  cases w[i]? <;> simp [coord]
theorem step_co (w : List W) (g : Gate) (h : valid g) (j : Fin 6) :
  coord j (step w g) = g.op.eval (g.inputs.map fun i => (w.map (coord j)).getD i false) := by
  have ones : (63 : W).getLsbD j.val = true := by fin_cases j <;> decide
  simp only [← read_co]
  rcases g with ⟨o,x⟩
  rcases h with ⟨ho,hl⟩
  change x.length ≤ 2 at hl
  change o = .and ∨ o = .or ∨ o = .not at ho
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals try simp at hl
  all_goals try omega
  all_goals rcases ho with rfl|rfl|rfl <;>
    simp [step,GateOp.eval,← read_co,coord,BitVec.getLsbD_not,j.isLt,ones]
  all_goals fin_cases j <;> simp_all
theorem can_bin {xs : List W} {a b : W} (ha : a ∈ xs) (hb : b ∈ xs) :
    can xs (a &&& b) ∧ can xs (a ||| b) := by
  constructor <;> apply List.any_eq_true.mpr <;> refine ⟨a,ha,?_⟩ <;>
    apply Bool.or_eq_true_iff.mpr <;> right <;> apply List.any_eq_true.mpr <;>
    exact ⟨b,hb,by simp⟩
theorem can_not {xs : List W} {a : W} (ha : a ∈ xs) : can xs (~~~a) := by
  apply List.any_eq_true.mpr
  exact ⟨a,ha,by simp⟩
set_option maxHeartbeats 1000000
private theorem and63 (a : W) : a &&& 63 = a := by revert a; decide +kernel
private theorem or0 (a : W) : a ||| 0 = a := by revert a; decide +kernel
theorem step_can (ys : List W) (g : Gate) (h : valid g) :
    can (ys.reverse ++ base) (step (raw ++ ys) g) := by
  let xs := ys.reverse ++ base
  have mem0 : (0 : W) ∈ xs := by simp [xs, base]
  have mem1 : (63 : W) ∈ xs := by simp [xs, base]
  have read (i : Nat) : (raw ++ ys).getD i 0 ∈ xs := by
    simp only [List.getD]
    cases hv : (raw ++ ys)[i]? with
    | none => exact mem0
    | some v =>
      have hm := List.mem_of_getElem? hv
      rcases List.mem_append.mp hm with hr|hy
      · exact List.mem_append_right _ (show v ∈ 0 :: 63 :: raw by simp [hr])
      · exact List.mem_append_left _ (List.mem_reverse.mpr hy)
  rcases g with ⟨o,x⟩
  rcases h with ⟨ho,hl⟩
  change x.length ≤ 2 at hl
  change o = .and ∨ o = .or ∨ o = .not at ho
  have ident (a : W) (ha : a ∈ xs) : can xs a := by simpa using (can_bin ha ha).1
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals try simp at hl
  all_goals try omega
  all_goals rcases ho with rfl|rfl|rfl
  all_goals change can xs _
  all_goals simp only [step, List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    List.headD_nil,List.headD_cons,and63,
    or0,show (~~~(0 : W)) = 63 by decide]
  all_goals first | exact ident _ mem0 | exact ident _ mem1 | exact ident _ (read _)
                  | exact (can_bin (read _) (read _)).1 | exact (can_bin (read _) (read _)).2
                  | exact can_not (read _)
inductive History : List W → Prop
  | nil : History []
  | cons {x : W} {ys : List W} : History ys → can (ys ++ base) x → History (x :: ys)
def collect (ys : List W) : List Gate → List W
  | [] => ys
  | g :: gs => collect (ys ++ [step (raw ++ ys) g]) gs
theorem collect_spec (ys : List W) (gs : List Gate) (hg : ∀ g ∈ gs, valid g)
    (hy : History ys.reverse) : History (collect ys gs).reverse ∧
    (collect ys gs).length = ys.length + gs.length := by
  induction gs generalizing ys with
  | nil => simp [collect,hy]
  | cons g gs ih =>
    have hh := History.cons hy (step_can ys g (hg _ (by simp)))
    have hx := ih (ys ++ [step (raw ++ ys) g]) (fun a ha => hg a (by simp [ha])) (by simpa using hh)
    exact ⟨hx.1,by simpa [collect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2⟩
theorem collect_co (ys : List W) (gs : List Gate) (hg : ∀ g ∈ gs, valid g) (j : Fin 6) :
    (raw ++ collect ys gs).map (coord j) =
    gs.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
       ((raw ++ ys).map (coord j)) := by
  induction gs generalizing ys with
  | nil => rfl
  | cons g gs ih =>
    rw [collect,List.foldl_cons,ih _ (fun a ha => hg a (by simp [ha]))]
    simp [← List.append_assoc,List.map_append,step_co _ _ (hg g (by simp))]
def targets : List W := [7,25,42,52]

private def owner (a : W) : Option W :=
  if [3,5,6,56].contains a then some 7 else
  if [9,17,24,38].contains a then some 25 else
  if [10,21,34,40].contains a then some 42 else
  if [11,20,36,48].contains a then some 52 else none

private def pair (a b t : W) := (t == a &&& b) || (t == a ||| b)

private theorem can_iff (L : List W) (t : W) :
    can L t = true ↔ ∃ x ∈ L, t = ~~~x ∨ ∃ y ∈ L, pair x y t = true := by
  simp [can,pair,List.any_eq_true]

private theorem pair_comm (a b t : W) : pair a b t = pair b a t := by
  simp [_root_.PEqualNP.Outside.Pasch1042.pair,BitVec.and_comm a b,BitVec.or_comm a b]

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000


private def check1 (a : W) := targets.contains a || targets.all fun t =>
  !can (a::(targets.erase t ++ base)) t || owner a == some t

private def check2 (a b : W) := targets.contains a || targets.contains b || targets.all fun t =>
  !pair a b t || owner a == some t || owner b == some t ||
    (owner a == none && owner b == none && (a &&& b == t))

private theorem owner_cert : ∀ a : W, check1 a = true := by decide
private theorem pair_cert_0 : ∀ b : W, check2 0 b = true := by decide
private theorem pair_cert_1 : ∀ b : W, check2 1 b = true := by decide
private theorem pair_cert_2 : ∀ b : W, check2 2 b = true := by decide
private theorem pair_cert_3 : ∀ b : W, check2 3 b = true := by decide
private theorem pair_cert_4 : ∀ b : W, check2 4 b = true := by decide
private theorem pair_cert_5 : ∀ b : W, check2 5 b = true := by decide
private theorem pair_cert_6 : ∀ b : W, check2 6 b = true := by decide
private theorem pair_cert_7 : ∀ b : W, check2 7 b = true := by decide
private theorem pair_cert_8 : ∀ b : W, check2 8 b = true := by decide
private theorem pair_cert_9 : ∀ b : W, check2 9 b = true := by decide
private theorem pair_cert_10 : ∀ b : W, check2 10 b = true := by decide
private theorem pair_cert_11 : ∀ b : W, check2 11 b = true := by decide
private theorem pair_cert_12 : ∀ b : W, check2 12 b = true := by decide
private theorem pair_cert_13 : ∀ b : W, check2 13 b = true := by decide
private theorem pair_cert_14 : ∀ b : W, check2 14 b = true := by decide
private theorem pair_cert_15 : ∀ b : W, check2 15 b = true := by decide
private theorem pair_cert_16 : ∀ b : W, check2 16 b = true := by decide
private theorem pair_cert_17 : ∀ b : W, check2 17 b = true := by decide
private theorem pair_cert_18 : ∀ b : W, check2 18 b = true := by decide
private theorem pair_cert_19 : ∀ b : W, check2 19 b = true := by decide
private theorem pair_cert_20 : ∀ b : W, check2 20 b = true := by decide
private theorem pair_cert_21 : ∀ b : W, check2 21 b = true := by decide
private theorem pair_cert_22 : ∀ b : W, check2 22 b = true := by decide
private theorem pair_cert_23 : ∀ b : W, check2 23 b = true := by decide
private theorem pair_cert_24 : ∀ b : W, check2 24 b = true := by decide
private theorem pair_cert_25 : ∀ b : W, check2 25 b = true := by decide
private theorem pair_cert_26 : ∀ b : W, check2 26 b = true := by decide
private theorem pair_cert_27 : ∀ b : W, check2 27 b = true := by decide
private theorem pair_cert_28 : ∀ b : W, check2 28 b = true := by decide
private theorem pair_cert_29 : ∀ b : W, check2 29 b = true := by decide
private theorem pair_cert_30 : ∀ b : W, check2 30 b = true := by decide
private theorem pair_cert_31 : ∀ b : W, check2 31 b = true := by decide
private theorem pair_cert_32 : ∀ b : W, check2 32 b = true := by decide
private theorem pair_cert_33 : ∀ b : W, check2 33 b = true := by decide
private theorem pair_cert_34 : ∀ b : W, check2 34 b = true := by decide
private theorem pair_cert_35 : ∀ b : W, check2 35 b = true := by decide
private theorem pair_cert_36 : ∀ b : W, check2 36 b = true := by decide
private theorem pair_cert_37 : ∀ b : W, check2 37 b = true := by decide
private theorem pair_cert_38 : ∀ b : W, check2 38 b = true := by decide
private theorem pair_cert_39 : ∀ b : W, check2 39 b = true := by decide
private theorem pair_cert_40 : ∀ b : W, check2 40 b = true := by decide
private theorem pair_cert_41 : ∀ b : W, check2 41 b = true := by decide
private theorem pair_cert_42 : ∀ b : W, check2 42 b = true := by decide
private theorem pair_cert_43 : ∀ b : W, check2 43 b = true := by decide
private theorem pair_cert_44 : ∀ b : W, check2 44 b = true := by decide
private theorem pair_cert_45 : ∀ b : W, check2 45 b = true := by decide
private theorem pair_cert_46 : ∀ b : W, check2 46 b = true := by decide
private theorem pair_cert_47 : ∀ b : W, check2 47 b = true := by decide
private theorem pair_cert_48 : ∀ b : W, check2 48 b = true := by decide
private theorem pair_cert_49 : ∀ b : W, check2 49 b = true := by decide
private theorem pair_cert_50 : ∀ b : W, check2 50 b = true := by decide
private theorem pair_cert_51 : ∀ b : W, check2 51 b = true := by decide
private theorem pair_cert_52 : ∀ b : W, check2 52 b = true := by decide
private theorem pair_cert_53 : ∀ b : W, check2 53 b = true := by decide
private theorem pair_cert_54 : ∀ b : W, check2 54 b = true := by decide
private theorem pair_cert_55 : ∀ b : W, check2 55 b = true := by decide
private theorem pair_cert_56 : ∀ b : W, check2 56 b = true := by decide
private theorem pair_cert_57 : ∀ b : W, check2 57 b = true := by decide
private theorem pair_cert_58 : ∀ b : W, check2 58 b = true := by decide
private theorem pair_cert_59 : ∀ b : W, check2 59 b = true := by decide
private theorem pair_cert_60 : ∀ b : W, check2 60 b = true := by decide
private theorem pair_cert_61 : ∀ b : W, check2 61 b = true := by decide
private theorem pair_cert_62 : ∀ b : W, check2 62 b = true := by decide
private theorem pair_cert_63 : ∀ b : W, check2 63 b = true := by decide
private theorem pair_cert (a b : W) : check2 a b = true := by
  have h := a.isLt
  have w : a = BitVec.ofNat 6 a.toNat := by simp
  rw [w]; generalize a.toNat = n at *; change n < 64 at h
  interval_cases n
  · exact pair_cert_0 b
  · exact pair_cert_1 b
  · exact pair_cert_2 b
  · exact pair_cert_3 b
  · exact pair_cert_4 b
  · exact pair_cert_5 b
  · exact pair_cert_6 b
  · exact pair_cert_7 b
  · exact pair_cert_8 b
  · exact pair_cert_9 b
  · exact pair_cert_10 b
  · exact pair_cert_11 b
  · exact pair_cert_12 b
  · exact pair_cert_13 b
  · exact pair_cert_14 b
  · exact pair_cert_15 b
  · exact pair_cert_16 b
  · exact pair_cert_17 b
  · exact pair_cert_18 b
  · exact pair_cert_19 b
  · exact pair_cert_20 b
  · exact pair_cert_21 b
  · exact pair_cert_22 b
  · exact pair_cert_23 b
  · exact pair_cert_24 b
  · exact pair_cert_25 b
  · exact pair_cert_26 b
  · exact pair_cert_27 b
  · exact pair_cert_28 b
  · exact pair_cert_29 b
  · exact pair_cert_30 b
  · exact pair_cert_31 b
  · exact pair_cert_32 b
  · exact pair_cert_33 b
  · exact pair_cert_34 b
  · exact pair_cert_35 b
  · exact pair_cert_36 b
  · exact pair_cert_37 b
  · exact pair_cert_38 b
  · exact pair_cert_39 b
  · exact pair_cert_40 b
  · exact pair_cert_41 b
  · exact pair_cert_42 b
  · exact pair_cert_43 b
  · exact pair_cert_44 b
  · exact pair_cert_45 b
  · exact pair_cert_46 b
  · exact pair_cert_47 b
  · exact pair_cert_48 b
  · exact pair_cert_49 b
  · exact pair_cert_50 b
  · exact pair_cert_51 b
  · exact pair_cert_52 b
  · exact pair_cert_53 b
  · exact pair_cert_54 b
  · exact pair_cert_55 b
  · exact pair_cert_56 b
  · exact pair_cert_57 b
  · exact pair_cert_58 b
  · exact pair_cert_59 b
  · exact pair_cert_60 b
  · exact pair_cert_61 b
  · exact pair_cert_62 b
  · exact pair_cert_63 b

private theorem owner_ok {a t : W} (ha : a ∉ targets) (ht : t ∈ targets)
    (hc : can (a :: (targets.erase t ++ base)) t = true) : owner a = some t := by
  have h := owner_cert a
  simp [check1,ha,List.all_eq_true] at h
  simpa [hc] using h t ht

private theorem pair_ok {a b t : W} (ha : a ∉ targets) (hb : b ∉ targets) (ht : t ∈ targets)
    (hc : pair a b t = true) : owner a = some t ∨ owner b = some t ∨
      (owner a = none ∧ owner b = none ∧ a &&& b = t) := by
  have h := pair_cert a b
  simp [check2,ha,hb,List.all_eq_true] at h
  have r := h t ht
  simp [hc] at r
  tauto
private theorem reduce_can (a b c t : W) (Q : List W)
    (h : can (a::b::c::Q) t = true) :
    can (a::Q) t = true ∨ can (b::Q) t = true ∨ can (c::Q) t = true ∨
      pair a b t = true ∨ pair a c t = true ∨ pair b c t = true := by
  simp only [can_iff,List.mem_cons] at h ⊢
  obtain ⟨x,hx,hx'⟩ := h
  rcases hx' with hx'|⟨y,hy,hy'⟩
  · rcases hx with rfl|rfl|rfl|h <;> grind
  · rcases hx with rfl|rfl|rfl|h <;> rcases hy with rfl|rfl|rfl|h <;>
      first
      | exact Or.inl ⟨_, Or.inl rfl, Or.inr ⟨_, Or.inl rfl, hy'⟩⟩
      | exact Or.inr (Or.inl ⟨_, Or.inl rfl, Or.inr ⟨_, Or.inl rfl, hy'⟩⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨_, Or.inl rfl, Or.inr ⟨_, Or.inl rfl, hy'⟩⟩))
      | grind [pair_comm]

private def extra (a b : W) : List W :=
  if owner a = none ∧ owner b = none then [a &&& b] else []

private def pool (a b c : W) : List W :=
  (owner a).toList ++ (owner b).toList ++ (owner c).toList ++ extra a b ++ extra a c ++ extra b c

private theorem pool_length (a b c : W) : (pool a b c).length ≤ 3 := by
  cases ha : owner a <;> cases hb : owner b <;> cases hc : owner c <;> simp [pool,extra,ha,hb,hc]

private theorem from_pair {a b t : W} (ha : a ∉ targets) (hb : b ∉ targets) (ht : t ∈ targets)
    (h : pair a b t = true) :
    t ∈ (owner a).toList ∨ t ∈ (owner b).toList ∨ t ∈ extra a b := by
  rcases pair_ok ha hb ht h with e|e|⟨e,f,r⟩
  · simp [e]
  · simp [e]
  · simp [extra,e,f,r]

theorem no_three (a b c : W) (ha : a ∉ targets) (hb : b ∉ targets) (hc : c ∉ targets) :
    ¬ ∀ t ∈ targets, can (a :: b :: c :: (targets.erase t ++ base)) t = true := by
  intro h
  have incl : targets.toFinset ⊆ (pool a b c).toFinset := by
    intro t ht
    have ht' : t ∈ targets := List.mem_toFinset.mp ht
    apply List.mem_toFinset.mpr
    simp only [pool,List.mem_append]
    rcases reduce_can _ _ _ _ _ (h t ht') with z|z|z|z|z|z
    · simp [owner_ok ha ht' z]
    · simp [owner_ok hb ht' z]
    · simp [owner_ok hc ht' z]
    · have q := from_pair ha hb ht' z
      tauto
    · have q := from_pair ha hc ht' z
      tauto
    · have q := from_pair hb hc ht' z
      tauto
  have h1 := Finset.card_le_card incl
  have h2 := List.toFinset_card_le (pool a b c)
  have h3 := pool_length a b c
  have h4 : targets.toFinset.card = 4 := by decide
  omega

theorem can_mono {xs zs : List W} {t : W} (sub : xs ⊆ zs) (h : can xs t) : can zs t := by
  obtain ⟨a,ha,hs⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨a,sub ha,?_⟩
  rcases Bool.or_eq_true_iff.mp hs with hn|hb
  · simp [hn]
  · obtain ⟨b,hb,hv⟩ := List.any_eq_true.mp hb
    exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨b,sub hb,hv⟩))
theorem first_gate {ys : List W} (hh : History ys) (t : W) (ht : t ∈ ys) :
    ∃ zs : List W, zs ⊆ ys ∧ t ∉ zs ∧ can (zs ++ base) t := by
  induction hh with
  | nil => simp at ht
  | @cons x ys hh hx ih =>
    by_cases hin : t ∈ ys
    · obtain ⟨zs,hz,hn,hc⟩ := ih hin
      exact ⟨zs,List.subset_cons_of_subset _ hz,hn,hc⟩
    · have eq := (List.mem_cons.mp ht).resolve_right hin
      subst x
      exact ⟨ys,List.subset_cons_self _ _,hin,hx⟩
theorem three_slots (l : List W) (hlen : l.length ≤ 3) (hn : ∀ x ∈ l, x ∉ targets) :
    ∃ a b c : W, a ∉ targets ∧ b ∉ targets ∧ c ∉ targets ∧ l ⊆ [a,b,c] := by
  have hz : (0 : W) ∉ targets := by decide
  rcases l with _|⟨a,_|⟨b,_|⟨c,_|⟨d,ds⟩⟩⟩⟩
  · exact ⟨0,0,0,hz,hz,hz,by simp⟩
  · exact ⟨a,0,0,hn a (by simp),hz,hz,by simp⟩
  · exact ⟨a,b,0,hn a (by simp),hn b (by simp),hz,by simp⟩
  · exact ⟨a,b,c,hn a (by simp),hn b (by simp),hn c (by simp),by simp⟩
  · simp at hlen; omega
theorem short_fails (ys : List W) (hh : History ys) (hl : ys.length ≤ 7) (ht : targets ⊆ ys) : False := by
  let p := fun x : W => decide (x ∈ targets)
  let free := ys.filter (fun x => !p x)
  have ht' : targets ⊆ ys.filter p := fun x hx => List.mem_filter.mpr ⟨ht hx,by simp [p,hx]⟩
  have four := (by decide : targets.Nodup).length_le_of_subset ht'
  change 4 ≤ _ at four
  have sum := List.length_eq_length_filter_add (l := ys) p
  have len : free.length ≤ 3 := by dsimp [free]; omega
  have hn : ∀ x ∈ free, x ∉ targets := by intro x hx; simpa [p] using (List.mem_filter.mp hx).2
  obtain ⟨a,b,c,ha,hb,hc,cover⟩ := three_slots free len hn
  apply no_three a b c ha hb hc
  intro t htgt
  obtain ⟨zs,sub,hnz,gen⟩ := first_gate hh t (ht htgt)
  apply can_mono _ gen
  intro x hm
  rcases List.mem_append.mp hm with hx|hx
  · by_cases hxt : x ∈ targets
    · have hnxt : x ≠ t := fun e => hnz (e ▸ hx)
      have he : x ∈ targets.erase t := (List.mem_erase_of_ne hnxt).mpr hxt
      simp [he]
    · have hf := cover (List.mem_filter.mpr ⟨sub hx,by simp [p,hxt]⟩)
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
      rcases hf with rfl|rfl|rfl <;> simp
  · simp [hx]
def targetMask : Fin 4 → W := ![7,25,42,52]
def rows : Fin 4 → Finset (Fin 6) := ![{0,1,2},{0,3,4},{1,3,5},{2,4,5}]
theorem targetMask_co (i : Fin 4) (j : Fin 6) :
    coord j (targetMask i) = decide (∃ v ∈ rows i, inputs j v = true) := by
  fin_cases i <;> fin_cases j <;> decide
theorem output_mem (gs : List Gate) (ol : Fin 4 → Nat) (hg : ∀ g ∈ gs, valid g)
    (he : ∀ i x, Circuit.eval ⟨gs,ol i⟩ (List.ofFn x) =
       decide (∃ v ∈ rows i, x v = true)) (i : Fin 4) : targetMask i ∈ collect [] gs := by
  let w := raw ++ collect [] gs
  have hw : w.getD (ol i) 0 = targetMask i := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let j : Fin 6 := ⟨k,hk⟩
    change coord j _ = coord j _
    rw [read_co,targetMask_co,← he i (inputs j)]
    have h := collect_co [] gs hg j
    simp only [List.append_nil,start] at h
    rw [show w.map (coord j) = _ from h]
    rfl
  have hz : targetMask i ≠ 0 := by fin_cases i <;> decide
  have hr : targetMask i ∉ raw := by fin_cases i <;> decide
  simp only [List.getD] at hw
  cases h : w[ol i]? with
  | none => rw [h] at hw; exact (hz hw.symm).elim
  | some v =>
    rw [h] at hw
    exact (List.mem_append.mp (show targetMask i ∈ w from hw ▸ List.mem_of_getElem? h)).resolve_left hr
theorem lower (gs : List Gate) (ol : Fin 4 → Nat) (hg : ∀ g ∈ gs, valid g)
    (he : ∀ i x, Circuit.eval ⟨gs,ol i⟩ (List.ofFn x) = decide (∃ v ∈ rows i, x v = true)) :
    8 ≤ gs.length := by
  by_contra! small
  obtain ⟨hh,hl⟩ := collect_spec [] gs hg (by exact History.nil)
  apply short_fails (collect [] gs).reverse hh
  · simp only [List.length_reverse,hl,List.length_nil,Nat.zero_add]; omega
  · intro t ht
    apply List.mem_reverse.mpr
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl
    · exact output_mem gs ol hg he 0
    · exact output_mem gs ol hg he 1
    · exact output_mem gs ol hg he 2
    · exact output_mem gs ol hg he 3
end PEqualNP.Outside.Pasch1042
theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length := by
  intro _ gs ol hg _ he
  exact PEqualNP.Outside.Pasch1042.lower gs ol hg he
