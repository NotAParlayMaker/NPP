import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.Anchor1023
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
theorem step_can (raw : List W) (hraw : raw ⊆ base) (ys : List W) (g : Gate) (h : valid g) :
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
      · exact List.mem_append_right _ (hraw hr)
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
def collect (raw : List W) (ys : List W) : List Gate → List W
  | [] => ys
  | g :: gs => collect raw (ys ++ [step (raw ++ ys) g]) gs
theorem collect_spec (raw : List W) (hraw : raw ⊆ base) (ys : List W) (gs : List Gate) (hg : ∀ g ∈ gs, valid g)
    (hy : History ys.reverse) : History (collect raw ys gs).reverse ∧
    (collect raw ys gs).length = ys.length + gs.length := by
  induction gs generalizing ys with
  | nil => simp [collect,hy]
  | cons g gs ih =>
    have hh := History.cons hy (step_can raw hraw ys g (hg _ (by simp)))
    have hx := ih (ys ++ [step (raw ++ ys) g]) (fun a ha => hg a (by simp [ha])) (by simpa using hh)
    exact ⟨hx.1,by simpa [collect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2⟩
theorem collect_co (raw : List W) (ys : List W) (gs : List Gate) (hg : ∀ g ∈ gs, valid g) (j : Fin 6) :
    (raw ++ collect raw ys gs).map (coord j) =
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
  simp [_root_.PEqualNP.Outside.Anchor1023.pair,BitVec.and_comm a b,BitVec.or_comm a b]

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
def reserve := (targets ++ base).toFinset
theorem four_distinct (ys : List W) (hh : History ys) (ht : targets ⊆ ys) :
    4 ≤ (ys.toFinset \ reserve).card := by
  classical
  by_contra! small
  let F := ys.toFinset \ reserve
  have len : F.toList.length ≤ 3 := by simpa [F] using (show (ys.toFinset \ reserve).card ≤ 3 by omega)
  have hn : ∀ x ∈ F.toList, x ∉ targets := by
    intro x hx hxt
    have h := Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)
    exact h.2 (by simp [reserve,hxt])
  obtain ⟨a,b,c,ha,hb,hc,cover⟩ := three_slots _ len hn
  apply no_three a b c ha hb hc
  intro t htgt
  obtain ⟨zs,sub,hnz,gen⟩ := first_gate hh t (ht htgt)
  apply can_mono _ gen
  intro x hm
  rcases List.mem_append.mp hm with hx|hx
  · by_cases hxb : x ∈ base
    · simp [hxb]
    by_cases hxt : x ∈ targets
    · have hnxt : x ≠ t := fun e => hnz (e ▸ hx)
      have he := (List.mem_erase_of_ne hnxt).mpr hxt
      simp [he]
    have hf := cover (show x ∈ F.toList by simp [F,reserve,sub hx,hxt,hxb])
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl <;> simp
  · simp [hx]

abbrev Pt := Fin 7
def line (w : Pt) := ({0,1,3} : Finset Pt).image (·+w)
def atom : Pt → Pt → W := ![![63,1,2,32,4,8,16],![1,63,2,32,16,8,4],![1,2,63,4,16,8,32],![1,32,2,63,8,16,4],![1,2,16,4,63,32,8],![1,2,8,4,32,63,16],![1,2,32,4,8,16,63]]
def target : Pt → Pt → W := ![![63,7,42,52,63,25,63],![63,63,42,52,25,63,7],![7,63,63,52,25,42,63],![63,42,63,63,25,52,7],![7,63,52,63,63,42,25],![7,42,63,52,63,63,25],![7,42,52,63,25,63,63]]
def wires (p : Pt) := List.ofFn (atom p)
def bands (p : Pt) (j : Fin 6) : Pt → Bool := fun k => coord j (atom p k)
theorem bands_ok : ∀ (p : Pt) (j : Fin 6),
    (Finset.univ.filter (fun k => bands p j k = false)).card = 5 := by decide
theorem wires_base : ∀ p : Pt, wires p ⊆ base := by decide
theorem target_co : ∀ p w j, coord j (target p w) =
    decide (∃ k ∈ line w, bands p j k = true) := by decide
theorem all_targets : ∀ (p : Pt) (t : W), t ∈ targets → ∃ w, target p w = t := by decide
theorem target_in : ∀ (p w : Pt), target p w ∈ reserve := by decide
theorem target_separate : ∀ i j : Pt, (∀ p, target p i = target p j) → i=j := by decide
theorem target_not_raw : ∀ i j : Pt, ∃ p, target p i ≠ atom p j := by decide
theorem target_nonzero : ∀ p w : Pt, target p w ≠ 0 := by decide
theorem target_not_base : ∀ t : W, t ∈ targets → t ∉ base := by decide

def trace (p : Pt) (gs : List Gate) := collect (wires p) [] gs
def sig (p : Pt) (gs : List Gate) (i : ℕ) := (wires p ++ trace p gs).getD i 0
def Correct (gs : List Gate) (ol : Pt → ℕ) := ∀ w (x : Pt → Bool),
    ((Finset.univ.filter (fun p => x p=false)).card = 4 ∨
    (Finset.univ.filter (fun p => x p=false)).card = 5) →
    (Circuit.mk gs (ol w)).eval (List.ofFn x) = decide (∃ v ∈ line w,x v=true)

theorem sig_out (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) (p w : Pt) : sig p gs (ol w) = target p w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  let j : Fin 6 := ⟨k,hk⟩
  change coord j ((wires p ++ trace p gs).getD (ol w) 0) = coord j (target p w)
  rw [read_co,target_co,← he w (bands p j) (Or.inr (bands_ok p j))]
  have h := collect_co (wires p) [] gs hg j
  rw [show (wires p ++ trace p gs).map (coord j) = _ from h]
  simp only [List.append_nil,wires,List.map_ofFn]
  rfl

def gateRange (gs : List Gate) := Finset.Ico 7 (7+gs.length)
def outputs (ol : Pt → ℕ) := Finset.univ.image ol
def auxiliary (gs : List Gate) (ol : Pt → ℕ) := gateRange gs \ outputs ol
def projected (p : Pt) (gs : List Gate) (ol : Pt → ℕ) :=
  ((auxiliary gs ol).image (sig p gs)) \ reserve

private theorem trace_spec (p : Pt) (gs : List Gate) (hg : ∀ g ∈ gs, valid g) :
    History (trace p gs).reverse ∧ (trace p gs).length = gs.length := by
  simpa [trace] using collect_spec (wires p) (wires_base p) [] gs hg History.nil

private theorem sig_raw (p : Pt) (gs : List Gate) (i : Pt) : sig p gs i.val = atom p i := by
  rw [sig,List.getD_append _ _ _ _ (by simp [wires])]
  rw [List.getD_eq_getElem _ _ (by simp [wires])]
  fin_cases i <;> rfl

private theorem output_range (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) : outputs ol ⊆ gateRange gs := by
  intro i hi
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_Ico.mpr
  constructor
  · by_contra! lo
    let j : Pt := ⟨ol w,lo⟩
    obtain ⟨p,hsep⟩ := target_not_raw w j
    exact hsep ((sig_out gs ol hg he p w).symm.trans (sig_raw p gs j))
  · by_contra! high
    have h := sig_out gs ol hg he 0 w
    have len := (trace_spec 0 gs hg).2
    rw [sig,List.getD_eq_default _ _ (by simp [wires,len]; omega)] at h
    exact target_nonzero _ _ h.symm

private theorem outputs_card (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) : (outputs ol).card = 7 := by
  have hinj : Function.Injective ol := by
    intro i j hij
    apply target_separate
    intro p
    rw [← sig_out gs ol hg he p i,← sig_out gs ol hg he p j,hij]
  simp [outputs,Finset.card_image_of_injective _ hinj]

private theorem trace_target (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) (p : Pt) : targets ⊆ (trace p gs).reverse := by
  intro t ht
  apply List.mem_reverse.mpr
  obtain ⟨w, hw⟩ := all_targets p t ht
  have hs := (sig_out gs ol hg he p w).trans hw
  have hr := output_range gs ol hg he (show ol w ∈ outputs ol by simp [outputs])
  have hl := (trace_spec p gs hg).2
  have rr := Finset.mem_Ico.mp hr
  simp only [sig,List.getD_append_right _ _ _ _ (show (wires p).length ≤ ol w by simpa [wires] using rr.1)] at hs
  have hbound : ol w - (wires p).length < (trace p gs).length := by simp [wires,hl]; omega
  rw [List.getD_eq_getElem _ _ hbound] at hs
  exact hs ▸ List.getElem_mem ..

theorem projected_four (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) (p : Pt) : 4 ≤ (projected p gs ol).card := by
  classical
  have h := four_distinct (trace p gs).reverse (trace_spec p gs hg).1 (trace_target gs ol hg he p)
  apply h.trans (Finset.card_le_card ?_)
  intro t ht
  obtain ⟨hmem,hres⟩ := Finset.mem_sdiff.mp ht
  have hmem' : t ∈ trace p gs := List.mem_reverse.mp (List.mem_toFinset.mp hmem)
  obtain ⟨i,hi,hi'⟩ := List.mem_iff_getElem.mp hmem'
  have hl := (trace_spec p gs hg).2
  have hv : sig p gs (7+i) = t := by
    rw [sig,List.getD_append_right _ _ _ _ (by simp [wires])]
    rw [show 7+i-(wires p).length=i by simp [wires],List.getD_eq_getElem _ _ hi]; exact hi'
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_image.mpr ⟨7+i,Finset.mem_sdiff.mpr ⟨?_,?_⟩,hv⟩,hres⟩
  · apply Finset.mem_Ico.mpr; omega
  · intro ho
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp ho
    have eq := (sig_out gs ol hg he p w).symm.trans ((congrArg (sig p gs) hw).trans hv)
    exact hres (eq ▸ target_in p w)

theorem auxiliary_size (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) : (auxiliary gs ol).card + 7 = gs.length := by
  have h := Finset.card_sdiff_add_card_eq_card (output_range gs ol hg he)
  simpa [auxiliary,gateRange,outputs_card gs ol hg he] using h

theorem projection_lower (gs : List Gate) (ol : Pt → ℕ) (hg : ∀ g ∈ gs, valid g)
    (he : Correct gs ol) : 11 ≤ gs.length ∧ (gs.length ≤ 13 →
      ∀ p, (auxiliary gs ol).card - (projected p gs ol).card ≤ 2) := by
  have h := auxiliary_size gs ol hg he
  have hl := projected_four gs ol hg he 0
  have hu : (projected 0 gs ol).card ≤ (auxiliary gs ol).card :=
    (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_image_le
  exact ⟨by omega,by intro hs p; have := projected_four gs ol hg he p; omega⟩
end PEqualNP.Outside.Anchor1023

namespace PEqualNP.Outside.Fano1023
open CircuitLowerBounds
abbrev G := BitVec 21
def ins : List G := [33867, 67733, 135462, 270904, 541632, 1080320, 2064384]
def goal : List G := [372479, 744439, 1474366, 2089976, 1638347, 2096277, 2069871]
def index : Fin 7 → Fin 6 → Fin 21 := ![![0, 1, 6, 10, 15, 3],![0, 2, 16, 11, 7, 4],![1, 2, 5, 12, 8, 17],![3, 5, 18, 9, 13, 4],![6, 7, 9, 19, 8, 14],![10, 11, 13, 12, 20, 14],![15, 16, 18, 19, 20, 17]]
def project (p : Fin 7) (x : G) : Anchor1023.W :=
  BitVec.ofBoolListLE (List.ofFn fun b : Fin 6 => x.getLsbD (index p b).val)
theorem bit_project (p : Fin 7) (x : G) (j : Fin 6) :
   (project p x).getLsbD j.val = x.getLsbD (index p j).val := by
  unfold project
  apply BitVec.getLsbD_ofBoolListLE.trans
  fin_cases j <;> rfl
theorem project_ins : ∀ p, ins.map (project p) = Anchor1023.wires p := by decide +kernel
theorem project_target : ∀ (p w : Fin 7), project p (goal.getD w.val 0) = Anchor1023.target p w := by decide +kernel
theorem project_sep (x y : G) (he : ∀ p, project p x = project p y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have coverage : ∀ i : Fin 21, ∃ p j, index p j = i := by decide
  obtain ⟨p,j,eq⟩ := coverage ⟨i,hi⟩
  have h := congrArg (fun w : BitVec 6 => w.getLsbD j.val) (he p)
  simpa only [bit_project,eq] using h
def step (w : List G) (g : Gate) : G :=
  let x := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => x.foldr (.&&&.) 2097151
  | .or => x.foldr (.|||.) 0
  | .not => ~~~(x.headD 0)
  | _ => 0
def collect (ys : List G) : List Gate → List G
  | [] => ys
  | g :: gs => collect (ys ++ [step (ins ++ ys) g]) gs
def wide (gs : List Gate) (i : Nat) : G := (ins ++ collect [] gs).getD i 0
theorem project_zero (p : Fin 7) : project p 0 = 0 := by revert p; decide
theorem project_read (p : Fin 7) (w : List G) (i : Nat) :
    project p (w.getD i 0) = (w.map (project p)).getD i 0 := by
  simp only [List.getD,List.getElem?_map]
  cases w[i]? with
  | none => exact project_zero p
  | some v => rfl
theorem project_ops (p : Fin 7) (x y : G) :
  (project p (x &&& y) = (project p x &&& project p y)) ∧
  (project p (x ||| y) = (project p x ||| project p y)) ∧
  (project p (~~~x) = ~~~(project p x)) := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    let j : Fin 6 := ⟨i,hi⟩
    exact (bit_project p (x &&& y) j).trans (by rw [BitVec.getLsbD_and,BitVec.getLsbD_and,← bit_project p x j,← bit_project p y j])
  constructor
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    let j : Fin 6 := ⟨i,hi⟩
    exact (bit_project p (x ||| y) j).trans (by rw [BitVec.getLsbD_or,BitVec.getLsbD_or,← bit_project p x j,← bit_project p y j])
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    let j : Fin 6 := ⟨i,hi⟩
    exact (bit_project p (~~~x) j).trans (by rw [BitVec.getLsbD_not,BitVec.getLsbD_not,← bit_project p x j]; simp [hi,(index p j).isLt]; rfl)
theorem project_step (p : Fin 7) (w : List G) (g : Gate) (h : Anchor1023.valid g) :
    project p (step w g) = Anchor1023.step (w.map (project p)) g := by
  have full : project p 2097151 = 63 := by revert p; decide
  rcases g with ⟨o,x⟩
  rcases h with ⟨ho,hl⟩
  change x.length ≤ 2 at hl
  change o = .and ∨ o = .or ∨ o = .not at ho
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals try simp at hl
  all_goals try omega
  all_goals rcases ho with rfl|rfl|rfl <;>
    simp only [step,Anchor1023.step,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
      List.headD_nil,List.headD_cons,(project_ops p _ _).1,(project_ops p _ _).2.1,
      (project_ops p _ 0).2.2, full, project_zero, project_read]
theorem project_collect (p : Fin 7) (ys : List G) (gs : List Gate) (hg : ∀ g ∈ gs, Anchor1023.valid g) :
    (collect ys gs).map (project p) = Anchor1023.collect (Anchor1023.wires p) (ys.map (project p)) gs := by
  induction gs generalizing ys with
  | nil => rfl
  | cons g gs ih =>
    rw [collect,Anchor1023.collect,ih _ (fun a ha => hg a (by simp [ha]))]
    simp [List.map_append,project_step _ _ _ (hg g (by simp)),project_ins]
theorem project_wide (p : Fin 7) (gs : List Gate) (hg : ∀ g ∈ gs, Anchor1023.valid g) (i : Nat) :
    project p (wide gs i) = Anchor1023.sig p gs i := by
  unfold wide Anchor1023.sig Anchor1023.trace
  rw [project_read,List.map_append,project_ins,project_collect _ _ _ hg]; rfl
theorem wide_out (gs : List Gate) (ol : Fin 7 → Nat) (hg : ∀ g ∈ gs,Anchor1023.valid g)
    (he : Anchor1023.Correct gs ol) (w : Fin 7) : wide gs (ol w) = goal.getD w.val 0 := by
  apply project_sep
  intro p
  rw [project_wide _ _ hg,project_target,Anchor1023.sig_out _ _ hg he]
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
def base : List G := 0 :: 2097151 :: ins
def gate (xs : List G) (t : G) : Prop := ∃ a ∈ xs, ∃ b ∈ xs, t = a &&& b ∨ t = a ||| b
inductive Hist : List G → Prop
  | nil : Hist []
  | cons {v ys} : Hist ys → gate (ys ++ base) v → Hist (v::ys)
def aux (ys : List G) := ys.toFinset \ (goal ++ base).toFinset
def seen (S : Finset G) (p : Fin 7) := S.image (project p) \ Anchor1023.reserve
def quality (S : Finset G) := ∀ p, S.card ≤ (seen S p).card + 2
def fit (S : Finset G) := ∀ t ∈ goal, gate (S.toList ++ (goal.erase t ++ base)) t
def extend (S : Finset G) (v : G) := v ∉ goal ++ base ∧ v ∉ S ∧ gate (S.toList ++ (goal ++ base)) v
def Reach : ℕ → Finset G → Prop
  | 0, S => fit S
  | k+1, S => fit S ∨ ∃ v, extend S v ∧ quality (insert v S) ∧ Reach k (insert v S)
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
private theorem gate_mono {xs ys : List G} {v : G} (hs : xs ⊆ ys) (h : gate xs v) : gate ys v := by
  obtain ⟨a,ha,b,hb,hh⟩ := h
  exact ⟨a,hs ha,b,hs hb,hh⟩

private theorem seen_insert_bound (S : Finset G) (x : G) (p : Fin 7) :
    (seen (insert x S) p).card ≤ (seen S p).card + 1 := by
  apply (Finset.card_le_card (t := insert (project p x) (seen S p)) ?_).trans (Finset.card_insert_le ..)
  intro y hy
  obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hy
  rw [Finset.image_insert] at hm
  rcases Finset.mem_insert.mp hm with rfl|hm
  · simp
  · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hm,hn⟩)

private theorem quality_prev {S : Finset G} {x} (hx : x ∉ S) (h : quality (insert x S)) : quality S := by
  intro p
  have h1 := h p
  rw [Finset.card_insert_of_notMem hx] at h1
  have h2 := seen_insert_bound S x p
  omega

private inductive Build : Finset G → Prop
  | nil : Build ∅
  | step {S v} : Build S → extend S v → Build (insert v S)

private theorem build_hist {ys : List G} (hh : Hist ys) : Build (aux ys) := by
  induction hh with
  | nil => simpa [aux] using Build.nil
  | @cons v ys hh hv ih =>
    by_cases H : v ∈ goal ++ base
    · have he : aux (v::ys) = aux ys := by ext x; simp [aux] at *; grind
      rw [he]; exact ih
    · have he : aux (v::ys) = insert v (aux ys) := by ext x; simp [aux]; grind
      rw [he]
      by_cases hs : v ∈ aux ys
      · simpa [hs] using ih
      apply Build.step ih
      refine ⟨H,hs,gate_mono ?_ hv⟩
      intro x hx
      rcases List.mem_append.mp hx with h|h
      · by_cases h' : x ∈ goal ++ base
        · simp [h']
        · apply List.mem_append_left; apply Finset.mem_toList.mpr; exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr h,fun hx => h' (List.mem_toFinset.mp hx)⟩
      · simp [h]

private theorem first_wide {ys : List G} (hh : Hist ys) {t} (ht : t ∈ ys) :
    ∃ zs : List G, zs ⊆ ys ∧ t ∉ zs ∧ gate (zs ++ base) t := by
  induction hh with
  | nil => simp at ht
  | @cons x ys hh h ih =>
    by_cases hin : t ∈ ys
    · obtain ⟨zs,hz,hn,hc⟩ := ih hin
      exact ⟨zs,List.subset_cons_of_subset _ hz,hn,hc⟩
    · have eq := (List.mem_cons.mp ht).resolve_right hin
      subst x
      exact ⟨ys,List.subset_cons_self _ _,hin,h⟩

private theorem fit_hist {ys : List G} (hh : Hist ys) (hGoal : goal ⊆ ys) : fit (aux ys) := by
  intro t ht
  obtain ⟨zs,sub,hn,gen⟩ := first_wide hh (hGoal ht)
  apply gate_mono _ gen
  intro x hx
  rcases List.mem_append.mp hx with h|h
  · by_cases hg : x ∈ goal
    · have hnxt : x ≠ t := fun e => hn (e ▸ h)
      have h' := (List.mem_erase_of_ne hnxt).mpr hg
      simp [h']
    · by_cases hb : x ∈ base
      · simp [hb]
      · simp [aux,sub h,hg,hb]
  · simp [h]

private theorem to_root {S : Finset G} (hb : Build S) (hq : quality S)
    (n : ℕ) (hr : Reach n S) : Reach (S.card+n) ∅ := by
  induction hb generalizing n with
  | nil => simpa using hr
  | @step S v _ hv ih =>
    have h1 : Reach (n+1) S := Or.inr ⟨v,hv,hq,hr⟩
    have h2 := ih (quality_prev hv.2.1 hq) _ h1
    simpa [Finset.card_insert_of_notMem hv.2.1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h2

theorem reach_of_history {ys : List G} (hh : Hist ys) (hGoal : goal ⊆ ys) (hsize : (aux ys).card ≤ 6)
    (hq : ∀ p, 4 ≤ (seen (aux ys) p).card) : Reach 6 ∅ := by
  let S := aux ys
  have qual : quality S := fun p => by have := hq p; dsimp [S]; omega
  have fitS := fit_hist hh hGoal
  have rwit (n : ℕ) : Reach n S := by cases n with
                                      | zero => exact fitS
                                      | succ => exact Or.inl fitS
  have h := to_root (build_hist hh) qual (6-S.card) (rwit _)
  convert h using 1
  dsimp [S]; omega
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
open CircuitLowerBounds

private theorem step_gen (ys : List G) (g : Gate) (hg : Anchor1023.valid g)
    (hp : g.op = .and ∨ g.op = .or) : gate (ys.reverse ++ base) (step (ins ++ ys) g) := by
  let xs := ys.reverse ++ base
  have read (i : Nat) : (ins ++ ys).getD i 0 ∈ xs := by
    simp only [List.getD]
    cases hv : (ins ++ ys)[i]? with
    | none => simp [xs,base]
    | some v =>
      rcases List.mem_append.mp (List.mem_of_getElem? hv) with hr|hy
      · exact List.mem_append_right _ (by simp [base,hr])
      · exact List.mem_append_left _ (List.mem_reverse.mpr hy)
  have identity (v : G) (hv : v ∈ xs) : gate xs v :=
    ⟨v,hv,v,hv,Or.inl (by simp)⟩
  have h0 : (0 : G) ∈ xs := by simp [xs,base]
  have h1 : (2097151 : G) ∈ xs := by simp [xs,base]
  have hand (v : G) : v &&& 2097151 = v := by
    change v &&& BitVec.allOnes 21 = v
    exact BitVec.and_allOnes
  have hor (v : G) : v ||| 0 = v := BitVec.or_zero
  rcases g with ⟨o,x⟩
  have hl : x.length ≤ 2 := hg.2
  change o = .and ∨ o = .or at hp
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  all_goals try simp at hl
  all_goals try omega
  all_goals rcases hp with rfl|rfl
  all_goals change gate xs _
  all_goals simp only [step,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,hand,hor]
  all_goals first | exact identity _ h0 | exact identity _ h1 | exact identity _ (read _)
                  | exact ⟨_,read _,_,read _,Or.inl rfl⟩ | exact ⟨_,read _,_,read _,Or.inr rfl⟩

private theorem hist_len (ys : List G) (gs : List Gate) (hg : ∀ g ∈ gs, Anchor1023.valid g)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (hy : Hist ys.reverse) :
    Hist (collect ys gs).reverse ∧ (collect ys gs).length = ys.length + gs.length := by
  induction gs generalizing ys with
  | nil => simp [collect,hy]
  | cons g gs ih =>
    have hh := Hist.cons hy (step_gen ys g (hg _ (by simp)) (hm _ (by simp)))
    have hx := ih (ys ++ [step (ins ++ ys) g]) (fun a ha => hg a (by simp [ha]))
      (fun a ha => hm a (by simp [ha])) (by simpa using hh)
    exact ⟨hx.1,by simpa [collect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2⟩

private theorem all_goal : ∀ t ∈ goal, ∃ w : Fin 7, goal.getD w.val 0 = t := by
  intro t ht
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ht
  exact ⟨⟨i,hi⟩,List.getD_eq_getElem _ _ hi⟩

private theorem in_goals (gs : List Gate) (ol : Fin 7 → Nat) (hg : ∀ g ∈ gs,Anchor1023.valid g)
    (he : Anchor1023.Correct gs ol) : goal ⊆ (collect [] gs).reverse := by
  intro t ht
  obtain ⟨w,hw⟩ := all_goal t ht
  have h := (wide_out gs ol hg he w).trans hw
  have h0 : t ≠ 0 := fun h => (by decide : (0 : G) ∉ goal) (h ▸ ht)
  have hraw : t ∉ ins := fun h => (Finset.disjoint_left.mp (by decide : Disjoint goal.toFinset ins.toFinset)) (List.mem_toFinset.mpr ht) (List.mem_toFinset.mpr h)
  unfold wide at h
  simp only [List.getD] at h
  cases hx : (ins ++ collect [] gs)[ol w]? with
  | none => simp [hx] at h; exact (h0 h.symm).elim
  | some v =>
    have eq : v = t := by simpa [hx] using h
    subst v
    exact List.mem_reverse.mpr ((List.mem_append.mp (List.mem_of_getElem? hx)).resolve_left hraw)

private theorem aux_bound (ys : List G) (hg : goal ⊆ ys) (hl : ys.length ≤ 13) : (aux ys).card ≤ 6 := by
  have hs : goal.toFinset ⊆ ys.toFinset := fun _ h => List.mem_toFinset.mpr (hg (List.mem_toFinset.mp h))
  have hc := Finset.card_sdiff_add_card_eq_card hs
  have cg : goal.toFinset.card = 7 := by decide
  have hu := List.toFinset_card_le ys
  have hh : aux ys ⊆ ys.toFinset \ goal.toFinset := by
    intro v hv
    simp only [aux,Finset.mem_sdiff,List.mem_toFinset,List.mem_append,not_or] at hv ⊢
    exact ⟨hv.1,hv.2.1⟩
  have := Finset.card_le_card hh
  omega

private theorem exc_all (p : Fin 7) (v : G) (hv : v ∈ goal ++ base) : project p v ∈ Anchor1023.reserve := by
  have cert : ∀ p : Fin 7, (goal ++ base).all (fun v => decide (project p v ∈ Anchor1023.reserve)) = true := by decide +kernel
  simpa using List.all_eq_true.mp (cert p) v hv

private theorem projection_bound (gs : List Gate) (ol : Fin 7 → Nat) (hg : ∀ g ∈ gs,Anchor1023.valid g)
    (he : Anchor1023.Correct gs ol) (p : Fin 7) :
    4 ≤ (((aux (collect [] gs).reverse).image (project p)) \ Anchor1023.reserve).card := by
  apply (Anchor1023.projected_four gs ol hg he p).trans (Finset.card_le_card ?_)
  intro t ht
  obtain ⟨ht,hr⟩ := Finset.mem_sdiff.mp ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨wide gs i,?_,project_wide _ _ hg _⟩,hr⟩
  have hxc : wide gs i ∉ goal ++ base := by
    intro h
    exact hr (project_wide p gs hg i ▸ exc_all p _ h)
  have hraw : wide gs i ∉ ins := fun h => hxc (by simp [base,h])
  have h0 : wide gs i ≠ 0 := fun h => hxc (by simp [base,h])
  apply Finset.mem_sdiff.mpr
  refine ⟨List.mem_toFinset.mpr (List.mem_reverse.mpr ?_),by simpa using hxc⟩
  have h : (ins ++ collect [] gs)[i]? = some (wide gs i) := by
    unfold wide List.getD at *
    cases hi : (ins ++ collect [] gs)[i]? <;> simp_all
  exact (List.mem_append.mp (List.mem_of_getElem? h)).resolve_left hraw

theorem wide_history (gs : List Gate) (ol : Fin 7 → Nat) (hg : ∀ g ∈ gs,Anchor1023.valid g)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (he : Anchor1023.Correct gs ol) (hl : gs.length ≤ 13) :
    let ys := (collect [] gs).reverse
    Hist ys ∧ goal ⊆ ys ∧ (aux ys).card ≤ 6 ∧
      ∀ p, 4 ≤ (((aux ys).image (project p)) \ Anchor1023.reserve).card := by
  have h := hist_len [] gs hg hm Hist.nil
  have g := in_goals gs ol hg he
  exact ⟨h.1,g,aux_bound _ g (by simpa [h.2] using hl),projection_bound gs ol hg he⟩
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
abbrev PermId := Fin 168
def point (a : Fin 168) (i : Fin 7) : Fin 7 :=
  ((#[
    #[0, 1, 2, 3, 4, 5, 6],
    #[0, 1, 4, 3, 2, 6, 5],
    #[0, 1, 5, 3, 6, 2, 4],
    #[0, 1, 6, 3, 5, 4, 2],
    #[0, 2, 1, 6, 4, 5, 3],
    #[0, 2, 3, 6, 5, 4, 1],
    #[0, 2, 4, 6, 1, 3, 5],
    #[0, 2, 5, 6, 3, 1, 4],
    #[0, 3, 2, 1, 5, 4, 6],
    #[0, 3, 4, 1, 6, 2, 5],
    #[0, 3, 5, 1, 2, 6, 4],
    #[0, 3, 6, 1, 4, 5, 2],
    #[0, 4, 1, 5, 2, 6, 3],
    #[0, 4, 2, 5, 1, 3, 6],
    #[0, 4, 3, 5, 6, 2, 1],
    #[0, 4, 6, 5, 3, 1, 2],
    #[0, 5, 1, 4, 6, 2, 3],
    #[0, 5, 2, 4, 3, 1, 6],
    #[0, 5, 3, 4, 2, 6, 1],
    #[0, 5, 6, 4, 1, 3, 2],
    #[0, 6, 1, 2, 5, 4, 3],
    #[0, 6, 3, 2, 4, 5, 1],
    #[0, 6, 4, 2, 3, 1, 5],
    #[0, 6, 5, 2, 1, 3, 4],
    #[1, 0, 2, 3, 6, 5, 4],
    #[1, 0, 4, 3, 5, 6, 2],
    #[1, 0, 5, 3, 4, 2, 6],
    #[1, 0, 6, 3, 2, 4, 5],
    #[1, 2, 0, 4, 6, 5, 3],
    #[1, 2, 3, 4, 5, 6, 0],
    #[1, 2, 5, 4, 3, 0, 6],
    #[1, 2, 6, 4, 0, 3, 5],
    #[1, 3, 2, 0, 5, 6, 4],
    #[1, 3, 4, 0, 6, 5, 2],
    #[1, 3, 5, 0, 2, 4, 6],
    #[1, 3, 6, 0, 4, 2, 5],
    #[1, 4, 0, 2, 5, 6, 3],
    #[1, 4, 3, 2, 6, 5, 0],
    #[1, 4, 5, 2, 0, 3, 6],
    #[1, 4, 6, 2, 3, 0, 5],
    #[1, 5, 0, 6, 4, 2, 3],
    #[1, 5, 2, 6, 3, 0, 4],
    #[1, 5, 3, 6, 2, 4, 0],
    #[1, 5, 4, 6, 0, 3, 2],
    #[1, 6, 0, 5, 2, 4, 3],
    #[1, 6, 2, 5, 0, 3, 4],
    #[1, 6, 3, 5, 4, 2, 0],
    #[1, 6, 4, 5, 3, 0, 2],
    #[2, 0, 1, 6, 3, 5, 4],
    #[2, 0, 3, 6, 1, 4, 5],
    #[2, 0, 4, 6, 5, 3, 1],
    #[2, 0, 5, 6, 4, 1, 3],
    #[2, 1, 0, 4, 3, 5, 6],
    #[2, 1, 3, 4, 0, 6, 5],
    #[2, 1, 5, 4, 6, 0, 3],
    #[2, 1, 6, 4, 5, 3, 0],
    #[2, 3, 0, 5, 1, 4, 6],
    #[2, 3, 1, 5, 0, 6, 4],
    #[2, 3, 4, 5, 6, 0, 1],
    #[2, 3, 6, 5, 4, 1, 0],
    #[2, 4, 0, 1, 5, 3, 6],
    #[2, 4, 3, 1, 6, 0, 5],
    #[2, 4, 5, 1, 0, 6, 3],
    #[2, 4, 6, 1, 3, 5, 0],
    #[2, 5, 0, 3, 4, 1, 6],
    #[2, 5, 1, 3, 6, 0, 4],
    #[2, 5, 4, 3, 0, 6, 1],
    #[2, 5, 6, 3, 1, 4, 0],
    #[2, 6, 1, 0, 5, 3, 4],
    #[2, 6, 3, 0, 4, 1, 5],
    #[2, 6, 4, 0, 3, 5, 1],
    #[2, 6, 5, 0, 1, 4, 3],
    #[3, 0, 2, 1, 6, 4, 5],
    #[3, 0, 4, 1, 5, 2, 6],
    #[3, 0, 5, 1, 4, 6, 2],
    #[3, 0, 6, 1, 2, 5, 4],
    #[3, 1, 2, 0, 4, 6, 5],
    #[3, 1, 4, 0, 2, 5, 6],
    #[3, 1, 5, 0, 6, 4, 2],
    #[3, 1, 6, 0, 5, 2, 4],
    #[3, 2, 0, 5, 6, 4, 1],
    #[3, 2, 1, 5, 4, 6, 0],
    #[3, 2, 4, 5, 1, 0, 6],
    #[3, 2, 6, 5, 0, 1, 4],
    #[3, 4, 0, 6, 5, 2, 1],
    #[3, 4, 1, 6, 2, 5, 0],
    #[3, 4, 2, 6, 1, 0, 5],
    #[3, 4, 5, 6, 0, 1, 2],
    #[3, 5, 0, 2, 4, 6, 1],
    #[3, 5, 1, 2, 6, 4, 0],
    #[3, 5, 4, 2, 0, 1, 6],
    #[3, 5, 6, 2, 1, 0, 4],
    #[3, 6, 0, 4, 2, 5, 1],
    #[3, 6, 1, 4, 5, 2, 0],
    #[3, 6, 2, 4, 0, 1, 5],
    #[3, 6, 5, 4, 1, 0, 2],
    #[4, 0, 1, 5, 3, 6, 2],
    #[4, 0, 2, 5, 6, 3, 1],
    #[4, 0, 3, 5, 1, 2, 6],
    #[4, 0, 6, 5, 2, 1, 3],
    #[4, 1, 0, 2, 3, 6, 5],
    #[4, 1, 3, 2, 0, 5, 6],
    #[4, 1, 5, 2, 6, 3, 0],
    #[4, 1, 6, 2, 5, 0, 3],
    #[4, 2, 0, 1, 6, 3, 5],
    #[4, 2, 3, 1, 5, 0, 6],
    #[4, 2, 5, 1, 3, 6, 0],
    #[4, 2, 6, 1, 0, 5, 3],
    #[4, 3, 0, 6, 1, 2, 5],
    #[4, 3, 1, 6, 0, 5, 2],
    #[4, 3, 2, 6, 5, 0, 1],
    #[4, 3, 5, 6, 2, 1, 0],
    #[4, 5, 1, 0, 6, 3, 2],
    #[4, 5, 2, 0, 3, 6, 1],
    #[4, 5, 3, 0, 2, 1, 6],
    #[4, 5, 6, 0, 1, 2, 3],
    #[4, 6, 0, 3, 2, 1, 5],
    #[4, 6, 1, 3, 5, 0, 2],
    #[4, 6, 2, 3, 0, 5, 1],
    #[4, 6, 5, 3, 1, 2, 0],
    #[5, 0, 1, 4, 3, 2, 6],
    #[5, 0, 2, 4, 6, 1, 3],
    #[5, 0, 3, 4, 1, 6, 2],
    #[5, 0, 6, 4, 2, 3, 1],
    #[5, 1, 0, 6, 3, 2, 4],
    #[5, 1, 2, 6, 4, 0, 3],
    #[5, 1, 3, 6, 0, 4, 2],
    #[5, 1, 4, 6, 2, 3, 0],
    #[5, 2, 0, 3, 6, 1, 4],
    #[5, 2, 1, 3, 4, 0, 6],
    #[5, 2, 4, 3, 1, 6, 0],
    #[5, 2, 6, 3, 0, 4, 1],
    #[5, 3, 0, 2, 1, 6, 4],
    #[5, 3, 1, 2, 0, 4, 6],
    #[5, 3, 4, 2, 6, 1, 0],
    #[5, 3, 6, 2, 4, 0, 1],
    #[5, 4, 1, 0, 2, 3, 6],
    #[5, 4, 2, 0, 1, 6, 3],
    #[5, 4, 3, 0, 6, 1, 2],
    #[5, 4, 6, 0, 3, 2, 1],
    #[5, 6, 0, 1, 2, 3, 4],
    #[5, 6, 2, 1, 0, 4, 3],
    #[5, 6, 3, 1, 4, 0, 2],
    #[5, 6, 4, 1, 3, 2, 0],
    #[6, 0, 1, 2, 3, 4, 5],
    #[6, 0, 3, 2, 1, 5, 4],
    #[6, 0, 4, 2, 5, 1, 3],
    #[6, 0, 5, 2, 4, 3, 1],
    #[6, 1, 0, 5, 3, 4, 2],
    #[6, 1, 2, 5, 4, 3, 0],
    #[6, 1, 3, 5, 0, 2, 4],
    #[6, 1, 4, 5, 2, 0, 3],
    #[6, 2, 1, 0, 4, 3, 5],
    #[6, 2, 3, 0, 5, 1, 4],
    #[6, 2, 4, 0, 1, 5, 3],
    #[6, 2, 5, 0, 3, 4, 1],
    #[6, 3, 0, 4, 1, 5, 2],
    #[6, 3, 1, 4, 0, 2, 5],
    #[6, 3, 2, 4, 5, 1, 0],
    #[6, 3, 5, 4, 2, 0, 1],
    #[6, 4, 0, 3, 5, 1, 2],
    #[6, 4, 1, 3, 2, 0, 5],
    #[6, 4, 2, 3, 1, 5, 0],
    #[6, 4, 5, 3, 0, 2, 1],
    #[6, 5, 0, 1, 4, 3, 2],
    #[6, 5, 2, 1, 3, 4, 0],
    #[6, 5, 3, 1, 2, 0, 4],
    #[6, 5, 4, 1, 0, 2, 3]] : Array (Array (Fin 7))).getD a.val #[]).getD i.val 0
def edgeBack (a : Fin 168) (i : Fin 21) : Fin 21 :=
  ((#[
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    #[0, 6, 7, 3, 4, 9, 1, 2, 8, 5, 15, 16, 19, 18, 17, 10, 11, 14, 13, 12, 20],
    #[0, 10, 11, 3, 4, 13, 15, 16, 20, 18, 1, 2, 12, 5, 17, 6, 7, 14, 9, 19, 8],
    #[0, 15, 16, 3, 4, 18, 10, 11, 20, 13, 6, 7, 19, 9, 14, 1, 2, 17, 5, 12, 8],
    #[1, 0, 2, 15, 17, 16, 6, 8, 7, 19, 10, 12, 11, 20, 14, 3, 5, 4, 18, 9, 13],
    #[15, 0, 16, 1, 17, 2, 10, 20, 11, 12, 6, 19, 7, 8, 14, 3, 18, 4, 5, 13, 9],
    #[6, 0, 7, 10, 14, 11, 1, 8, 2, 12, 15, 19, 16, 20, 17, 3, 9, 4, 13, 5, 18],
    #[10, 0, 11, 6, 14, 7, 15, 20, 16, 19, 1, 12, 2, 8, 17, 3, 13, 4, 9, 18, 5],
    #[3, 1, 5, 0, 4, 2, 10, 13, 12, 11, 6, 9, 8, 7, 14, 15, 18, 17, 16, 20, 19],
    #[3, 10, 13, 0, 4, 11, 1, 5, 12, 2, 15, 18, 20, 16, 17, 6, 9, 14, 7, 8, 19],
    #[3, 6, 9, 0, 4, 7, 15, 18, 19, 16, 1, 5, 8, 2, 17, 10, 13, 14, 11, 20, 12],
    #[3, 15, 18, 0, 4, 16, 6, 9, 19, 7, 10, 13, 20, 11, 14, 1, 5, 17, 2, 8, 12],
    #[1, 6, 8, 15, 17, 19, 0, 2, 7, 16, 3, 5, 9, 18, 4, 10, 12, 14, 20, 11, 13],
    #[6, 1, 8, 10, 14, 12, 0, 7, 2, 11, 3, 9, 5, 13, 4, 15, 19, 17, 20, 16, 18],
    #[15, 10, 20, 1, 17, 12, 0, 16, 11, 2, 3, 18, 13, 5, 4, 6, 19, 14, 8, 7, 9],
    #[10, 15, 20, 6, 14, 19, 0, 11, 16, 7, 3, 13, 18, 9, 4, 1, 12, 17, 8, 2, 5],
    #[1, 10, 12, 15, 17, 20, 3, 5, 13, 18, 0, 2, 11, 16, 4, 6, 8, 14, 19, 9, 7],
    #[10, 1, 12, 6, 14, 8, 3, 13, 5, 9, 0, 11, 2, 7, 4, 15, 20, 17, 19, 18, 16],
    #[15, 6, 19, 1, 17, 8, 3, 18, 9, 5, 0, 16, 7, 2, 4, 10, 20, 14, 12, 13, 11],
    #[6, 15, 19, 10, 14, 20, 3, 9, 18, 13, 0, 7, 16, 11, 4, 1, 8, 17, 12, 5, 2],
    #[1, 3, 5, 15, 17, 18, 10, 12, 13, 20, 6, 8, 9, 19, 14, 0, 2, 4, 16, 11, 7],
    #[15, 3, 18, 1, 17, 5, 6, 19, 9, 8, 10, 20, 13, 12, 14, 0, 16, 4, 2, 7, 11],
    #[10, 3, 13, 6, 14, 9, 1, 12, 5, 8, 15, 20, 18, 19, 17, 0, 11, 4, 7, 2, 16],
    #[6, 3, 9, 10, 14, 13, 15, 19, 18, 20, 1, 8, 5, 12, 17, 0, 7, 4, 11, 16, 2],
    #[0, 2, 1, 4, 3, 5, 16, 15, 17, 18, 11, 10, 12, 13, 20, 7, 6, 8, 9, 19, 14],
    #[0, 16, 15, 4, 3, 18, 2, 1, 17, 5, 7, 6, 19, 9, 8, 11, 10, 20, 13, 12, 14],
    #[0, 11, 10, 4, 3, 13, 7, 6, 14, 9, 2, 1, 12, 5, 8, 16, 15, 20, 18, 19, 17],
    #[0, 7, 6, 4, 3, 9, 11, 10, 14, 13, 16, 15, 19, 18, 20, 2, 1, 8, 5, 12, 17],
    #[1, 2, 0, 17, 15, 16, 5, 3, 4, 18, 12, 10, 11, 20, 13, 8, 6, 7, 19, 9, 14],
    #[15, 16, 0, 17, 1, 2, 18, 3, 4, 5, 19, 6, 7, 8, 9, 20, 10, 11, 12, 13, 14],
    #[10, 11, 0, 14, 6, 7, 13, 3, 4, 9, 12, 1, 2, 8, 5, 20, 15, 16, 19, 18, 17],
    #[6, 7, 0, 14, 10, 11, 9, 3, 4, 13, 19, 15, 16, 20, 18, 8, 1, 2, 12, 5, 17],
    #[3, 5, 1, 4, 0, 2, 18, 15, 17, 16, 9, 6, 8, 7, 19, 13, 10, 12, 11, 20, 14],
    #[3, 18, 15, 4, 0, 16, 5, 1, 17, 2, 13, 10, 20, 11, 12, 9, 6, 19, 7, 8, 14],
    #[3, 9, 6, 4, 0, 7, 13, 10, 14, 11, 5, 1, 8, 2, 12, 18, 15, 19, 16, 20, 17],
    #[3, 13, 10, 4, 0, 11, 9, 6, 14, 7, 18, 15, 20, 16, 19, 5, 1, 12, 2, 8, 17],
    #[1, 5, 3, 17, 15, 18, 2, 0, 4, 16, 8, 6, 9, 19, 7, 12, 10, 13, 20, 11, 14],
    #[15, 18, 3, 17, 1, 5, 16, 0, 4, 2, 20, 10, 13, 12, 11, 19, 6, 9, 8, 7, 14],
    #[6, 9, 3, 14, 10, 13, 7, 0, 4, 11, 8, 1, 5, 12, 2, 19, 15, 18, 20, 16, 17],
    #[10, 13, 3, 14, 6, 9, 11, 0, 4, 7, 20, 15, 18, 19, 16, 12, 1, 5, 8, 2, 17],
    #[1, 12, 10, 17, 15, 20, 8, 6, 14, 19, 2, 0, 11, 16, 7, 5, 3, 13, 18, 9, 4],
    #[10, 12, 1, 14, 6, 8, 20, 15, 17, 19, 11, 0, 2, 7, 16, 13, 3, 5, 9, 18, 4],
    #[15, 19, 6, 17, 1, 8, 20, 10, 14, 12, 16, 0, 7, 2, 11, 18, 3, 9, 5, 13, 4],
    #[6, 19, 15, 14, 10, 20, 8, 1, 17, 12, 7, 0, 16, 11, 2, 9, 3, 18, 13, 5, 4],
    #[1, 8, 6, 17, 15, 19, 12, 10, 14, 20, 5, 3, 9, 18, 13, 2, 0, 7, 16, 11, 4],
    #[6, 8, 1, 14, 10, 12, 19, 15, 17, 20, 9, 3, 5, 13, 18, 7, 0, 2, 11, 16, 4],
    #[15, 20, 10, 17, 1, 12, 19, 6, 14, 8, 18, 3, 13, 5, 9, 16, 0, 11, 2, 7, 4],
    #[10, 20, 15, 14, 6, 19, 12, 1, 17, 8, 13, 3, 18, 9, 5, 11, 0, 16, 7, 2, 4],
    #[2, 0, 1, 7, 8, 6, 16, 17, 15, 19, 11, 12, 10, 14, 20, 4, 5, 3, 9, 18, 13],
    #[7, 0, 6, 2, 8, 1, 11, 14, 10, 12, 16, 19, 15, 17, 20, 4, 9, 3, 5, 13, 18],
    #[16, 0, 15, 11, 20, 10, 2, 17, 1, 12, 7, 19, 6, 14, 8, 4, 18, 3, 13, 5, 9],
    #[11, 0, 10, 16, 20, 15, 7, 14, 6, 19, 2, 12, 1, 17, 8, 4, 13, 3, 18, 9, 5],
    #[2, 1, 0, 8, 7, 6, 5, 4, 3, 9, 12, 11, 10, 14, 13, 17, 16, 15, 19, 18, 20],
    #[7, 6, 0, 8, 2, 1, 9, 4, 3, 5, 19, 16, 15, 17, 18, 14, 11, 10, 12, 13, 20],
    #[11, 10, 0, 20, 16, 15, 13, 4, 3, 18, 12, 2, 1, 17, 5, 14, 7, 6, 19, 9, 8],
    #[16, 15, 0, 20, 11, 10, 18, 4, 3, 13, 19, 7, 6, 14, 9, 17, 2, 1, 12, 5, 8],
    #[8, 1, 6, 2, 7, 0, 12, 14, 10, 11, 5, 9, 3, 4, 13, 17, 19, 15, 16, 20, 18],
    #[8, 6, 1, 7, 2, 0, 19, 17, 15, 16, 9, 5, 3, 4, 18, 14, 12, 10, 11, 20, 13],
    #[20, 10, 15, 11, 16, 0, 12, 17, 1, 2, 13, 18, 3, 4, 5, 14, 19, 6, 7, 8, 9],
    #[20, 15, 10, 16, 11, 0, 19, 14, 6, 7, 18, 13, 3, 4, 9, 17, 12, 1, 2, 8, 5],
    #[5, 1, 3, 12, 13, 10, 2, 4, 0, 11, 8, 9, 6, 14, 7, 17, 18, 15, 20, 16, 19],
    #[13, 10, 3, 12, 5, 1, 11, 4, 0, 2, 20, 18, 15, 17, 16, 14, 9, 6, 8, 7, 19],
    #[9, 6, 3, 19, 18, 15, 7, 4, 0, 16, 8, 5, 1, 17, 2, 14, 13, 10, 20, 11, 12],
    #[18, 15, 3, 19, 9, 6, 16, 4, 0, 7, 20, 13, 10, 14, 11, 17, 5, 1, 8, 2, 12],
    #[12, 1, 10, 5, 13, 3, 8, 14, 6, 9, 2, 11, 0, 4, 7, 17, 20, 15, 18, 19, 16],
    #[12, 10, 1, 13, 5, 3, 20, 17, 15, 18, 11, 2, 0, 4, 16, 14, 8, 6, 9, 19, 7],
    #[19, 6, 15, 9, 18, 3, 8, 17, 1, 5, 7, 16, 0, 4, 2, 14, 20, 10, 13, 12, 11],
    #[19, 15, 6, 18, 9, 3, 20, 14, 10, 13, 16, 7, 0, 4, 11, 17, 8, 1, 5, 12, 2],
    #[5, 3, 1, 13, 12, 10, 18, 17, 15, 20, 9, 8, 6, 14, 19, 4, 2, 0, 11, 16, 7],
    #[13, 3, 10, 5, 12, 1, 9, 14, 6, 8, 18, 20, 15, 17, 19, 4, 11, 0, 2, 7, 16],
    #[18, 3, 15, 9, 19, 6, 5, 17, 1, 8, 13, 20, 10, 14, 12, 4, 16, 0, 7, 2, 11],
    #[9, 3, 6, 18, 19, 15, 13, 14, 10, 20, 5, 8, 1, 17, 12, 4, 7, 0, 16, 11, 2],
    #[4, 2, 5, 0, 3, 1, 11, 13, 12, 10, 16, 18, 17, 15, 20, 7, 9, 8, 6, 14, 19],
    #[4, 11, 13, 0, 3, 10, 2, 5, 12, 1, 7, 9, 14, 6, 8, 16, 18, 20, 15, 17, 19],
    #[4, 16, 18, 0, 3, 15, 7, 9, 19, 6, 2, 5, 17, 1, 8, 11, 13, 20, 10, 14, 12],
    #[4, 7, 9, 0, 3, 6, 16, 18, 19, 15, 11, 13, 14, 10, 20, 2, 5, 8, 1, 17, 12],
    #[4, 5, 2, 3, 0, 1, 9, 7, 8, 6, 18, 16, 17, 15, 19, 13, 11, 12, 10, 14, 20],
    #[4, 9, 7, 3, 0, 6, 5, 2, 8, 1, 13, 11, 14, 10, 12, 18, 16, 19, 15, 17, 20],
    #[4, 18, 16, 3, 0, 15, 13, 11, 20, 10, 5, 2, 17, 1, 12, 9, 7, 19, 6, 14, 8],
    #[4, 13, 11, 3, 0, 10, 18, 16, 20, 15, 9, 7, 14, 6, 19, 5, 2, 12, 1, 17, 8],
    #[17, 2, 16, 1, 15, 0, 12, 20, 11, 10, 5, 18, 4, 3, 13, 8, 19, 7, 6, 14, 9],
    #[17, 16, 2, 15, 1, 0, 19, 8, 7, 6, 18, 5, 4, 3, 9, 20, 12, 11, 10, 14, 13],
    #[14, 11, 7, 10, 6, 0, 12, 8, 2, 1, 13, 9, 4, 3, 5, 20, 19, 16, 15, 17, 18],
    #[14, 7, 11, 6, 10, 0, 19, 20, 16, 15, 9, 13, 4, 3, 18, 8, 12, 2, 1, 17, 5],
    #[17, 12, 20, 1, 15, 10, 2, 16, 11, 0, 8, 19, 14, 6, 7, 5, 18, 13, 3, 4, 9],
    #[17, 19, 8, 15, 1, 6, 16, 2, 7, 0, 20, 12, 14, 10, 11, 18, 5, 9, 3, 4, 13],
    #[14, 12, 8, 10, 6, 1, 11, 7, 2, 0, 20, 19, 17, 15, 16, 13, 9, 5, 3, 4, 18],
    #[14, 19, 20, 6, 10, 15, 7, 11, 16, 0, 8, 12, 17, 1, 2, 9, 13, 18, 3, 4, 5],
    #[17, 5, 18, 1, 15, 3, 8, 19, 9, 6, 2, 16, 4, 0, 7, 12, 20, 13, 10, 14, 11],
    #[17, 18, 5, 15, 1, 3, 20, 12, 13, 10, 16, 2, 4, 0, 11, 19, 8, 9, 6, 14, 7],
    #[14, 9, 13, 6, 10, 3, 8, 12, 5, 1, 7, 11, 4, 0, 2, 19, 20, 18, 15, 17, 16],
    #[14, 13, 9, 10, 6, 3, 20, 19, 18, 15, 11, 7, 4, 0, 16, 12, 8, 5, 1, 17, 2],
    #[17, 8, 19, 1, 15, 6, 5, 18, 9, 3, 12, 20, 14, 10, 13, 2, 16, 7, 0, 4, 11],
    #[17, 20, 12, 15, 1, 10, 18, 5, 13, 3, 19, 8, 14, 6, 9, 16, 2, 11, 0, 4, 7],
    #[14, 8, 12, 6, 10, 1, 9, 13, 5, 3, 19, 20, 17, 15, 18, 7, 11, 2, 0, 4, 16],
    #[14, 20, 19, 10, 6, 15, 13, 9, 18, 3, 12, 8, 17, 1, 5, 11, 7, 16, 0, 4, 2],
    #[2, 16, 17, 7, 8, 19, 0, 1, 15, 6, 4, 5, 18, 9, 3, 11, 12, 20, 14, 10, 13],
    #[16, 2, 17, 11, 20, 12, 0, 15, 1, 10, 4, 18, 5, 13, 3, 7, 19, 8, 14, 6, 9],
    #[7, 11, 14, 2, 8, 12, 0, 6, 10, 1, 4, 9, 13, 5, 3, 16, 19, 20, 17, 15, 18],
    #[11, 7, 14, 16, 20, 19, 0, 10, 6, 15, 4, 13, 9, 18, 3, 2, 12, 8, 17, 1, 5],
    #[2, 5, 4, 8, 7, 9, 1, 0, 3, 6, 17, 16, 18, 19, 15, 12, 11, 13, 14, 10, 20],
    #[7, 9, 4, 8, 2, 5, 6, 0, 3, 1, 14, 11, 13, 12, 10, 19, 16, 18, 17, 15, 20],
    #[16, 18, 4, 20, 11, 13, 15, 0, 3, 10, 17, 2, 5, 12, 1, 19, 7, 9, 14, 6, 8],
    #[11, 13, 4, 20, 16, 18, 10, 0, 3, 15, 14, 7, 9, 19, 6, 12, 2, 5, 17, 1, 8],
    #[5, 2, 4, 12, 13, 11, 1, 3, 0, 10, 17, 18, 16, 20, 15, 8, 9, 7, 14, 6, 19],
    #[13, 11, 4, 12, 5, 2, 10, 3, 0, 1, 14, 9, 7, 8, 6, 20, 18, 16, 17, 15, 19],
    #[18, 16, 4, 19, 9, 7, 15, 3, 0, 6, 17, 5, 2, 8, 1, 20, 13, 11, 14, 10, 12],
    #[9, 7, 4, 19, 18, 16, 6, 3, 0, 15, 14, 13, 11, 20, 10, 8, 5, 2, 17, 1, 12],
    #[8, 12, 14, 2, 7, 11, 1, 6, 10, 0, 17, 19, 20, 16, 15, 5, 9, 13, 4, 3, 18],
    #[8, 19, 17, 7, 2, 16, 6, 1, 15, 0, 14, 12, 20, 11, 10, 9, 5, 18, 4, 3, 13],
    #[20, 12, 17, 11, 16, 2, 10, 15, 1, 0, 14, 19, 8, 7, 6, 13, 18, 5, 4, 3, 9],
    #[20, 19, 14, 16, 11, 7, 15, 10, 6, 0, 17, 12, 8, 2, 1, 18, 13, 9, 4, 3, 5],
    #[5, 18, 17, 13, 12, 20, 3, 1, 15, 10, 4, 2, 16, 11, 0, 9, 8, 19, 14, 6, 7],
    #[18, 5, 17, 9, 19, 8, 3, 15, 1, 6, 4, 16, 2, 7, 0, 13, 20, 12, 14, 10, 11],
    #[13, 9, 14, 5, 12, 8, 3, 10, 6, 1, 4, 11, 7, 2, 0, 18, 20, 19, 17, 15, 16],
    #[9, 13, 14, 18, 19, 20, 3, 6, 10, 15, 4, 7, 11, 16, 0, 5, 8, 12, 17, 1, 2],
    #[12, 8, 14, 5, 13, 9, 1, 10, 6, 3, 17, 20, 19, 18, 15, 2, 11, 7, 4, 0, 16],
    #[12, 20, 17, 13, 5, 18, 10, 1, 15, 3, 14, 8, 19, 9, 6, 11, 2, 16, 4, 0, 7],
    #[19, 8, 17, 9, 18, 5, 6, 15, 1, 3, 14, 20, 12, 13, 10, 7, 16, 2, 4, 0, 11],
    #[19, 20, 14, 18, 9, 13, 15, 6, 10, 3, 17, 8, 12, 5, 1, 16, 7, 11, 4, 0, 2],
    #[2, 11, 12, 7, 8, 14, 4, 5, 13, 9, 0, 1, 10, 6, 3, 16, 17, 20, 19, 18, 15],
    #[11, 2, 12, 16, 20, 17, 4, 13, 5, 18, 0, 10, 1, 15, 3, 7, 14, 8, 19, 9, 6],
    #[7, 16, 19, 2, 8, 17, 4, 9, 18, 5, 0, 6, 15, 1, 3, 11, 14, 20, 12, 13, 10],
    #[16, 7, 19, 11, 20, 14, 4, 18, 9, 13, 0, 15, 6, 10, 3, 2, 17, 8, 12, 5, 1],
    #[2, 12, 11, 8, 7, 14, 17, 16, 20, 19, 1, 0, 10, 6, 15, 5, 4, 13, 9, 18, 3],
    #[11, 12, 2, 20, 16, 17, 14, 7, 8, 19, 10, 0, 1, 15, 6, 13, 4, 5, 18, 9, 3],
    #[7, 19, 16, 8, 2, 17, 14, 11, 20, 12, 6, 0, 15, 1, 10, 9, 4, 18, 5, 13, 3],
    #[16, 19, 7, 20, 11, 14, 17, 2, 8, 12, 15, 0, 6, 10, 1, 18, 4, 9, 13, 5, 3],
    #[12, 2, 11, 5, 13, 4, 17, 20, 16, 18, 1, 10, 0, 3, 15, 8, 14, 7, 9, 19, 6],
    #[12, 11, 2, 13, 5, 4, 14, 8, 7, 9, 10, 1, 0, 3, 6, 20, 17, 16, 18, 19, 15],
    #[19, 16, 7, 18, 9, 4, 17, 8, 2, 5, 15, 6, 0, 3, 1, 20, 14, 11, 13, 12, 10],
    #[19, 7, 16, 9, 18, 4, 14, 20, 11, 13, 6, 15, 0, 3, 10, 8, 17, 2, 5, 12, 1],
    #[8, 5, 9, 2, 7, 4, 17, 19, 18, 16, 1, 6, 3, 0, 15, 12, 14, 13, 11, 20, 10],
    #[8, 9, 5, 7, 2, 4, 14, 12, 13, 11, 6, 1, 3, 0, 10, 19, 17, 18, 16, 20, 15],
    #[20, 18, 13, 16, 11, 4, 17, 12, 5, 2, 15, 10, 3, 0, 1, 19, 14, 9, 7, 8, 6],
    #[20, 13, 18, 11, 16, 4, 14, 19, 9, 7, 10, 15, 3, 0, 6, 12, 17, 5, 2, 8, 1],
    #[5, 9, 8, 13, 12, 14, 4, 2, 7, 11, 3, 1, 6, 10, 0, 18, 17, 19, 20, 16, 15],
    #[9, 5, 8, 18, 19, 17, 4, 7, 2, 16, 3, 6, 1, 15, 0, 13, 14, 12, 20, 11, 10],
    #[13, 18, 20, 5, 12, 17, 4, 11, 16, 2, 3, 10, 15, 1, 0, 9, 14, 19, 8, 7, 6],
    #[18, 13, 20, 9, 19, 14, 4, 16, 11, 7, 3, 15, 10, 6, 0, 5, 17, 12, 8, 2, 1],
    #[5, 8, 9, 12, 13, 14, 17, 18, 19, 20, 1, 3, 6, 10, 15, 2, 4, 7, 11, 16, 0],
    #[9, 8, 5, 19, 18, 17, 14, 13, 12, 20, 6, 3, 1, 15, 10, 7, 4, 2, 16, 11, 0],
    #[13, 20, 18, 12, 5, 17, 14, 9, 19, 8, 10, 3, 15, 1, 6, 11, 4, 16, 2, 7, 0],
    #[18, 20, 13, 19, 9, 14, 17, 5, 12, 8, 15, 3, 10, 6, 1, 16, 4, 11, 7, 2, 0],
    #[2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 0, 1, 3, 6, 10, 15],
    #[7, 4, 9, 2, 8, 5, 16, 19, 18, 17, 11, 14, 13, 12, 20, 0, 6, 3, 1, 15, 10],
    #[11, 4, 13, 16, 20, 18, 2, 12, 5, 17, 7, 14, 9, 19, 8, 0, 10, 3, 15, 1, 6],
    #[16, 4, 18, 11, 20, 13, 7, 19, 9, 14, 2, 17, 5, 12, 8, 0, 15, 3, 10, 6, 1],
    #[2, 17, 16, 8, 7, 19, 12, 11, 20, 14, 5, 4, 18, 9, 13, 1, 0, 15, 6, 10, 3],
    #[16, 17, 2, 20, 11, 12, 19, 7, 8, 14, 18, 4, 5, 13, 9, 15, 0, 1, 10, 6, 3],
    #[7, 14, 11, 8, 2, 12, 19, 16, 20, 17, 9, 4, 13, 5, 18, 6, 0, 10, 1, 15, 3],
    #[11, 14, 7, 20, 16, 19, 12, 2, 8, 17, 13, 4, 9, 18, 5, 10, 0, 6, 15, 1, 3],
    #[5, 4, 2, 13, 12, 11, 9, 8, 7, 14, 18, 17, 16, 20, 19, 3, 1, 0, 10, 6, 15],
    #[13, 4, 11, 5, 12, 2, 18, 20, 16, 17, 9, 14, 7, 8, 19, 3, 10, 0, 1, 15, 6],
    #[9, 4, 7, 18, 19, 16, 5, 8, 2, 17, 13, 14, 11, 20, 12, 3, 6, 0, 15, 1, 10],
    #[18, 4, 16, 9, 19, 7, 13, 20, 11, 14, 5, 17, 2, 8, 12, 3, 15, 0, 6, 10, 1],
    #[8, 17, 19, 2, 7, 16, 5, 9, 18, 4, 12, 14, 20, 11, 13, 1, 6, 15, 0, 3, 10],
    #[8, 14, 12, 7, 2, 11, 9, 5, 13, 4, 19, 17, 20, 16, 18, 6, 1, 10, 0, 3, 15],
    #[20, 17, 12, 16, 11, 2, 18, 13, 5, 4, 19, 14, 8, 7, 9, 15, 10, 1, 0, 3, 6],
    #[20, 14, 19, 11, 16, 7, 13, 18, 9, 4, 12, 17, 8, 2, 5, 10, 15, 6, 0, 3, 1],
    #[12, 17, 20, 5, 13, 18, 2, 11, 16, 4, 8, 14, 19, 9, 7, 1, 10, 15, 3, 0, 6],
    #[12, 14, 8, 13, 5, 9, 11, 2, 7, 4, 20, 17, 19, 18, 16, 10, 1, 6, 3, 0, 15],
    #[19, 17, 8, 18, 9, 5, 16, 7, 2, 4, 20, 14, 12, 13, 11, 15, 6, 1, 3, 0, 10],
    #[19, 14, 20, 9, 18, 13, 7, 16, 11, 4, 8, 17, 12, 5, 2, 6, 15, 10, 3, 0, 1],
    #[5, 17, 18, 12, 13, 20, 8, 9, 19, 14, 2, 4, 16, 11, 7, 1, 3, 15, 10, 6, 0],
    #[18, 17, 5, 19, 9, 8, 20, 13, 12, 14, 16, 4, 2, 7, 11, 15, 3, 1, 6, 10, 0],
    #[13, 14, 9, 12, 5, 8, 20, 18, 19, 17, 11, 4, 7, 2, 16, 10, 3, 6, 1, 15, 0],
    #[9, 14, 13, 19, 18, 20, 8, 5, 12, 17, 7, 4, 11, 16, 2, 6, 3, 10, 15, 1, 0]] : Array (Array (Fin 21))).getD a.val #[]).getD i.val 0
def smallBack (a : Fin 24) (i : Fin 6) : Fin 6 :=
  ((#[
    #[0, 1, 2, 3, 4, 5],
    #[0, 2, 1, 4, 3, 5],
    #[0, 3, 4, 1, 2, 5],
    #[0, 4, 3, 2, 1, 5],
    #[1, 0, 2, 3, 5, 4],
    #[1, 2, 0, 5, 3, 4],
    #[1, 3, 5, 0, 2, 4],
    #[1, 5, 3, 2, 0, 4],
    #[2, 0, 1, 4, 5, 3],
    #[2, 1, 0, 5, 4, 3],
    #[2, 4, 5, 0, 1, 3],
    #[2, 5, 4, 1, 0, 3],
    #[3, 0, 4, 1, 5, 2],
    #[3, 1, 5, 0, 4, 2],
    #[3, 4, 0, 5, 1, 2],
    #[3, 5, 1, 4, 0, 2],
    #[4, 0, 3, 2, 5, 1],
    #[4, 2, 5, 0, 3, 1],
    #[4, 3, 0, 5, 2, 1],
    #[4, 5, 2, 3, 0, 1],
    #[5, 1, 3, 2, 4, 0],
    #[5, 2, 4, 1, 3, 0],
    #[5, 3, 1, 4, 2, 0],
    #[5, 4, 2, 3, 1, 0]] : Array (Array (Fin 6))).getD a.val #[]).getD i.val 0
def localId (a : Fin 168) (i : Fin 7) : Fin 24 :=
  ((#[
    #[0, 0, 0, 0, 0, 0, 0],
    #[1, 3, 0, 2, 0, 0, 0],
    #[2, 2, 0, 3, 0, 0, 0],
    #[3, 1, 0, 1, 0, 0, 0],
    #[4, 0, 0, 0, 3, 2, 0],
    #[16, 1, 0, 1, 2, 3, 0],
    #[8, 3, 3, 2, 0, 0, 2],
    #[12, 2, 2, 3, 0, 0, 3],
    #[20, 0, 1, 0, 1, 1, 1],
    #[22, 2, 1, 3, 1, 1, 1],
    #[21, 3, 1, 2, 1, 1, 1],
    #[23, 1, 1, 1, 1, 1, 1],
    #[5, 0, 3, 0, 3, 2, 2],
    #[9, 3, 3, 2, 3, 2, 2],
    #[18, 1, 2, 1, 2, 3, 3],
    #[14, 2, 2, 3, 2, 3, 3],
    #[6, 0, 2, 0, 3, 2, 3],
    #[13, 2, 2, 3, 3, 2, 3],
    #[17, 1, 3, 1, 2, 3, 2],
    #[10, 3, 3, 2, 2, 3, 2],
    #[7, 0, 1, 0, 3, 2, 1],
    #[19, 1, 1, 1, 2, 3, 1],
    #[15, 2, 2, 3, 1, 1, 3],
    #[11, 3, 3, 2, 1, 1, 2],
    #[0, 0, 4, 20, 4, 4, 4],
    #[3, 1, 4, 21, 4, 4, 4],
    #[2, 2, 4, 23, 4, 4, 4],
    #[1, 3, 4, 22, 4, 4, 4],
    #[4, 4, 0, 4, 16, 12, 20],
    #[16, 8, 20, 8, 12, 16, 0],
    #[12, 12, 12, 16, 20, 0, 16],
    #[8, 16, 16, 12, 0, 20, 12],
    #[20, 20, 8, 0, 8, 8, 8],
    #[23, 21, 8, 1, 8, 8, 8],
    #[21, 23, 8, 2, 8, 8, 8],
    #[22, 22, 8, 3, 8, 8, 8],
    #[7, 4, 1, 4, 16, 12, 21],
    #[19, 8, 21, 8, 12, 16, 1],
    #[11, 16, 16, 12, 1, 21, 12],
    #[15, 12, 12, 16, 21, 1, 16],
    #[6, 4, 2, 4, 16, 12, 23],
    #[13, 12, 12, 16, 23, 2, 16],
    #[17, 8, 23, 8, 12, 16, 2],
    #[10, 16, 16, 12, 2, 23, 12],
    #[5, 4, 3, 4, 16, 12, 22],
    #[9, 16, 16, 12, 3, 22, 12],
    #[18, 8, 22, 8, 12, 16, 3],
    #[14, 12, 12, 16, 22, 3, 16],
    #[0, 4, 4, 20, 4, 6, 7],
    #[1, 16, 4, 22, 4, 7, 6],
    #[3, 8, 7, 21, 6, 4, 4],
    #[2, 12, 6, 23, 7, 4, 4],
    #[4, 4, 4, 7, 16, 13, 20],
    #[8, 16, 16, 15, 4, 20, 13],
    #[12, 12, 13, 19, 20, 4, 16],
    #[16, 8, 20, 11, 13, 16, 4],
    #[5, 4, 16, 6, 16, 15, 22],
    #[9, 16, 16, 13, 16, 22, 15],
    #[14, 12, 15, 17, 22, 16, 16],
    #[18, 8, 22, 10, 15, 16, 16],
    #[7, 7, 8, 4, 17, 12, 21],
    #[15, 15, 12, 16, 21, 8, 17],
    #[11, 19, 17, 12, 8, 21, 12],
    #[19, 11, 21, 8, 12, 17, 8],
    #[6, 6, 12, 4, 19, 12, 23],
    #[13, 13, 12, 16, 23, 12, 19],
    #[10, 17, 19, 12, 12, 23, 12],
    #[17, 10, 23, 8, 12, 19, 12],
    #[20, 20, 8, 4, 10, 8, 11],
    #[22, 22, 8, 16, 11, 8, 10],
    #[23, 21, 11, 8, 8, 10, 8],
    #[21, 23, 10, 12, 8, 11, 8],
    #[0, 20, 5, 20, 5, 5, 5],
    #[2, 22, 5, 23, 5, 5, 5],
    #[3, 21, 5, 21, 5, 5, 5],
    #[1, 23, 5, 22, 5, 5, 5],
    #[20, 20, 9, 20, 9, 9, 9],
    #[21, 23, 9, 22, 9, 9, 9],
    #[23, 21, 9, 21, 9, 9, 9],
    #[22, 22, 9, 23, 9, 9, 9],
    #[4, 5, 20, 5, 18, 14, 20],
    #[16, 9, 20, 9, 14, 18, 20],
    #[12, 14, 14, 18, 20, 20, 18],
    #[8, 18, 18, 14, 20, 20, 14],
    #[6, 5, 22, 5, 18, 14, 23],
    #[17, 9, 23, 9, 14, 18, 22],
    #[13, 14, 14, 18, 23, 22, 18],
    #[10, 18, 18, 14, 22, 23, 14],
    #[7, 5, 21, 5, 18, 14, 21],
    #[19, 9, 21, 9, 14, 18, 21],
    #[11, 18, 18, 14, 21, 21, 14],
    #[15, 14, 14, 18, 21, 21, 18],
    #[5, 5, 23, 5, 18, 14, 22],
    #[18, 9, 22, 9, 14, 18, 23],
    #[9, 18, 18, 14, 23, 22, 14],
    #[14, 14, 14, 18, 22, 23, 18],
    #[0, 5, 7, 20, 6, 6, 7],
    #[3, 9, 7, 21, 6, 6, 7],
    #[1, 18, 6, 22, 7, 7, 6],
    #[2, 14, 6, 23, 7, 7, 6],
    #[4, 7, 5, 7, 17, 13, 20],
    #[8, 19, 17, 15, 5, 20, 13],
    #[16, 11, 20, 11, 13, 17, 5],
    #[12, 15, 13, 19, 20, 5, 17],
    #[7, 7, 9, 7, 17, 13, 21],
    #[15, 15, 13, 19, 21, 9, 17],
    #[19, 11, 21, 11, 13, 17, 9],
    #[11, 19, 17, 15, 9, 21, 13],
    #[5, 6, 18, 6, 19, 15, 22],
    #[9, 17, 19, 13, 18, 22, 15],
    #[14, 13, 15, 17, 22, 18, 19],
    #[18, 10, 22, 10, 15, 19, 18],
    #[20, 20, 11, 5, 10, 10, 11],
    #[23, 21, 11, 9, 10, 10, 11],
    #[22, 22, 10, 18, 11, 11, 10],
    #[21, 23, 10, 14, 11, 11, 10],
    #[6, 6, 14, 6, 19, 15, 23],
    #[13, 13, 15, 17, 23, 14, 19],
    #[10, 17, 19, 13, 14, 23, 15],
    #[17, 10, 23, 10, 15, 19, 14],
    #[0, 6, 6, 20, 7, 6, 7],
    #[2, 13, 6, 23, 7, 6, 7],
    #[1, 17, 7, 22, 6, 7, 6],
    #[3, 10, 7, 21, 6, 7, 6],
    #[4, 6, 6, 7, 19, 13, 20],
    #[12, 13, 13, 19, 20, 6, 19],
    #[8, 17, 19, 15, 6, 20, 13],
    #[16, 10, 20, 11, 13, 19, 6],
    #[6, 6, 13, 7, 19, 13, 23],
    #[13, 13, 13, 19, 23, 13, 19],
    #[17, 10, 23, 11, 13, 19, 13],
    #[10, 17, 19, 15, 13, 23, 13],
    #[5, 7, 17, 6, 17, 15, 22],
    #[9, 19, 17, 13, 17, 22, 15],
    #[18, 11, 22, 10, 15, 17, 17],
    #[14, 15, 15, 17, 22, 17, 17],
    #[20, 20, 10, 6, 10, 11, 11],
    #[21, 23, 10, 13, 10, 11, 11],
    #[22, 22, 11, 17, 11, 10, 10],
    #[23, 21, 11, 10, 11, 10, 10],
    #[7, 7, 10, 6, 17, 15, 21],
    #[11, 19, 17, 13, 10, 21, 15],
    #[15, 15, 15, 17, 21, 10, 17],
    #[19, 11, 21, 10, 15, 17, 10],
    #[0, 7, 5, 20, 5, 6, 7],
    #[1, 19, 5, 22, 5, 7, 6],
    #[2, 15, 6, 23, 7, 5, 5],
    #[3, 11, 7, 21, 6, 5, 5],
    #[4, 5, 7, 7, 18, 13, 20],
    #[16, 9, 20, 11, 13, 18, 7],
    #[8, 18, 18, 15, 7, 20, 13],
    #[12, 14, 13, 19, 20, 7, 18],
    #[20, 20, 9, 7, 10, 9, 11],
    #[22, 22, 9, 19, 11, 9, 10],
    #[21, 23, 10, 15, 9, 11, 9],
    #[23, 21, 11, 11, 9, 10, 9],
    #[5, 5, 19, 6, 18, 15, 22],
    #[9, 18, 18, 13, 19, 22, 15],
    #[18, 9, 22, 10, 15, 18, 19],
    #[14, 14, 15, 17, 22, 19, 18],
    #[6, 6, 15, 5, 19, 14, 23],
    #[13, 13, 14, 18, 23, 15, 19],
    #[17, 10, 23, 9, 14, 19, 15],
    #[10, 17, 19, 14, 15, 23, 14],
    #[7, 7, 11, 5, 17, 14, 21],
    #[19, 11, 21, 9, 14, 17, 11],
    #[15, 15, 14, 18, 21, 11, 17],
    #[11, 19, 17, 14, 11, 21, 14]] : Array (Array (Fin 24))).getD a.val #[]).getD i.val 0
def inverseId (a : PermId) : PermId := (#[0, 1, 2, 3, 4, 20, 12, 16, 8, 10, 9, 11, 6, 13, 23, 19, 7, 17, 22, 15, 5, 21, 18, 14, 24, 27, 26, 25, 48, 144, 120, 96, 72, 75, 73, 74, 49, 145, 98, 122, 51, 121, 146, 99, 50, 97, 147, 123, 28, 36, 44, 40, 52, 100, 124, 148, 60, 104, 140, 164, 56, 132, 108, 156, 64, 128, 116, 160, 80, 88, 92, 84, 32, 34, 35, 33, 76, 77, 79, 78, 68, 152, 136, 112, 71, 154, 137, 115, 69, 153, 114, 138, 70, 155, 113, 139, 31, 45, 38, 43, 53, 101, 150, 126, 57, 133, 157, 109, 62, 107, 141, 167, 83, 94, 90, 87, 66, 131, 118, 163, 30, 41, 39, 47, 54, 125, 103, 151, 65, 129, 161, 117, 61, 105, 166, 142, 82, 86, 91, 95, 58, 110, 135, 159, 29, 37, 42, 46, 55, 149, 102, 127, 81, 89, 85, 93, 63, 106, 165, 143, 67, 130, 162, 119, 59, 158, 134, 111] : Array PermId).getD a.val 0
def inverseSmall (a : Fin 24) : Fin 24 := (#[0, 1, 2, 3, 4, 8, 12, 16, 5, 9, 14, 18, 6, 13, 10, 17, 7, 15, 11, 19, 20, 22, 21, 23] : Array (Fin 24)).getD a.val 0

private def rearrange {n : Nat} (f : Fin n → Fin n) (w : BitVec n) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn fun i => w.getLsbD (f i).val)).cast (by simp)

private theorem bit_rearrange {n : Nat} (f : Fin n → Fin n) (w : BitVec n) (i : Fin n) :
    (rearrange f w).getLsbD i.val = w.getLsbD (f i).val := by
  unfold rearrange
  rw [BitVec.getLsbD_cast]
  apply BitVec.getLsbD_ofBoolListLE.trans
  simp [List.getD_eq_getElem?_getD, i.isLt]

def ren (a : PermId) (w : G) := rearrange (edgeBack a) w
theorem ren_and (a : PermId) (x y : G) : ren a (x &&& y) = ren a x &&& ren a y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin 21 := ⟨i,hi⟩
  exact (bit_rearrange _ _ j).trans (by simp only [BitVec.getLsbD_and,ren,← bit_rearrange (edgeBack a) x j,← bit_rearrange (edgeBack a) y j]; rfl)
theorem ren_or (a : PermId) (x y : G) : ren a (x ||| y) = ren a x ||| ren a y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin 21 := ⟨i,hi⟩
  exact (bit_rearrange _ _ j).trans (by simp only [BitVec.getLsbD_or,ren,← bit_rearrange (edgeBack a) x j,← bit_rearrange (edgeBack a) y j]; rfl)

private theorem cancels {n : Nat} (f g : Fin n → Fin n) (h : ∀ i, f (g i) = i)
    (x : BitVec n) : rearrange g (rearrange f x) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin n := ⟨i,hi⟩
  exact (bit_rearrange _ _ j).trans ((bit_rearrange _ _ (g j)).trans (by rw [h j]))

theorem ren_injective (a : PermId) : Function.Injective (ren a) := by
  have h : ∀ (a : PermId) (i : Fin 21), edgeBack a (edgeBack (inverseId a) i) = i := by decide +kernel
  exact Function.LeftInverse.injective (cancels _ _ (h a))

theorem point_inverse : ∀ (a : PermId) (i : Fin 7), point a (point (inverseId a) i) = i := by decide +kernel
theorem ren_ins : ∀ a : PermId, ins.toFinset.image (ren a) = ins.toFinset := by decide +kernel
theorem ren_goal : ∀ a : PermId, goal.toFinset.image (ren a) = goal.toFinset := by decide +kernel

private theorem index_natural : ∀ (a : PermId) (p : Fin 7) (j : Fin 6),
    edgeBack a (index (point a p) j) = index p (smallBack (localId a p) j) := by decide +kernel

private theorem project_ren (a : PermId) (p : Fin 7) (x : G) :
    project (point a p) (ren a x) = rearrange (smallBack (localId a p)) (project p x) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  let j : Fin 6 := ⟨i,hi⟩
  rw [show i = j.val by rfl,bit_project,ren,bit_rearrange,bit_rearrange,bit_project,index_natural]

theorem ren_proj_card (a : PermId) (S : Finset G) (p : Fin 7) :
    (((S.image (ren a)).image (project (point a p))) \ Anchor1023.reserve).card =
      ((S.image (project p)) \ Anchor1023.reserve).card := by
  let f := rearrange (smallBack (localId a p))
  have hi : ∀ (q : Fin 24) (i : Fin 6), smallBack q (smallBack (inverseSmall q) i) = i := by decide +kernel
  have hf : Function.Injective f := Function.LeftInverse.injective (cancels _ _ (hi (localId a p)))
  have pres : ∀ (q : Fin 24) (v : BitVec 6), rearrange (smallBack q) v ∈ Anchor1023.reserve ↔ v ∈ Anchor1023.reserve := by decide +kernel
  have eq : ((S.image (ren a)).image (project (point a p))) \ Anchor1023.reserve =
      ((S.image (project p)) \ Anchor1023.reserve).image f := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨⟨_,⟨x,hx,rfl⟩,rfl⟩,hr⟩
      exact ⟨project p x,⟨⟨x,hx,rfl⟩,fun h => hr ((project_ren a p x) ▸ (pres _ _).mpr h)⟩,(project_ren a p x).symm⟩
    · rintro ⟨_,⟨⟨x,hx,rfl⟩,hr⟩,rfl⟩
      exact ⟨⟨ren a x,⟨x,hx,rfl⟩,project_ren a p x⟩,fun h => hr ((pres _ _).mp h)⟩
  rw [eq,Finset.card_image_of_injective _ hf]
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023

theorem ren_base : ∀ a : PermId, base.toFinset.image (ren a) = base.toFinset := by decide +kernel

private theorem image_mem_ren {f : G → G} (S : Finset G) (hinj : Function.Injective f) {u : G} :
    f u ∈ S.image f ↔ u ∈ S := by
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
    exact hinj he ▸ hv
  · exact Finset.mem_image_of_mem _

private theorem relmem {xs : List G} {f : G → G} (hinj : Function.Injective f)
    (he : xs.toFinset.image f = xs.toFinset) (u : G) : f u ∈ xs ↔ u ∈ xs := by
  change f u ∈ xs ↔ u ∈ xs
  simpa only [List.mem_toFinset] using
    (show f u ∈ xs.toFinset ↔ u ∈ xs.toFinset from by
      conv_lhs => rw [← he]
      exact image_mem_ren _ hinj)

private theorem ren_gate (a : PermId) {xs ys : List G} (ht : ∀ x ∈ xs, ren a x ∈ ys)
    {t : G} (h : gate xs t) : gate ys (ren a t) := by
  obtain ⟨x,hx,y,hy,he⟩ := h
  refine ⟨ren a x,ht x hx,ren a y,ht y hy,?_⟩
  rcases he with rfl|rfl
  · exact Or.inl (ren_and a x y)
  · exact Or.inr (ren_or a x y)

private theorem ren_fit (a : PermId) {S : Finset G} (h : fit S) : fit (S.image (ren a)) := by
  intro y hy
  have nd : goal.Nodup := by decide
  have ex : y ∈ goal.toFinset.image (ren a) := (ren_goal a).symm ▸ List.mem_toFinset.mpr hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ex
  refine ren_gate a ?_ (h x (List.mem_toFinset.mp hx))
  intro v hv
  simp only [List.mem_append,Finset.mem_toList,nd.mem_erase_iff] at hv ⊢
  rcases hv with hS | ⟨hne,hg⟩ | hb
  · exact Or.inl (Finset.mem_image_of_mem _ hS)
  · exact Or.inr (Or.inl ⟨fun e => hne ((ren_injective a) e), (relmem (ren_injective a) (ren_goal a) _).mpr hg⟩)
  · exact Or.inr (Or.inr ((relmem (ren_injective a) (ren_base a) _).mpr hb))

private theorem ren_extend (a : PermId) {S : Finset G} {v : G} (h : extend S v) :
    extend (S.image (ren a)) (ren a v) := by
  rcases h with ⟨hr, hs, hg⟩
  have hgmem := relmem (ren_injective a) (ren_goal a)
  have hbmem := relmem (ren_injective a) (ren_base a)
  refine ⟨?_,?_,ren_gate a ?_ hg⟩
  · simpa only [List.mem_append,hgmem,hbmem] using hr
  · simpa only [image_mem_ren _ (ren_injective a)] using hs
  · intro x hx
    simp only [List.mem_append, Finset.mem_toList, hgmem,hbmem,
      image_mem_ren _ (ren_injective a)] at hx ⊢
    exact hx

private theorem ren_quality (a : PermId) {S : Finset G} (h : quality S) : quality (S.image (ren a)) := by
  intro p
  let q := point (inverseId a) p
  have eq := ren_proj_card a S q
  change (seen (S.image (ren a)) (point a q)).card = (seen S q).card at eq
  rw [show point a q = p from point_inverse a p] at eq
  rw [eq, Finset.card_image_of_injective _ (ren_injective a)]
  exact h q

theorem ren_reach (a : PermId) (k : ℕ) (S : Finset G) (h : Reach k S) :
    Reach k (S.image (ren a)) := by
  induction k generalizing S with
  | zero => exact ren_fit a h
  | succ k ih =>
    rcases h with hf | ⟨v, hv, hq, hr⟩
    · exact Or.inl (ren_fit a hf)
    · exact Or.inr ⟨ren a v,ren_extend a hv,by simpa using ren_quality a hq,
        by simpa using ih (insert v S) hr⟩
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023

private def frozen (s : List G) : List (Fin 7 × Finset Anchor1023.W) :=
  (List.finRange 7).filterMap fun p =>
    let old := seen s.toFinset p
    if old.card + 2 ≤ s.toFinset.card then some (p,old ∪ Anchor1023.reserve) else none

private theorem frozen_fresh (s : List G) (v : G) (hn : v ∉ s.toFinset)
    (hq : quality (insert v s.toFinset)) (p : Fin 7) (T : Finset Anchor1023.W)
    (hh : (p,T) ∈ frozen s) : project p v ∉ T := by
  obtain ⟨p',_,hp⟩ := List.mem_filterMap.mp hh
  change (if (seen s.toFinset p').card + 2 ≤ s.toFinset.card then some (p',seen s.toFinset p' ∪ Anchor1023.reserve) else none) = some (p,T) at hp
  split at hp
  next hs =>
    cases hp
    intro h
    have eq : seen (insert v s.toFinset) p = seen s.toFinset p := by
      ext x
      simp only [seen,Finset.image_insert,Finset.mem_sdiff,Finset.mem_insert] at *
      grind
    have hk := hq p
    rw [eq,Finset.card_insert_of_notMem hn] at hk
    omega
  next => contradiction

end PEqualNP.Outside.Fano1023
namespace PEqualNP.Outside.Fano1023
private def sixNat (a b c d e f : Bool) : Nat :=
  a.toNat + 2*(b.toNat + 2*(c.toNat + 2*(d.toNat + 2*(e.toNat + 2*f.toNat))))

private def directProject (p : Fin 7) (x : G) : Nat :=
  match p.val with
  | 0 => sixNat (x.toNat.testBit 0) (x.toNat.testBit 1) (x.toNat.testBit 6) (x.toNat.testBit 10) (x.toNat.testBit 15) (x.toNat.testBit 3)
  | 1 => sixNat (x.toNat.testBit 0) (x.toNat.testBit 2) (x.toNat.testBit 16) (x.toNat.testBit 11) (x.toNat.testBit 7) (x.toNat.testBit 4)
  | 2 => sixNat (x.toNat.testBit 1) (x.toNat.testBit 2) (x.toNat.testBit 5) (x.toNat.testBit 12) (x.toNat.testBit 8) (x.toNat.testBit 17)
  | 3 => sixNat (x.toNat.testBit 3) (x.toNat.testBit 5) (x.toNat.testBit 18) (x.toNat.testBit 9) (x.toNat.testBit 13) (x.toNat.testBit 4)
  | 4 => sixNat (x.toNat.testBit 6) (x.toNat.testBit 7) (x.toNat.testBit 9) (x.toNat.testBit 19) (x.toNat.testBit 8) (x.toNat.testBit 14)
  | 5 => sixNat (x.toNat.testBit 10) (x.toNat.testBit 11) (x.toNat.testBit 13) (x.toNat.testBit 12) (x.toNat.testBit 20) (x.toNat.testBit 14)
  | _ => sixNat (x.toNat.testBit 15) (x.toNat.testBit 16) (x.toNat.testBit 18) (x.toNat.testBit 19) (x.toNat.testBit 20) (x.toNat.testBit 17)

private theorem directProject_eq (p : Fin 7) (x : G) : directProject p x = (project p x).toNat := by
  have h : ∀ (a b c d e f : Bool), sixNat a b c d e f =
      (BitVec.ofBoolListLE [a,b,c,d,e,f]).toNat := by decide
  fin_cases p <;> simp only [directProject,h] <;> rfl

private def packed : List Anchor1023.W → Nat
  | [] => 0
  | x :: xs => 2^x.toNat ||| packed xs
private theorem packed_mem (xs : List Anchor1023.W) (v : Anchor1023.W) :
    (packed xs).testBit v.toNat = true ↔ v ∈ xs := by
  induction xs with
  | nil => simp [packed]
  | cons x xs ih =>
    simp only [packed,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    rw [BitVec.toNat_inj,eq_comm (a := x)]

def blockedTable (s : List G) : List (Fin 7 × Nat) :=
  (List.finRange 7).filterMap fun p =>
    if (seen s.toFinset p).card + 2 ≤ s.toFinset.card then
      some (p,packed (s.map (project p) ++ (Anchor1023.targets ++ Anchor1023.base))) else none
def blocked (T : List (Fin 7 × Nat)) (v : G) : Bool :=
  T.any fun e => e.2.testBit (directProject e.1 v)
theorem blocked_false (s : List G) (v : G) (hn : v ∉ s.toFinset)
    (hq : quality (insert v s.toFinset)) : blocked (blockedTable s) v = false := by
  apply Bool.eq_false_iff.mpr
  intro H
  obtain ⟨e,he,hit⟩ := List.any_eq_true.mp H
  obtain ⟨p,hp,hpair⟩ := List.mem_filterMap.mp he
  split at hpair
  next hs =>
    cases hpair
    have hm : project p v ∈ s.map (project p) ++ (Anchor1023.targets ++ Anchor1023.base) :=
      (packed_mem ..).mp (by simpa only [directProject_eq] using hit)
    let U := seen s.toFinset p ∪ Anchor1023.reserve
    have hf : (p,U) ∈ frozen s := List.mem_filterMap.mpr ⟨p,hp,by simp [U,hs]⟩
    apply frozen_fresh s v hn hq p U hf
    rcases List.mem_append.mp hm with hi|hr
    · have hi' : project p v ∈ s.toFinset.image (project p) := by simpa using hi
      by_cases hz : project p v ∈ Anchor1023.reserve
      · exact Finset.mem_union_right _ hz
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi',hz⟩)
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hr)
  next => contradiction
end PEqualNP.Outside.Fano1023
namespace PEqualNP.Outside.Fano1023
def upperAll {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => true
  | x::xs => (x::xs).all (f x) && upperAll f xs

theorem upper_sound {α : Type} (f : α → α → Bool) (sym : ∀ a b, f a b=f b a)
    {s : List α} (h : upperAll f s) (a b : α) (ha : a ∈ s) (hb : b ∈ s) : f a b := by
  induction s with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hh,ht⟩ := Bool.and_eq_true_iff.mp h
    rcases List.mem_cons.mp ha with rfl|ha
    · exact List.all_eq_true.mp hh b hb
    rcases List.mem_cons.mp hb with rfl|hb
    · rw [sym]; exact List.all_eq_true.mp hh a (by assumption)
    · exact ih ht ha hb

def coveredFast (s allowed : List G) : Bool :=
  let bank := s ++ (goal ++ base)
  let table := blockedTable s
  let ok v := bank.contains v || allowed.contains v || blocked table v
  upperAll (fun a b => ok (a &&& b) && ok (a ||| b)) bank

theorem coveredFast_sound (s allowed : List G) (v : G) (h : coveredFast s allowed = true)
    (he : extend s.toFinset v) (hq : quality (insert v s.toFinset)) : v ∈ allowed := by
  obtain ⟨hn,hs,a,ha,b,hb,hv⟩ := he
  have mem (x : G) (hx : x ∈ s.toFinset.toList ++ (goal ++ base)) : x ∈ s ++ (goal ++ base) := by simpa using hx
  have h1 := upper_sound _ (fun x y => by simp [BitVec.and_comm x y,BitVec.or_comm x y]) h a b (mem a ha) (mem b hb)
  have hvb : v ∉ s ++ (goal ++ base) := by simpa using (show v ∉ s ∧ v ∉ goal ++ base by simpa using And.intro hs hn)
  have h2 := Bool.and_eq_true_iff.mp h1
  have h3 : ((s ++ (goal ++ base)).contains v || allowed.contains v || blocked (blockedTable s) v) = true := by
    rcases hv with rfl|rfl
    · exact h2.1
    · exact h2.2
  simpa [hvb,blocked_false s v hs hq] using h3

end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
abbrev Link := G × PermId × ℕ
def canB (v : G) (s : List G) : Bool :=
  s.any (fun a => s.any (fun b => (v == a &&& b) || (v == a ||| b)))
theorem canB_iff (v : G) (s : List G) : canB v s = true ↔ gate s v := by
  simp [canB,gate,List.any_eq_true]
def missing (s : List G) (t : G) :=
  goal.contains t && !canB t (s ++ (goal.erase t ++ base))
theorem missing_sound {s : List G} {t : G} (h : missing s t = true) : ¬fit s.toFinset := by
  simp only [missing,Bool.and_eq_true,List.contains_iff_mem,Bool.not_eq_true'] at h
  intro f
  obtain ⟨a,ha,b,hb,hab⟩ := f t h.1
  have mem (x : G) (hx : x ∈ s.toFinset.toList ++ (goal.erase t ++ base)) :
      x ∈ s ++ (goal.erase t ++ base) := by simpa using hx
  have z := (canB_iff t _).mpr ⟨a,mem a ha,b,mem b hb,hab⟩
  simp [h.2] at z

def eqset (l r : List G) : Bool := l.all r.contains && r.all l.contains
theorem eqset_sound {l r : List G} (h : eqset l r) : l.toFinset = r.toFinset := by
  simp [eqset,List.all_eq_true] at h
  ext x
  simpa using Iff.intro (h.1 x) (h.2 x)

def checkLinks (s : List G) (es : List Link) (next : Array (List G)) :=
  es.all fun ⟨v,pi,j⟩ => decide (j<next.size) &&
    eqset ((v::s).map (ren pi)) (next[j]?.getD [])

theorem transition {s : List G} {es : List Link} {next : Array (List G)} {k}
    (h : checkLinks s es next = true)
    (hn : ∀ j : Fin next.size, ¬Reach k (next[j.val]).toFinset)
    {v : G} (hv : v ∈ es.map Prod.fst) : ¬Reach k (insert v s.toFinset) := by
  obtain ⟨⟨v',pi,j⟩,hmem,rfl⟩ := List.mem_map.mp hv
  have e := List.all_eq_true.mp h _ hmem
  change (decide (j<next.size) && eqset ((v'::s).map (ren pi)) (next[j]?.getD [])) = true at e
  obtain ⟨hj,eq⟩ := Bool.and_eq_true_iff.mp e
  have hj' : j < next.size := of_decide_eq_true hj
  have hset := eqset_sound eq
  simp [hj'] at hset
  intro hr
  apply hn ⟨j,hj'⟩
  have hren := ren_reach pi k (insert v' s.toFinset) hr
  convert hren using 1
  have hmap : (s.map (ren pi)).toFinset = s.toFinset.image (ren pi) := by ext x; simp
  simpa [Finset.image_insert,hmap] using hset.symm

def rowCheck (s : List G) (t : G) (es : List Link) (next : Array (List G)) :=
   missing s t && coveredFast s (es.map Prod.fst) && checkLinks s es next
theorem row_sound {s : List G} {t : G} {es : List Link} {next : Array (List G)} {k}
    (h : rowCheck s t es next = true)
    (hn : ∀ j : Fin next.size, ¬Reach k (next[j.val]).toFinset) : ¬Reach (k+1) s.toFinset := by
  obtain ⟨hf,hl⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hm,hc⟩ := Bool.and_eq_true_iff.mp hf
  rintro (f|⟨v,he,hq,hr⟩)
  · exact missing_sound hm f
  · exact transition hl hn (coveredFast_sound s _ v hc he hq) hr
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
def rowAt (s : Array (List G)) (instructions : Array (G × List Link)) (next : Array (List G)) (i : ℕ) :=
  let q := instructions[i]?.getD (0,[])
  rowCheck (s[i]?.getD []) q.1 q.2 next
def bottomAt (s : Array (List G)) (instructions : Array G) (i : ℕ) :=
  missing (s[i]?.getD []) (instructions[i]?.getD 0)
def checkChunk (n : ℕ) (f : ℕ → Bool) (b : ℕ) :=
  (List.range 8).all fun j => decide (n ≤ 8*b+j) || f (8*b+j)
theorem checkedChunk {n : ℕ} {f : ℕ → Bool}
    (hc : ∀ b : Fin ((n+7)/8), checkChunk n f b.val) (i : Fin n) : f i.val := by
  have hi := i.isLt
  let b : Fin ((n+7)/8) := ⟨i.val/8,by omega⟩
  have h := List.all_eq_true.mp (hc b) (i.val%8) (List.mem_range.mpr (by omega))
  have eq : 8*b.val+i.val%8=i.val := by dsimp [b]; omega
  simpa [eq,not_le.mpr hi] using h

theorem nodeLayer {s : Array (List G)} {instructions : Array (G × List Link)} {next : Array (List G)} {k}
    (h : ∀ i : Fin s.size, rowAt s instructions next i.val)
    (hn : ∀ j : Fin next.size, ¬Reach k (next[j.val]).toFinset)
    (i : Fin s.size) : ¬Reach (k+1) (s[i.val]).toFinset := by
  have hi := h i
  simp only [rowAt,Array.getElem?_eq_getElem i.isLt,Option.getD_some] at hi
  exact row_sound hi hn
theorem bottomLayer {s : Array (List G)} {instructions : Array G}
    (h : ∀ i : Fin s.size, bottomAt s instructions i.val) (i : Fin s.size) : ¬Reach 0 (s[i.val]).toFinset := by
  have hi := h i
  simp only [bottomAt,Array.getElem?_eq_getElem i.isLt,Option.getD_some] at hi
  exact missing_sound hi
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
set_option maxRecDepth 200000
set_option maxHeartbeats 80000000
def L0 : Array (List G) := #[[]]
def L1 : Array (List G) := #[[1],[38],[44747],[101599],[507903],[1048575]]
def L2 : Array (List G) := #[[1,2],[1,8],[1,32],[1,38],[1,67],[1,560],[1,1034],[1,4096],[1,4354],[1,17152],[1,44747],[1,101599],[1,135463],[1,154422],[1,169327],[1,270905],[1,273982],[1,304763],[1,406334],[1,507903],[1,547779],[1,676838],[1,743573],[1,778239],[1,1014783],[1,1048575],[1,1211686],[1,1467192],[1,1474367],[1,1507199],[1,1572863],[1,1769455],[1,1835007],[1,1998846],[1,2031615],[1,2097135],[1,2097150],[38,67],[38,704],[38,2177],[38,4354],[38,33903],[38,44747],[38,68343],[38,101599],[38,154422],[38,169327],[38,507903],[38,540800],[38,541670],[38,547779],[38,575435],[38,609237],[38,676838],[38,743573],[38,778239],[38,913407],[38,1048575],[38,1605568],[38,1631176],[38,1638383],[38,1703903],[38,1769455],[38,1802231],[38,1835007],[38,1966079],[38,2064383],[38,2097099],[38,2097119],[38,2097135],[2614,68343],[44747,68343],[44747,101599],[44747,110303],[44747,154422],[44747,169327],[44747,180207],[44747,203191],[44747,338621],[44747,361583],[44747,507903],[44747,609237],[44747,725351],[44747,778239],[44747,786431],[44747,913407],[44747,1014783],[44747,1048575],[44747,1966079],[44747,2064383],[44747,2068774],[44747,2072063],[44747,2080751],[44747,2080767],[44747,2087927],[44747,2088959],[44747,2096127],[3,203191],[9,338621],[627,304763],[33903,169327],[101599,169327],[101599,237055],[101599,304763],[101599,406334],[101599,507903],[101599,778239],[101599,1014783],[101599,1048575],[101599,1211686],[101599,1507199],[101599,1572863],[101599,1769455],[101599,1835007],[101599,1998846],[101599,2031615],[101599,2097135],[101599,2097150],[75,1014783],[44783,1769455],[102143,778239],[507903,778239],[507903,913407],[507903,1048575],[507903,1703903],[507903,1769455],[507903,1835007],[507903,1966079],[507903,2064383],[507903,2097099],[507903,2097119],[507903,2097135],[1099,2064383],[110335,1835007],[372463,2097135],[1048575,1572863],[1048575,2031615],[1048575,2096639],[1048575,2096895]]
def L3 : Array (List G) := #[[1,101599,135463],[1,101599,270905],[1,101599,406334],[1,101599,676838],[1,101599,1211686],[1,101599,1474367],[1,101599,1998846],[1,101599,2097150],[1,169327,338621],[1,169327,609237],[1,169327,812024],[1,169327,1146005],[1,169327,1343032],[1,169327,1605568],[1,169327,2073144],[1,169327,2081728],[1,169327,2092029],[1,169327,2096128],[1,169327,2096829],[1,169327,2097109],[1,169327,2097144],[1,169327,2097149],[1,304763,676838],[1,304763,1211686],[1,304763,1605568],[1,304763,1802231],[1,304763,2097143],[1,406334,1605568],[1,406334,1703903],[1,406334,2081728],[1,406334,2097099],[1,406334,2097119],[1,507903,1605568],[1,507903,2081728],[1,676838,2096128],[1,676838,2096351],[1,676838,2096829],[1,676838,2096895],[1,1211686,2081728],[1,1211686,2091003],[1,1211686,2093055],[38,33903,338621],[38,101599,406334],[38,101599,541670],[38,101599,676838],[38,101599,812024],[38,101599,1080358],[38,101599,1211686],[38,101599,1343032],[38,101599,1605568],[38,101599,1998846],[38,101599,2081728],[38,101599,2089982],[38,101599,2094078],[38,101599,2097144],[38,101599,2097150],[38,169327,541670],[38,169327,609237],[38,169327,812024],[38,169327,1605568],[38,169327,2064422],[38,169327,2066581],[38,169327,2081728],[38,169327,2089982],[38,169327,2092029],[38,169327,2097109],[38,169327,2097149],[38,507903,541670],[38,507903,1605568],[38,575435,1146005],[38,575435,1211686],[38,575435,1343032],[38,575435,1540031],[38,575435,2066581],[38,575435,2068774],[38,575435,2096128],[38,575435,2096567],[38,575435,2096829],[38,575435,2096958],[38,575435,2097087],[38,609237,1211686],[38,609237,1343032],[38,609237,1507199],[38,609237,2096128],[38,609237,2096495],[38,609237,2097023],[38,676838,1441535],[38,676838,2096128],[38,676838,2096351],[38,676838,2096895],[38,778239,2096128],[38,913407,2096128],[38,1048575,2096128],[44747,101599,406334],[44747,101599,676838],[44747,101599,812024],[44747,101599,1211686],[44747,101599,1605568],[44747,101599,1998846],[44747,101599,2068774],[44747,101599,2094078],[44747,101599,2097150],[44747,110303,406334],[44747,110303,2068774],[44747,169327,338621],[44747,169327,609237],[44747,169327,812024],[44747,169327,2066581],[44747,169327,2092029],[44747,169327,2097149],[44747,180207,338621],[44747,180207,609237],[44747,180207,812024],[44747,180207,2066581],[44747,180207,2092029],[44747,180207,2097149],[44747,203191,812024],[44747,203191,1343032],[44747,203191,1605568],[44747,203191,1900539],[44747,203191,2073144],[44747,203191,2081728],[44747,203191,2091003],[44747,203191,2093051],[44747,203191,2097099],[44747,203191,2097144],[44747,203191,2097147],[44747,338621,1605568],[44747,338621,1769455],[44747,338621,2068774],[44747,338621,2080751],[44747,338621,2086895],[44747,338621,2097135],[44747,609237,1343032],[44747,609237,1507199],[44747,609237,1507327],[44747,609237,2068774],[44747,609237,2078591],[44747,609237,2080751],[44747,609237,2096958],[44747,609237,2097023],[44747,913407,2068774],[44747,1966079,2068774],[3,203191,270907],[3,203191,304763],[3,203191,541635],[3,203191,575435],[3,203191,812024],[3,203191,1080323],[3,203191,1113163],[3,203191,1343032],[3,203191,1605568],[3,203191,1900539],[3,203191,2073144],[3,203191,2089979],[3,203191,2091003],[3,203191,2097144],[3,203191,2097147],[9,135471,338621],[9,169327,338621],[9,338621,676838],[9,338621,1605568],[9,338621,1769455],[9,338621,2097135],[627,203191,304763],[627,304763,676838],[627,304763,1080947],[627,304763,1146005],[627,304763,1211686],[627,304763,1802231],[627,304763,2096128],[627,304763,2096567],[627,304763,2096887],[627,304763,2097143],[33903,169327,338621],[33903,169327,609237],[33903,169327,812024],[33903,169327,1605568],[33903,169327,2066581],[33903,169327,2081728],[33903,169327,2092029],[33903,169327,2097109],[33903,169327,2097149],[101599,169327,203191],[101599,169327,338621],[101599,169327,406334],[101599,169327,812024],[101599,169327,1014783],[101599,169327,1146005],[101599,169327,1343032],[101599,169327,1540031],[101599,169327,1605568],[101599,169327,1802231],[101599,169327,1998846],[101599,169327,2064383],[101599,169327,2073144],[101599,169327,2092029],[101599,169327,2096127],[101599,169327,2096829],[101599,169327,2097087],[101599,169327,2097144],[101599,169327,2097149],[101599,237055,406334],[101599,237055,676838],[101599,237055,812024],[101599,237055,1211686],[101599,237055,1343032],[101599,237055,1605568],[101599,237055,1998846],[101599,237055,2081728],[101599,237055,2094078],[101599,237055,2097144],[101599,237055,2097150],[101599,304763,338621],[101599,304763,676838],[101599,304763,1014783],[101599,304763,1605568],[101599,304763,1802231],[101599,304763,2064383],[101599,304763,2097143],[30,101599,406334],[101599,406334,507903],[101599,406334,778239],[101599,406334,913407],[101599,406334,1014783],[101599,406334,1048575],[101599,406334,1441535],[101599,406334,1507199],[101599,406334,1572863],[101599,406334,1605568],[101599,406334,1703903],[101599,406334,1769455],[101599,406334,1802231],[101599,406334,1835007],[101599,406334,1900539],[101599,406334,1966079],[101599,406334,1998846],[101599,406334,2031615],[101599,406334,2064383],[101599,406334,2081728],[101599,406334,2086895],[101599,406334,2088959],[101599,406334,2091003],[101599,406334,2093055],[101599,406334,2094078],[101599,406334,2095103],[101599,406334,2097099],[101599,406334,2097119],[101599,406334,2097135],[101599,406334,2097144],[101599,406334,2097147],[101599,406334,2097150],[101599,507903,1211686],[101599,507903,1998846],[101599,507903,2081728],[101599,507903,2094078],[101599,507903,2097144],[101599,507903,2097150],[101599,778239,1211686],[101599,778239,1998846],[101599,778239,2096958],[101599,778239,2097150],[101599,1014783,1211686],[101599,1014783,1507199],[101599,1014783,1769455],[101599,1014783,1900539],[101599,1014783,1998846],[101599,1014783,2031615],[101599,1014783,2096495],[101599,1014783,2096958],[101599,1014783,2097023],[101599,1014783,2097135],[101599,1014783,2097150],[101599,1048575,1211686],[101599,1048575,1998846],[101599,1048575,2096958],[101599,1048575,2097150],[360,169327,812024],[101599,1211686,1310207],[101599,1211686,1572863],[101599,1211686,1835007],[101599,1211686,2081728],[101599,1211686,2086895],[101599,1211686,2088959],[101599,1211686,2091003],[101599,1211686,2093055],[101599,1211686,2095103],[101599,1507199,1540031],[101599,1507199,1802231],[101599,1507199,1998846],[101599,1507199,2064383],[101599,1507199,2087927],[101599,1507199,2092029],[101599,1507199,2094078],[101599,1507199,2096127],[101599,1507199,2097143],[101599,1507199,2097150],[101599,1572863,1998846],[101599,1572863,2094078],[101599,1572863,2097150],[101599,1769455,1802231],[101599,1769455,1998846],[101599,1769455,2064383],[101599,1769455,2087927],[101599,1769455,2094078],[101599,1769455,2096127],[101599,1769455,2096567],[101599,1769455,2096958],[101599,1769455,2097087],[101599,1769455,2097143],[101599,1769455,2097144],[101599,1769455,2097149],[101599,1769455,2097150],[101599,1835007,1998846],[101599,1835007,2094078],[101599,1835007,2096958],[101599,1835007,2097150],[75,1014783,1113163],[3294,101599,1998846],[44783,338621,1769455],[101599,678902,1998846],[75,1014783,2096128],[44783,1769455,2066581],[101599,1471294,2094078],[101599,1998846,2031615],[101599,1998846,2094078],[101599,1998846,2095103],[101599,1998846,2096127],[101599,1998846,2096958],[101599,1998846,2097023],[101599,1998846,2097135],[101599,1998846,2097150],[101599,2031615,2064383],[101599,2031615,2096127],[101599,2031615,2097087],[101599,2031615,2097143],[101599,2031615,2097150],[101599,2097135,2097143],[101599,2097135,2097150],[1099,2064383,2065483],[101598,101599,2097150],[101599,372478,2097150],[101599,744438,2097150],[75,1014783,1080395],[507903,778239,2097144],[507903,1703903,1998846],[507903,1703903,2094078],[507903,1703903,2096958],[507903,1703903,2097150],[507903,1769455,2097149],[507903,1835007,2097144],[507903,2064383,2097099],[507903,2097119,2097150]]
def L4 : Array (List G) := #[[1,101599,406334,1605568],[1,101599,406334,2081728],[1,101599,676838,2096128],[1,101599,1211686,2081728],[1,169327,338621,1605568],[1,169327,338621,2081728],[1,169327,338621,2096128],[1,169327,609237,1343032],[1,169327,609237,2073144],[1,169327,609237,2096128],[1,169327,812024,1146005],[1,169327,812024,2096128],[1,169327,1146005,2073144],[1,169327,1146005,2081728],[1,169327,1343032,2081728],[1,169327,1605568,2073144],[1,304763,676838,2096128],[1,304763,1211686,2081728],[1,304763,1605568,2068774],[38,101599,406334,541670],[38,101599,406334,1080358],[38,101599,406334,1605568],[38,101599,406334,2081728],[38,101599,676838,1343032],[38,101599,676838,2073144],[38,101599,676838,2096128],[38,101599,812024,1211686],[38,101599,812024,2096128],[38,101599,1211686,2081728],[38,101599,1343032,2081728],[38,169327,609237,1343032],[38,169327,609237,2073144],[38,169327,609237,2096128],[38,169327,812024,1146005],[38,169327,812024,2066581],[38,169327,812024,2096128],[38,169327,1605568,2066581],[38,575435,1146005,2068774],[38,575435,1146005,2073144],[38,575435,1211686,2066581],[38,575435,1343032,2066581],[38,575435,1343032,2068774],[38,609237,1211686,2065483],[38,609237,1343032,2065483],[44747,101599,406334,1605568],[44747,101599,406334,2081728],[44747,101599,406334,2096128],[44747,101599,676838,1343032],[44747,101599,676838,2096128],[44747,101599,812024,1211686],[44747,101599,812024,2068774],[44747,101599,1211686,2081728],[44747,101599,1605568,2068774],[44747,169327,338621,1605568],[44747,169327,338621,2081728],[44747,169327,609237,1343032],[44747,169327,609237,2073144],[44747,169327,812024,1146005],[44747,169327,812024,2066581],[44747,180207,338621,1605568],[44747,180207,338621,2081728],[44747,180207,609237,1343032],[44747,180207,609237,2073144],[44747,180207,812024,1146005],[44747,180207,812024,2066581],[44747,203191,812024,2096128],[44747,203191,1605568,2073144],[44747,338621,1605568,2068774],[44747,338621,1605568,2080751],[44747,609237,1343032,2068774],[44747,609237,1343032,2080751],[3,203191,304763,1605568],[3,203191,304763,2081728],[3,203191,304763,2096128],[3,203191,575435,1343032],[3,203191,575435,2073144],[3,203191,812024,1113163],[3,203191,812024,2096128],[3,203191,1113163,2073144],[3,203191,1605568,2073144],[9,169327,338621,1605568],[9,169327,338621,2081728],[9,338621,676838,2096128],[9,338621,1605568,2068774],[627,203191,304763,1080947],[627,203191,304763,1605568],[627,203191,304763,2096128],[627,304763,676838,1080947],[627,304763,676838,1146005],[627,304763,676838,2096128],[627,304763,676838,2096887],[627,304763,1146005,2068774],[627,304763,1211686,2081728],[33903,169327,338621,1605568],[33903,169327,338621,2081728],[33903,169327,609237,1343032],[33903,169327,609237,2073144],[33903,169327,609237,2096128],[33903,169327,812024,1146005],[33903,169327,812024,2066581],[33903,169327,812024,2096128],[33903,169327,1605568,2066581],[101599,169327,203191,812024],[101599,169327,203191,1343032],[101599,169327,203191,2097144],[101599,169327,338621,406334],[101599,169327,338621,676838],[101599,169327,338621,812024],[101599,169327,338621,1211686],[101599,169327,338621,1343032],[101599,169327,338621,1605568],[101599,169327,338621,1998846],[101599,169327,338621,2068774],[101599,169327,338621,2081728],[101599,169327,338621,2094078],[101599,169327,338621,2096128],[101599,169327,338621,2096958],[101599,169327,338621,2097144],[101599,169327,338621,2097150],[101599,169327,406334,609237],[101599,169327,406334,812024],[101599,169327,406334,1146005],[101599,169327,406334,1605568],[101599,169327,406334,2066581],[101599,169327,406334,2081728],[101599,169327,406334,2092029],[101599,169327,406334,2096128],[101599,169327,406334,2096829],[101599,169327,406334,2097109],[101599,169327,406334,2097144],[101599,169327,406334,2097149],[101599,169327,812024,879613],[101599,169327,812024,947198],[101599,169327,812024,1014783],[101599,169327,812024,1146005],[101599,169327,812024,1211686],[101599,169327,812024,1343032],[101599,169327,812024,1540031],[101599,169327,812024,1802231],[101599,169327,812024,1867768],[101599,169327,812024,1998846],[101599,169327,812024,2064383],[101599,169327,812024,2073144],[101599,169327,812024,2081728],[101599,169327,812024,2087927],[101599,169327,812024,2092029],[101599,169327,812024,2094078],[101599,169327,812024,2096127],[101599,169327,812024,2096128],[101599,169327,812024,2096567],[101599,169327,812024,2096829],[101599,169327,812024,2096958],[101599,169327,812024,2097087],[101599,169327,812024,2097109],[101599,169327,812024,2097143],[101599,169327,812024,2097144],[101599,169327,812024,2097149],[101599,169327,812024,2097150],[101599,169327,1014783,1343032],[101599,169327,1014783,1605568],[101599,169327,1014783,2073144],[101599,169327,1014783,2096128],[101599,169327,1014783,2097144],[101599,169327,1146005,1211686],[101599,169327,1146005,1998846],[101599,169327,1146005,2073144],[101599,169327,1146005,2094078],[101599,169327,1146005,2096958],[101599,169327,1146005,2097150],[101599,169327,1343032,1408701],[101599,169327,1343032,1540031],[101599,169327,1343032,1605568],[101599,169327,1343032,1802231],[101599,169327,1343032,1867768],[101599,169327,1343032,1998846],[101599,169327,1343032,2064383],[101599,169327,1343032,2092029],[101599,169327,1343032,2094078],[101599,169327,1343032,2096127],[101599,169327,1343032,2096128],[101599,169327,1343032,2096567],[101599,169327,1343032,2096696],[101599,169327,1343032,2096829],[101599,169327,1343032,2096958],[101599,169327,1343032,2097087],[101599,169327,1343032,2097109],[101599,169327,1343032,2097143],[101599,169327,1343032,2097144],[101599,169327,1343032,2097149],[101599,169327,1343032,2097150],[101599,169327,1540031,1605568],[101599,169327,1540031,2073144],[101599,169327,1540031,2097144],[101599,169327,1605568,1671125],[101599,169327,1605568,1802231],[101599,169327,1605568,1867768],[101599,169327,1605568,1998846],[101599,169327,1605568,2064383],[101599,169327,1605568,2073144],[101599,169327,1605568,2092029],[101599,169327,1605568,2096127],[101599,169327,1605568,2096829],[101599,169327,1605568,2097087],[101599,169327,1605568,2097144],[101599,169327,1605568,2097149],[101599,169327,1802231,2073144],[101599,169327,1802231,2097144],[101599,169327,1998846,2073144],[101599,169327,1998846,2092029],[101599,169327,1998846,2096829],[101599,169327,1998846,2097109],[101599,169327,1998846,2097144],[101599,169327,1998846,2097149],[101599,169327,2064383,2073144],[101599,169327,2064383,2097144],[101599,169327,2073144,2075325],[101599,169327,2073144,2092029],[101599,169327,2073144,2096127],[101599,169327,2073144,2096696],[101599,169327,2073144,2096829],[101599,169327,2073144,2097087],[101599,169327,2073144,2097144],[101599,169327,2073144,2097149],[101599,169327,2092029,2094078],[101599,169327,2092029,2096958],[101599,169327,2092029,2097144],[101599,169327,2092029,2097150],[101599,169327,2096127,2097144],[101599,169327,2096829,2096958],[101599,169327,2096829,2097144],[101599,169327,2096829,2097150],[101599,169327,2097087,2097144],[101599,169327,1474360,2097144],[101599,169327,2097144,2097149],[101599,169327,2097149,2097150],[101599,237055,406334,1343032],[101599,237055,406334,1605568],[101599,237055,406334,2081728],[101599,237055,406334,2097144],[101599,237055,676838,1343032],[101599,237055,676838,2073144],[101599,237055,676838,2096128],[101599,237055,676838,2097144],[101599,237055,812024,947198],[101599,237055,812024,1211686],[101599,237055,812024,1867768],[101599,237055,812024,1998846],[101599,237055,812024,2073144],[101599,237055,812024,2081728],[101599,237055,812024,2094078],[101599,237055,812024,2096128],[101599,237055,812024,2096958],[101599,237055,812024,2097144],[101599,237055,812024,2097150],[101599,237055,1211686,1343032],[101599,237055,1211686,2081728],[101599,237055,1211686,2097144],[101599,237055,1343032,1867768],[101599,237055,1343032,1998846],[101599,237055,1343032,2081728],[101599,237055,1343032,2094078],[101599,237055,1343032,2097144],[101599,237055,1343032,2097150],[101599,237055,1605568,1998846],[101599,237055,1605568,2094078],[101599,237055,1605568,2096958],[101599,237055,1605568,2097144],[101599,237055,1605568,2097150],[101599,237055,1998846,2081728],[101599,237055,1998846,2097144],[101599,237055,2081728,2085862],[101599,237055,2081728,2094078],[101599,237055,2081728,2097088],[101599,237055,2081728,2097144],[101599,237055,2081728,2097150],[101599,237055,2094078,2097144],[101599,237055,1474360,2097144],[101599,237055,2097144,2097150],[101599,304763,338621,676838],[101599,304763,676838,1014783],[101599,304763,676838,1540031],[101599,304763,676838,1802231],[101599,304763,676838,1998846],[101599,304763,676838,2064383],[101599,304763,676838,2096128],[101599,304763,676838,2096567],[101599,304763,676838,2096829],[101599,304763,676838,2096958],[101599,304763,676838,2097087],[101599,304763,676838,2097143],[101599,304763,676838,2097150],[101599,304763,1014783,1605568],[101599,304763,1605568,1802231],[101599,304763,1605568,2064383],[101599,304763,1605568,2068774],[101599,304763,1605568,2087927],[101599,304763,1605568,2096127],[101599,304763,1605568,2097143],[101599,304763,1802231,1998846],[101599,304763,1802231,2094078],[101599,304763,1802231,2097144],[101599,304763,1802231,2097150],[101599,304763,2097143,2097150],[30,101599,406334,541662],[30,101599,406334,1605568],[30,101599,406334,2081728],[101599,406334,507903,1605568],[101599,406334,507903,2081728],[101599,406334,778239,1605568],[101599,406334,778239,2081728],[101599,406334,778239,2096128],[101599,406334,778239,2097144],[101599,406334,913407,1605568],[101599,406334,913407,2081728],[101599,406334,913407,2096128],[101599,406334,1014783,2081728],[101599,406334,1014783,2096128],[101599,406334,1014783,2097099],[101599,406334,1048575,1605568],[101599,406334,1048575,2081728],[101599,406334,1048575,2096128],[101599,406334,1441535,1605568],[101599,406334,1441535,2081728],[101599,406334,1507199,2081728],[101599,406334,1507199,2097109],[101599,406334,1572863,1605568],[101599,406334,1572863,2081728],[101599,406334,1605568,2086895],[101599,406334,1605568,2087927],[101599,406334,1605568,2088959],[101599,406334,1605568,2091003],[101599,406334,1605568,2093055],[101599,406334,1605568,2095103],[101599,406334,1605568,2096895],[101599,406334,1703903,1998846],[101599,406334,1703903,2081728],[101599,406334,1703903,2094078],[101599,406334,1703903,2096958],[101599,406334,1703903,2097144],[101599,406334,1703903,2097150],[101599,406334,1769455,2081728],[101599,406334,1769455,2092029],[101599,406334,1769455,2096829],[101599,406334,1769455,2097109],[101599,406334,1769455,2097144],[101599,406334,1769455,2097149],[101599,406334,1802231,1900539],[101599,406334,1802231,2081728],[101599,406334,1802231,2091003],[101599,406334,1802231,2097099],[101599,406334,1802231,2097144],[101599,406334,1802231,2097147],[101599,406334,1835007,2081728],[101599,406334,1835007,2097144],[101599,406334,1900539,2081728],[101599,406334,1900539,2087927],[101599,406334,1900539,2097109],[101599,406334,1900539,2097143],[101599,406334,1966079,2081728],[101599,406334,1998846,2097099],[101599,406334,1998846,2097109],[101599,406334,1998846,2097119],[101599,406334,2031615,2081728],[101599,406334,2031615,2097109],[101599,406334,2064383,2081728],[101599,406334,2064383,2097099],[360,169327,812024,2066581],[101599,406334,2081728,2084831],[101599,406334,2081728,2088959],[101599,406334,2081728,2093055],[101599,406334,2081728,2097119],[101599,406334,2086895,2092029],[101599,406334,2086895,2097109],[101599,406334,2086895,2097144],[101599,406334,2086895,2097149],[101599,406334,2088959,2097144],[101599,406334,2091003,2097109],[101599,406334,2091003,2097143],[101599,406334,2094078,2097099],[101599,406334,2094078,2097119],[101599,406334,2095103,2097109],[101599,406334,2097099,2097109],[101599,406334,2097099,2097143],[101599,406334,2097099,2097144],[101599,406334,2097099,2097149],[101599,406334,2097099,2097150],[101599,406334,2097119,2097144],[101599,406334,2097119,2097150],[101599,406334,2097135,2097144],[101599,406334,2097135,2097149],[101599,507903,1211686,2081728],[101599,507903,1211686,2097144],[101599,507903,1998846,2081728],[101599,507903,2081728,2094078],[101599,507903,2081728,2097144],[101599,507903,2081728,2097150],[101599,778239,1211686,2081728],[101599,778239,1211686,2097144],[101599,778239,2096958,2097144],[101599,1014783,1211686,1900539],[101599,1014783,1211686,2081728],[101599,1014783,1211686,2091003],[101599,1014783,1211686,2097099],[101599,1014783,1211686,2097147],[101599,1014783,2096495,2097144],[101599,1048575,1211686,2081728],[101599,1048575,1211686,2097144],[360,68093,169327,812024],[360,169327,812024,1146005],[360,169327,812024,2096637],[101599,1211686,1310207,2081728],[101599,1211686,1572863,2081728],[101599,1211686,1835007,2081728],[101599,1211686,2086895,2092029],[101599,1211686,2086895,2097109],[101599,1211686,2086895,2097149],[101599,1211686,2088959,2097144],[101599,1211686,2091003,2092029],[101599,1211686,2091003,2094078],[101599,1211686,2091003,2096127],[101599,1211686,2091003,2097150],[101599,1211686,2093055,2097150],[101599,1211686,2095103,2097149],[101599,1507199,2087927,2097144],[3294,101599,1998846,2067678]]
def L5 : Array (List G) := #[[101599,169327,203191,812024,1343032],[101599,169327,203191,812024,1867768],[101599,169327,203191,812024,2073144],[101599,169327,203191,812024,2096128],[101599,169327,203191,812024,2097144],[101599,169327,203191,1343032,1605568],[101599,169327,203191,1343032,1867768],[101599,169327,203191,1343032,2097144],[101599,169327,338621,406334,1605568],[101599,169327,338621,406334,2096128],[101599,169327,338621,676838,812024],[101599,169327,338621,676838,1343032],[101599,169327,338621,676838,1605568],[101599,169327,338621,676838,2073144],[101599,169327,338621,676838,2081728],[101599,169327,338621,676838,2096128],[101599,169327,338621,676838,2097144],[101599,169327,338621,812024,1211686],[101599,169327,338621,812024,2068774],[101599,169327,338621,812024,2096128],[101599,169327,338621,1211686,1343032],[101599,169327,338621,1211686,1605568],[101599,169327,338621,1211686,2073144],[101599,169327,338621,1211686,2081728],[101599,169327,338621,1211686,2096128],[101599,169327,338621,1211686,2097144],[101599,169327,338621,1343032,2068774],[101599,169327,338621,1343032,2081728],[101599,169327,338621,1605568,1736678],[101599,169327,338621,1605568,1867768],[101599,169327,338621,1605568,1998846],[101599,169327,338621,1605568,2068774],[101599,169327,338621,1605568,2081728],[101599,169327,338621,1605568,2094078],[101599,169327,338621,1605568,2096128],[101599,169327,338621,1605568,2096958],[101599,169327,338621,1605568,2097088],[101599,169327,338621,1605568,2097144],[101599,169327,338621,1605568,2097150],[101599,169327,338621,1998846,2081728],[101599,169327,338621,1998846,2096128],[101599,169327,338621,2068774,2097144],[101599,169327,338621,2081728,2085862],[101599,169327,338621,2081728,2094078],[101599,169327,338621,2081728,2096128],[101599,169327,338621,2081728,2096958],[101599,169327,338621,2081728,2097088],[101599,169327,338621,2081728,2097144],[101599,169327,338621,2081728,2097150],[101599,169327,338621,2094078,2096128],[101599,169327,338621,2096128,2096422],[101599,169327,338621,2096128,2096696],[101599,169327,338621,2096128,2096958],[101599,169327,338621,2096128,2097088],[101599,169327,338621,2096128,2097144],[101599,169327,338621,2096128,2097150],[101599,169327,406334,609237,812024],[101599,169327,406334,609237,1605568],[101599,169327,406334,609237,2081728],[101599,169327,406334,609237,2096128],[101599,169327,406334,609237,2097144],[101599,169327,406334,812024,1146005],[101599,169327,406334,812024,1605568],[101599,169327,406334,812024,2066581],[101599,169327,406334,812024,2096128],[101599,169327,406334,812024,2097109],[101599,169327,406334,1146005,2081728],[101599,169327,406334,1146005,2097144],[101599,169327,406334,1605568,1671125],[101599,169327,406334,1605568,1867768],[101599,169327,406334,1605568,2066581],[101599,169327,406334,1605568,2081728],[101599,169327,406334,1605568,2092029],[101599,169327,406334,1605568,2096128],[101599,169327,406334,1605568,2096829],[101599,169327,406334,1605568,2097088],[101599,169327,406334,1605568,2097109],[101599,169327,406334,1605568,2097144],[101599,169327,406334,1605568,2097149],[101599,169327,406334,2066581,2097144],[101599,169327,406334,2081728,2083797],[101599,169327,406334,2081728,2092029],[101599,169327,406334,2081728,2096128],[101599,169327,406334,2081728,2096829],[101599,169327,406334,2081728,2097088],[101599,169327,406334,2081728,2097109],[101599,169327,406334,2081728,2097144],[101599,169327,406334,2081728,2097149],[101599,169327,406334,2092029,2096128],[101599,169327,406334,2096128,2096696],[101599,169327,406334,2096128,2096829],[101599,169327,406334,2096128,2097088],[101599,169327,406334,2096128,2097109],[101599,169327,406334,2096128,2097144],[101599,169327,406334,2096128,2097149],[101599,169327,406334,2097109,2097144],[101599,169327,812024,879613,1211686],[101599,169327,812024,879613,2096128],[101599,169327,812024,947198,1146005],[101599,169327,812024,947198,2096128],[101599,169327,812024,1014783,2096128],[101599,169327,812024,1146005,1211686],[101599,169327,812024,1146005,1998846],[101599,169327,812024,1146005,2073144],[101599,169327,812024,1146005,2081728],[101599,169327,812024,1146005,2094078],[101599,169327,812024,1146005,2096958],[101599,169327,812024,1146005,2097150],[101599,169327,812024,1211686,2073144],[101599,169327,812024,1211686,2092029],[101599,169327,812024,1211686,2096829],[101599,169327,812024,1211686,2097109],[101599,169327,812024,1211686,2097149],[101599,169327,812024,1343032,1802231],[101599,169327,812024,1343032,2087927],[101599,169327,812024,1343032,2096567],[101599,169327,812024,1343032,2097109],[101599,169327,812024,1343032,2097143],[101599,169327,812024,1540031,2081728],[101599,169327,812024,1540031,2096128],[101599,169327,812024,1802231,2073144],[101599,169327,812024,1802231,2096128],[101599,169327,812024,1867768,2096128],[101599,169327,812024,1867768,2096567],[101599,169327,812024,1998846,2096128],[101599,169327,812024,2064383,2096128],[101599,169327,812024,2073144,2081728],[101599,169327,812024,2073144,2087927],[101599,169327,812024,2073144,2096567],[101599,169327,812024,2073144,2097109],[101599,169327,812024,2073144,2097143],[101599,169327,812024,2081728,2096829],[101599,169327,812024,2081728,2097087],[101599,169327,812024,2087927,2096128],[101599,169327,812024,2092029,2096128],[101599,169327,812024,2094078,2096128],[101599,169327,812024,2096127,2096128],[101599,169327,812024,2096128,2096422],[101599,169327,812024,2096128,2096567],[101599,169327,812024,2096128,2096696],[101599,169327,812024,2096128,2096829],[101599,169327,812024,2096128,2096958],[101599,169327,812024,2096128,2097087],[101599,169327,812024,2096128,2097088],[101599,169327,812024,2096128,2097109],[101599,169327,812024,2096128,2097143],[101599,169327,812024,2096128,2097144],[101599,169327,812024,2096128,2097149],[101599,169327,812024,2096128,2097150],[101599,169327,812024,2096567,2097144],[101599,169327,812024,2096958,2097109],[101599,169327,1014783,1343032,1605568],[101599,169327,1014783,1343032,2096128],[101599,169327,1014783,1605568,2073144],[101599,169327,1014783,1605568,2096128],[101599,169327,1014783,2073144,2096128],[101599,169327,1014783,2096128,2096696],[101599,169327,1014783,2096128,2097088],[101599,169327,1014783,2096128,2097144],[101599,169327,1146005,1211686,2073144],[101599,169327,1146005,1998846,2073144],[101599,169327,1146005,2073144,2077502],[101599,169327,1146005,2073144,2094078],[101599,169327,1146005,2073144,2096958],[101599,169327,1146005,2073144,2097150],[101599,169327,1146005,2094078,2097144],[101599,169327,1343032,1605568,2092029],[101599,169327,1343032,1605568,2096127],[101599,169327,1343032,2094078,2097109],[101599,169327,1343032,2096127,2096128],[101599,169327,1540031,1605568,2073144],[101599,169327,1605568,1671125,2073144],[101599,169327,1605568,1802231,2073144],[101599,169327,1605568,1867768,2073144],[101599,169327,1605568,1998846,2073144],[101599,169327,1605568,2064383,2073144],[101599,169327,1605568,2073144,2075325],[101599,169327,1605568,2073144,2092029],[101599,169327,1605568,2073144,2096127],[101599,169327,1605568,2073144,2096696],[101599,169327,1605568,2073144,2096829],[101599,169327,1605568,2073144,2097087],[101599,169327,1605568,2073144,2097144],[101599,169327,1605568,2073144,2097149],[101599,169327,1605568,2092029,2096958],[101599,169327,1802231,2073144,2096696],[101599,169327,1802231,2073144,2097144],[101599,169327,1998846,2073144,2097109],[101599,237055,406334,1343032,2081728],[101599,237055,406334,1605568,1867768],[101599,237055,406334,1605568,2097088],[101599,237055,406334,1605568,2097144],[101599,237055,406334,2081728,2097088],[101599,237055,406334,2081728,2097144],[101599,237055,676838,1343032,2096696],[101599,237055,676838,1343032,2097144],[101599,237055,676838,2073144,2096696],[101599,237055,676838,2073144,2097144],[101599,237055,676838,2096128,2096696],[101599,237055,676838,2096128,2097088],[101599,237055,676838,2096128,2097144],[101599,237055,812024,947198,2096128],[101599,237055,812024,1211686,2073144],[101599,237055,812024,1211686,2081728],[101599,237055,812024,1211686,2097144],[101599,237055,812024,1998846,2096128],[101599,237055,812024,2073144,2081728],[101599,237055,812024,2081728,2096958],[101599,237055,812024,2094078,2096128],[101599,237055,812024,2096128,2096958],[101599,237055,812024,2096128,2097144],[101599,237055,812024,2096128,2097150],[101599,237055,1211686,1343032,2081728],[101599,237055,1211686,2081728,2097088],[101599,237055,1211686,2081728,2097144],[101599,237055,1343032,1998846,2081728],[101599,237055,1343032,2081728,2085862],[101599,237055,1343032,2081728,2094078],[101599,237055,1343032,2081728,2097144],[101599,237055,1343032,2081728,2097150],[101599,304763,338621,676838,2096128],[101599,304763,676838,1014783,2096128],[101599,304763,676838,1540031,2096128],[101599,304763,676838,1802231,2096128],[101599,304763,676838,1998846,2096128],[101599,304763,676838,2064383,2096128],[101599,304763,676838,2096128,2097126],[101599,304763,676838,2096128,2097143],[101599,304763,676838,2096128,2097150],[101599,304763,676838,2096567,2097144],[101599,304763,1014783,1605568,2068774],[101599,304763,1605568,1802231,2068774],[101599,304763,1605568,2064383,2068774],[101599,304763,1605568,2068774,2097126],[101599,304763,1605568,2068774,2097143],[101599,304763,1605568,2087927,2096958],[101599,406334,778239,2096128,2097144],[101599,406334,1507199,2081728,2097109],[101599,406334,1605568,2086895,2096829],[101599,406334,1769455,2081728,2096829],[101599,507903,1211686,2081728,2097144]]
def L6 : Array (List G) := #[[101599,169327,203191,812024,1343032,1605568],[101599,169327,203191,812024,1343032,2081728],[101599,169327,203191,812024,1343032,2096128],[101599,169327,203191,812024,1867768,2096128],[101599,169327,203191,812024,2073144,2081728],[101599,169327,203191,812024,2096128,2096696],[101599,169327,203191,812024,2096128,2097144],[101599,169327,338621,406334,1605568,2081728],[101599,169327,338621,406334,1605568,2096128],[101599,169327,338621,406334,1605568,2097088],[101599,169327,338621,406334,2096128,2097088],[101599,169327,338621,676838,812024,2096128],[101599,169327,338621,676838,1343032,1605568],[101599,169327,338621,676838,1343032,2081728],[101599,169327,338621,676838,1343032,2096128],[101599,169327,338621,676838,1605568,2073144],[101599,169327,338621,676838,1605568,2096128],[101599,169327,338621,676838,2073144,2081728],[101599,169327,338621,676838,2081728,2096128],[101599,169327,338621,676838,2096128,2096696],[101599,169327,338621,676838,2096128,2097088],[101599,169327,338621,676838,2096128,2097144],[101599,169327,338621,812024,1211686,1605568],[101599,169327,338621,812024,1211686,2081728],[101599,169327,338621,812024,1211686,2096128],[101599,169327,338621,812024,2068774,2081728],[101599,169327,338621,812024,2068774,2096128],[101599,169327,338621,812024,2096128,2096422],[101599,169327,338621,1211686,1343032,2081728],[101599,169327,338621,1211686,1605568,2073144],[101599,169327,338621,1211686,1605568,2081728],[101599,169327,338621,1211686,2073144,2081728],[101599,169327,338621,1211686,2081728,2096128],[101599,169327,338621,1211686,2081728,2097088],[101599,169327,338621,1211686,2081728,2097144],[101599,169327,338621,1343032,2081728,2085862],[101599,169327,338621,1343032,2081728,2097088],[101599,169327,338621,1605568,1867768,2068774],[101599,169327,338621,1605568,2068774,2097144],[101599,169327,338621,1605568,2081728,2096958],[101599,169327,338621,1605568,2094078,2096128],[101599,169327,338621,1998846,2081728,2096128],[101599,169327,406334,609237,812024,2096128],[101599,169327,406334,609237,1605568,2073144],[101599,169327,406334,609237,2081728,2096128],[101599,169327,406334,609237,2096128,2096696],[101599,169327,406334,609237,2096128,2097088],[101599,169327,406334,609237,2096128,2097144],[101599,169327,406334,812024,1146005,1605568],[101599,169327,406334,812024,1605568,2066581],[101599,169327,406334,812024,2096128,2097088],[101599,169327,406334,812024,2096128,2097109],[101599,169327,406334,1146005,2081728,2097088],[101599,169327,406334,1146005,2081728,2097144],[101599,169327,406334,1605568,1867768,2066581],[101599,169327,406334,1605568,2066581,2097144],[101599,169327,406334,1605568,2081728,2096829],[101599,169327,406334,1605568,2092029,2096128],[101599,169327,812024,879613,2096128,2096422],[101599,169327,812024,1146005,1211686,2073144],[101599,169327,812024,1146005,1211686,2081728],[101599,169327,812024,1146005,2073144,2081728],[101599,169327,812024,1146005,2081728,2096958],[101599,169327,812024,1211686,2073144,2097109],[101599,169327,1605568,1671125,2073144,2077502],[101599,237055,406334,1343032,2081728,2097088],[101599,237055,812024,1211686,2073144,2081728],[101599,304763,338621,676838,2096128,2097126]]
def E0 : Array (G × List Link) := #[(372479,[(1,0,0),(2,4,0),(4,48,0),(8,8,0),(16,72,0),(32,60,0),(38,0,1),(64,6,0),(67,48,1),(128,49,0),(256,56,0),(512,62,0),(560,100,1),(704,1,1),(1024,7,0),(1034,60,1),(2048,51,0),(2068,104,1),(2177,6,1),(4096,64,0),(4354,13,1),(8192,61,0),(8712,22,1),(11264,2,1),(16384,82,0),(17152,114,1),(22528,98,1),(32768,5,0),(32840,62,1),(33793,50,1),(44747,0,2),(65536,50,0),(65541,4,1),(65680,106,1),(68343,25,2),(101599,0,3),(131072,80,0),(131360,113,1),(135172,97,1),(154422,52,2),(169327,4,3),(203191,48,3),(262144,63,0),(262184,20,1),(270352,102,1),(273982,33,2),(304763,8,3),(338621,72,3),(360448,3,1),(361583,1,2),(369400,32,2),(371861,24,2),(406334,60,3),(507903,0,4),(524288,66,0),(524608,12,1),(540800,99,1),(547779,38,2),(575435,6,3),(609237,49,3),(676838,56,3),(720896,96,1),(725351,36,2),(738288,53,2),(743573,48,2),(778239,48,4),(812024,62,3),(913407,1,4),(1014783,100,4),(1048575,0,5),(1048576,58,0),(1053696,14,1),(1073152,115,1),(1081098,30,2),(1113163,7,3),(1146005,51,3),(1211686,64,3),(1343032,61,3),(1441535,2,4),(1441792,112,1),(1447214,28,2),(1467192,68,2),(1473556,54,2),(1507199,60,4),(1540031,104,4),(1572863,8,5),(1605568,82,3),(1605632,15,1),(1611083,4,2),(1631176,31,2),(1637505,39,2),(1703903,6,4),(1769455,13,4),(1802231,98,4),(1835007,6,5),(1900539,22,4),(1966079,26,5),(1998846,114,4),(2031615,17,5),(2064383,120,5),(2064744,29,2),(2065483,5,3),(2066581,50,3),(2068774,80,3),(2069509,37,2),(2072063,4,4),(2073144,63,3),(2076415,3,4),(2078591,20,4),(2080767,24,5),(2081728,66,3),(2086895,12,4),(2087927,96,4),(2088959,4,5),(2089104,55,2),(2091003,62,4),(2092029,106,4),(2093055,10,5),(2094078,113,4),(2095103,18,5),(2096127,122,5),(2096128,58,3),(2096351,50,4),(2096495,14,4),(2096567,97,4),(2096639,5,5),(2096829,102,4),(2096895,2,5),(2096958,112,4),(2097023,16,5),(2097087,121,5),(2097099,15,4),(2097109,99,4),(2097119,7,5),(2097135,40,5),(2097143,124,5),(2097144,115,4),(2097147,19,5),(2097149,123,5),(2097150,140,5)])]
def F0 : ℕ → Bool := rowAt L0 E0 L1
def E1 : Array (G × List Link) := #[(372479,[(2,0,0),(4,24,0),(8,0,1),(16,24,1),(32,0,2),(38,0,3),(64,1,0),(67,0,4),(128,27,0),(256,56,2),(512,1,2),(560,0,5),(704,1,3),(1024,2,0),(1034,0,6),(2048,26,0),(2068,24,6),(2177,26,4),(4096,0,7),(4354,0,8),(8192,2,2),(8712,26,5),(11264,2,3),(16384,82,2),(17152,0,9),(22528,26,8),(32768,3,0),(32840,1,6),(33793,2,4),(44747,0,10),(65536,25,0),(65541,24,4),(65680,25,6),(68343,25,10),(101599,0,11),(131072,80,2),(131360,1,9),(135172,24,8),(135463,0,12),(154422,0,13),(169327,0,14),(203191,24,14),(262144,3,2),(262184,24,5),(270352,2,5),(270905,0,15),(273982,0,16),(304763,0,17),(338621,24,17),(360448,3,3),(361583,1,10),(369400,1,16),(371861,24,10),(406334,0,18),(507903,0,19),(524288,1,7),(524608,1,8),(540800,27,8),(541633,1,12),(547779,0,20),(575435,1,14),(609237,27,14),(676838,0,21),(720896,25,8),(725351,1,20),(738288,1,13),(743573,0,22),(778239,0,23),(812024,1,18),(913407,1,19),(1014783,0,24),(1048575,0,25),(1048576,58,2),(1053696,2,8),(1073152,3,9),(1080321,2,12),(1081098,26,13),(1113163,2,14),(1146005,26,14),(1211686,0,26),(1343032,2,18),(1441535,2,19),(1441792,2,9),(1447214,24,13),(1467192,0,27),(1473556,2,13),(1474367,0,28),(1507199,0,29),(1540031,24,29),(1572863,0,30),(1605568,26,21),(1605632,3,8),(1611083,24,22),(1631176,27,13),(1637505,3,20),(1703903,26,23),(1769455,0,31),(1802231,26,31),(1835007,0,32),(1900539,26,24),(1966079,26,25),(1998846,0,33),(2031615,0,34),(2064383,26,34),(2064385,3,12),(2064744,25,13),(2065483,3,14),(2066581,25,14),(2068774,24,21),(2069509,2,20),(2072063,24,23),(2073144,3,18),(2076415,3,19),(2078591,24,24),(2080767,24,25),(2081728,1,26),(2086895,1,31),(2087927,25,31),(2088959,1,32),(2089104,3,13),(2089977,1,28),(2091003,1,29),(2092029,25,29),(2093055,1,30),(2094078,1,33),(2095103,1,34),(2096127,25,34),(2096128,2,21),(2096351,2,23),(2096495,2,31),(2096567,24,31),(2096639,2,32),(2096829,2,24),(2096895,2,25),(2096958,2,33),(2097023,2,34),(2097087,24,34),(2097099,3,31),(2097109,27,31),(2097119,3,32),(2097135,0,35),(2097143,24,35),(2097144,3,33),(2097147,3,34),(2097149,27,34),(2097150,0,36)]),(372479,[(1,0,3),(2,28,4),(4,52,4),(8,8,3),(16,72,3),(32,60,4),(64,13,8),(67,0,37),(128,53,5),(256,56,6),(512,137,8),(560,76,37),(704,0,38),(1024,17,8),(1034,8,37),(2048,121,8),(2068,72,37),(2177,0,39),(4096,64,6),(4354,0,40),(8192,61,5),(8712,8,39),(11264,8,38),(16384,82,9),(17152,136,39),(22528,120,39),(32768,29,5),(32840,32,39),(33793,24,39),(33903,0,41),(44747,0,42),(65536,97,8),(65541,24,37),(65680,76,39),(67767,24,41),(68343,0,43),(101599,0,44),(131072,80,6),(131360,32,40),(135172,24,40),(154422,0,45),(169327,0,46),(203191,24,46),(262144,113,8),(262184,32,37),(270352,72,39),(270910,32,41),(273982,8,43),(304763,8,44),(338621,72,44),(360448,24,38),(361583,24,43),(369400,32,42),(371861,24,42),(406334,32,46),(507903,0,47),(524288,66,9),(524608,12,39),(540800,0,48),(541670,0,49),(547779,0,50),(575435,0,51),(609237,0,52),(676838,0,53),(720896,96,39),(725351,32,45),(738288,76,50),(743573,0,54),(778239,0,55),(812024,76,51),(913407,0,56),(1014783,76,55),(1048575,0,57),(1048576,58,9),(1053696,16,39),(1073152,8,48),(1080358,8,49),(1081098,8,50),(1113163,8,51),(1146005,72,51),(1211686,8,53),(1343032,8,52),(1441535,8,56),(1441792,112,39),(1447214,24,45),(1467192,8,54),(1473556,72,50),(1507199,8,55),(1540031,72,55),(1572863,8,57),(1605568,0,58),(1605632,24,48),(1611083,24,54),(1631176,0,59),(1637505,8,59),(1638383,0,60),(1703903,0,61),(1769455,0,62),(1802231,0,63),(1835007,0,64),(1900539,8,61),(1966079,0,65),(1998846,8,63),(2031615,8,64),(2064383,0,66),(2064422,24,49),(2064744,32,50),(2065483,24,52),(2066581,24,51),(2068774,24,53),(2069509,24,50),(2072063,24,55),(2073144,32,51),(2076415,24,56),(2078591,32,55),(2080767,24,57),(2081728,32,58),(2086895,32,63),(2087927,76,63),(2088959,32,66),(2089104,24,59),(2089982,32,60),(2091003,32,61),(2092029,76,61),(2093055,32,65),(2094078,32,62),(2095103,32,64),(2096127,76,64),(2096128,24,58),(2096311,24,60),(2096351,24,61),(2096495,24,63),(2096567,24,62),(2096639,24,64),(2096829,72,61),(2096895,24,65),(2096958,72,63),(2097023,24,66),(2097087,72,64),(2097099,0,67),(2097109,24,67),(2097119,0,68),(2097135,0,69),(2097143,24,69),(2097144,32,67),(2097147,8,68),(2097149,72,68),(2097150,32,69)]),(372479,[(1,0,10),(2,28,22),(4,52,13),(8,8,10),(16,73,16),(32,60,13),(38,0,42),(64,13,10),(67,52,45),(128,98,20),(256,56,13),(512,107,20),(560,101,50),(704,27,43),(1024,15,10),(1034,60,45),(2048,99,20),(2068,105,50),(2177,30,43),(2755,30,70),(4096,64,13),(4354,13,42),(8192,105,20),(8712,38,43),(11264,26,43),(11786,26,70),(16384,82,16),(17152,114,50),(22528,98,50),(32768,29,22),(32840,63,45),(33793,55,45),(41672,27,70),(44161,31,70),(65536,55,13),(65541,28,54),(65680,107,50),(68343,0,71),(101599,0,72),(110303,0,73),(131072,80,27),(131360,113,59),(135172,97,59),(154422,0,74),(169327,0,75),(180207,0,76),(203191,0,77),(262144,63,13),(262184,36,54),(270352,103,50),(273982,8,71),(304763,8,72),(306939,8,73),(338621,0,78),(360448,3,42),(361583,0,79),(369400,11,71),(371861,3,71),(406334,8,77),(507903,0,80),(524288,67,13),(524608,42,54),(540800,99,50),(547779,13,71),(575435,13,72),(585675,13,73),(609237,0,81),(676838,13,77),(720896,96,59),(725351,0,82),(738288,53,82),(743573,49,82),(778239,0,83),(786431,0,84),(812024,11,81),(913407,0,85),(1014783,0,86),(1048575,0,87),(1048576,59,13),(1053696,40,54),(1073152,115,50),(1081098,17,71),(1113163,15,72),(1113803,15,73),(1146005,3,81),(1211686,17,77),(1343032,8,81),(1441535,3,85),(1441792,112,59),(1447214,8,82),(1467192,69,82),(1473556,54,82),(1507199,8,83),(1507327,8,84),(1540031,8,86),(1572863,8,87),(1605568,13,78),(1605632,15,42),(1611083,6,79),(1631176,19,71),(1637505,15,71),(1703903,13,85),(1769455,13,80),(1802231,13,86),(1835007,13,87),(1900539,17,85),(1966079,0,88),(1998846,17,86),(2031615,17,87),(2064383,0,89),(2064744,11,82),(2065483,3,75),(2066581,3,77),(2068774,0,90),(2069509,3,82),(2072063,0,91),(2073144,11,77),(2076363,3,76),(2076415,3,80),(2078591,8,91),(2080751,0,92),(2080767,0,93),(2081728,19,77),(2086895,13,91),(2087927,0,94),(2088959,0,95),(2089104,3,74),(2091003,11,83),(2092029,11,86),(2093051,11,84),(2093055,11,87),(2094078,11,94),(2095103,11,95),(2096127,0,96),(2096128,15,77),(2096351,3,83),(2096495,15,91),(2096567,3,94),(2096639,3,95),(2096829,3,86),(2096863,3,84),(2096895,3,87),(2096958,8,94),(2097023,8,95),(2097087,3,96),(2097099,15,80),(2097109,15,86),(2097119,15,87),(2097135,13,93),(2097143,13,96),(2097144,19,86),(2097147,19,87),(2097149,3,89),(2097150,17,96)]),(744439,[(1,0,11),(2,4,14),(4,48,14),(6,28,97),(8,8,17),(16,72,17),(24,32,98),(32,60,21),(38,0,44),(64,6,14),(67,48,46),(128,49,14),(192,31,97),(256,56,18),(512,62,21),(560,100,52),(704,1,44),(1024,7,14),(1034,60,53),(2048,51,14),(2068,104,53),(2177,6,46),(3072,30,97),(3102,8,99),(4096,64,26),(4354,13,51),(8192,61,21),(8712,38,52),(11264,2,44),(16384,82,18),(17152,114,58),(22528,98,51),(32768,5,14),(32840,62,53),(33793,50,46),(36043,6,100),(44747,0,72),(65536,50,14),(65541,4,46),(65680,106,53),(67799,48,100),(68343,25,72),(98304,29,97),(98520,10,99),(99407,4,100),(101525,50,100),(131072,80,18),(131360,113,58),(135172,97,51),(154422,52,77),(169327,0,101),(203191,24,101),(237055,0,102),(262144,63,21),(262184,36,52),(270352,102,52),(273982,33,78),(304763,0,103),(338621,24,103),(360448,3,44),(361583,1,72),(369400,32,78),(371861,24,72),(406334,0,104),(507903,0,105),(524288,66,26),(524608,12,51),(540800,99,51),(547779,38,81),(575435,1,101),(609237,27,101),(643039,1,102),(676838,56,104),(720896,96,51),(725351,36,81),(738288,53,77),(743573,48,75),(778239,0,106),(812024,1,104),(913407,1,105),(1014783,0,107),(1048575,0,108),(1048576,58,18),(1053696,14,51),(1073152,115,58),(1081098,30,77),(1113163,2,101),(1146005,26,101),(1178847,2,102),(1211686,0,109),(1343032,2,104),(1441535,2,105),(1441792,112,58),(1447214,28,77),(1467192,68,90),(1473556,54,77),(1507199,0,110),(1540031,24,110),(1572863,0,111),(1605568,82,104),(1605632,15,51),(1611083,4,75),(1631176,31,77),(1637505,39,81),(1703903,26,106),(1769455,0,112),(1802231,26,112),(1835007,0,113),(1900539,26,107),(1966079,26,108),(1998846,0,114),(2031615,0,115),(2064383,26,115),(2064744,29,77),(2065483,3,101),(2066581,25,101),(2067679,3,102),(2068774,80,104),(2069509,37,81),(2072063,24,106),(2073144,3,104),(2076415,3,105),(2078591,24,107),(2080767,24,108),(2081728,1,109),(2086895,1,112),(2087927,25,112),(2088959,1,113),(2089104,55,77),(2091003,1,110),(2092029,25,110),(2093055,1,111),(2094078,1,114),(2095103,1,115),(2096127,25,115),(2096128,58,104),(2096351,2,106),(2096495,2,112),(2096567,24,112),(2096639,2,113),(2096829,2,107),(2096895,2,108),(2096958,2,114),(2097023,2,115),(2097087,24,115),(2097099,3,112),(2097109,27,112),(2097119,3,113),(2097135,0,116),(2097143,24,116),(2097144,3,114),(2097147,3,115),(2097149,27,115),(2097150,0,117)]),(372479,[(1,0,19),(2,28,23),(4,52,23),(8,8,19),(16,72,19),(32,60,23),(38,0,47),(64,13,31),(67,52,55),(128,53,24),(256,56,29),(512,137,31),(560,100,55),(704,1,56),(960,53,118),(1024,17,31),(1034,60,55),(2048,121,31),(2068,104,55),(2177,30,63),(4096,64,29),(4354,13,62),(8192,61,24),(8712,38,63),(11264,9,56),(15360,61,118),(16384,82,33),(17152,136,61),(22528,120,61),(32768,29,24),(32840,62,63),(33793,54,63),(44747,0,80),(49099,13,119),(65536,97,31),(65541,28,55),(65680,106,63),(68343,25,85),(101599,0,105),(131072,80,29),(131360,113,62),(135172,97,62),(154422,52,83),(169327,28,106),(203191,52,106),(203767,52,120),(262144,113,31),(262184,36,55),(270352,102,63),(273982,33,85),(304763,8,105),(338621,72,105),(360448,25,56),(361583,1,85),(369400,32,80),(371861,24,80),(406334,60,106),(409406,60,120),(491520,29,118),(497007,28,120),(500728,113,119),(507029,97,119),(524288,66,33),(524608,12,61),(540800,99,67),(547779,101,86),(575435,13,112),(609237,53,107),(676838,56,110),(720896,96,61),(725351,36,83),(738288,53,86),(743573,48,91),(778239,0,121),(812024,137,112),(913407,0,122),(1014783,76,121),(1048575,0,123),(1048576,58,33),(1053696,16,61),(1073152,115,67),(1081098,105,86),(1113163,17,112),(1146005,121,112),(1211686,64,110),(1343032,61,107),(1441535,8,122),(1441792,112,61),(1447214,28,83),(1467192,68,91),(1473556,61,86),(1507199,8,121),(1540031,72,121),(1572863,8,123),(1605568,82,114),(1605632,15,67),(1611083,4,91),(1631176,31,94),(1637505,39,94),(1703903,0,124),(1769455,0,125),(1802231,120,124),(1835007,0,126),(1900539,8,124),(1966079,0,127),(1998846,136,124),(2031615,8,126),(2064383,0,128),(2064744,29,86),(2065483,29,107),(2066581,97,112),(2068774,80,110),(2069509,37,86),(2072063,24,121),(2073144,113,112),(2076415,24,122),(2078591,32,121),(2080767,24,123),(2081728,66,114),(2086895,12,124),(2087927,96,124),(2088959,32,128),(2089104,55,94),(2091003,32,124),(2092029,76,124),(2093055,32,127),(2094078,32,125),(2095103,32,126),(2096127,76,126),(2096128,58,114),(2096351,24,124),(2096495,16,124),(2096567,24,125),(2096639,24,126),(2096829,72,124),(2096895,24,127),(2096958,112,124),(2097023,24,128),(2097087,72,126),(2097099,0,129),(2097109,24,129),(2097119,0,130),(2097135,0,131),(2097143,24,131),(2097144,32,129),(2097147,8,130),(2097149,72,130),(2097150,32,131)]),(372479,[(1,0,25),(2,12,32),(4,52,25),(8,8,30),(16,76,25),(32,60,32),(38,0,57),(64,13,32),(67,52,57),(128,53,25),(256,56,30),(512,62,32),(560,100,57),(704,1,57),(1024,17,34),(1034,60,64),(2048,51,35),(2068,105,66),(2177,30,66),(4096,64,34),(4354,13,64),(8192,114,34),(8712,38,64),(11264,26,65),(16384,90,34),(17152,136,64),(22528,98,65),(31744,30,132),(32768,18,34),(32840,62,64),(33793,50,69),(44747,0,87),(65536,50,35),(65541,29,66),(65680,106,66),(68343,25,88),(101599,0,108),(131072,88,34),(131360,137,64),(135172,97,69),(154422,52,87),(169327,12,113),(203191,52,108),(262144,113,34),(262184,36,64),(270352,146,69),(273982,77,87),(304763,8,111),(338621,76,108),(360448,25,65),(361583,1,87),(369400,76,87),(371861,24,93),(406334,60,113),(425790,60,133),(507903,0,123),(524288,66,34),(524608,12,64),(540800,99,69),(547779,101,87),(575435,13,113),(589771,13,133),(609237,53,108),(676838,56,111),(720896,96,65),(725351,100,87),(738288,53,87),(743573,48,93),(778239,52,123),(812024,62,113),(913407,1,123),(1014783,100,123),(1015808,29,132),(1021295,12,133),(1041400,62,133),(1047701,50,134),(1048576,58,36),(1053696,16,68),(1073152,115,68),(1081098,30,89),(1113163,17,115),(1146005,51,116),(1211686,64,115),(1343032,114,115),(1441535,26,127),(1441792,112,68),(1447214,28,95),(1467192,152,95),(1473556,61,96),(1507199,60,126),(1540031,105,128),(1572863,0,135),(1605568,90,115),(1605632,19,68),(1611083,4,95),(1631176,31,95),(1637505,39,96),(1703903,30,128),(1769455,13,126),(1802231,98,127),(1835007,52,135),(1900539,38,126),(1966079,34,135),(1998846,136,126),(2031615,0,136),(2064383,101,135),(2064744,29,89),(2065483,18,115),(2066581,50,116),(2068774,88,115),(2069509,37,96),(2072063,29,128),(2073144,113,115),(2076415,25,127),(2078591,36,126),(2080767,32,135),(2081728,66,115),(2086895,12,126),(2087927,96,127),(2088959,53,135),(2089104,63,96),(2091003,62,126),(2092029,106,128),(2093055,1,135),(2094078,137,126),(2095103,1,136),(2096127,100,135),(2096128,58,117),(2096351,50,131),(2096495,16,130),(2096567,97,131),(2096639,0,137),(2096829,146,131),(2096895,0,138),(2096958,112,130),(2097023,20,137),(2097087,76,137),(2097099,19,130),(2097109,99,131),(2097119,1,137),(2097135,44,137),(2097143,52,138),(2097144,115,130),(2097147,23,137),(2097149,77,137),(2097150,140,137)])]
def F1 : ℕ → Bool := rowAt L1 E1 L2
def E2 : Array (G × List Link) := #[(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[(135463,0,0),(270905,0,1),(406334,0,2),(541633,1,0),(676838,0,3),(812024,1,2),(1080321,2,0),(1211686,0,4),(1343032,2,2),(1474367,0,5),(1605568,26,3),(1998846,0,6),(2064385,3,0),(2068774,24,3),(2073144,3,2),(2081728,1,4),(2089977,1,5),(2094078,1,6),(2096128,2,3),(2096958,2,6),(2097144,3,6),(2097150,0,7)]),(372479,[(101599,0,0)]),(372479,[]),(372479,[(338621,0,8),(609237,0,9),(812024,0,10),(1146005,0,11),(1343032,0,12),(1605568,0,13),(2066581,25,9),(2073144,0,14),(2081728,0,15),(2092029,0,16),(2096128,0,17),(2096829,0,18),(2097109,0,19),(2097144,0,20),(2097149,0,21)]),(372479,[(101599,0,1)]),(372479,[]),(744439,[(203191,24,8),(609237,27,8),(676838,0,22),(1146005,26,8),(1211686,0,23),(1605568,0,24),(1802231,0,25),(2066581,25,8),(2068774,1,24),(2081728,1,23),(2087927,1,25),(2096128,2,22),(2096567,2,25),(2097109,3,25),(2097143,0,26)]),(372479,[(101599,0,2),(575435,1,10),(609237,27,14),(1113163,2,12),(1146005,26,12),(1605568,0,27),(1703903,0,28),(2065483,3,14),(2066581,25,10),(2081728,0,29),(2096128,24,27),(2096351,24,28),(2097099,0,30),(2097109,24,30),(2097119,0,31)]),(372479,[(1605568,0,32),(2081728,0,33),(2096128,24,32)]),(372479,[]),(372479,[(101599,0,3),(304763,0,22),(338621,25,24),(1113163,2,17),(1146005,26,13),(1343032,26,27),(1441535,26,32),(2065483,3,17),(2066581,25,13),(2073144,25,27),(2076415,25,32),(2096128,0,34),(2096351,0,35),(2096829,0,36),(2096895,0,37)]),(372479,[]),(372479,[(1343032,26,28),(2073144,25,28),(2096128,2,35)]),(372479,[(1113163,2,18),(2065483,3,18),(2096128,2,36)]),(372479,[(2096128,2,37)]),(372479,[(101599,0,4),(304763,0,23),(338621,24,23),(575435,1,15),(609237,27,15),(812024,1,29),(913407,1,33),(2065483,3,15),(2066581,25,15),(2073144,3,29),(2076415,3,33),(2081728,0,38),(2091003,0,39),(2092029,24,39),(2093055,0,40)]),(372479,[]),(372479,[(101599,0,5)]),(372479,[(609237,27,16),(2066581,25,16),(2081728,1,39)]),(372479,[(2081728,1,40)]),(372479,[(338621,26,25),(2066581,25,19),(2073144,3,30)]),(372479,[(2073144,3,31)]),(372479,[(101599,0,6),(2065483,3,20),(2066581,25,20)]),(372479,[(2066581,25,21)]),(372479,[(338621,24,26)]),(372479,[(101599,0,7)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[(338621,0,41)]),(372479,[]),(372479,[]),(744439,[(270910,32,41),(406334,0,42),(541670,0,43),(676838,0,44),(812024,0,45),(1080358,0,46),(1211686,0,47),(1343032,0,48),(1605568,0,49),(1998846,0,50),(2064422,24,43),(2068774,24,44),(2073144,24,45),(2081728,0,51),(2089982,0,52),(2094078,0,53),(2096128,24,49),(2096958,24,50),(2097144,0,54),(2097150,0,55)]),(372479,[]),(372479,[(338621,72,42),(541670,0,56),(609237,0,57),(812024,0,58),(1080358,8,56),(1146005,8,58),(1343032,8,57),(1605568,0,59),(2064422,0,60),(2066581,0,61),(2073144,8,61),(2081728,0,62),(2089982,0,63),(2092029,0,64),(2096128,8,62),(2096311,8,63),(2096829,8,64),(2097109,0,65),(2097144,8,65),(2097149,0,66)]),(372479,[(541670,0,67),(1080358,8,67),(1605568,0,68),(2064422,24,67),(2081728,32,68),(2096128,24,68)]),(372479,[]),(372479,[(101599,0,43),(169327,0,56),(203191,24,60),(304763,8,46),(338621,76,43),(406334,76,56),(507903,0,67)]),(372479,[]),(372479,[(203191,24,61),(338621,76,45),(406334,76,58),(1146005,0,69),(1211686,0,70),(1343032,0,71),(1540031,0,72),(2066581,0,73),(2068774,0,74),(2073144,32,69),(2096128,0,75),(2096567,0,76),(2096829,0,77),(2096958,0,78),(2097087,0,79)]),(372479,[(169327,0,57),(304763,8,48),(406334,76,57),(1113163,8,71),(1211686,0,80),(1343032,0,81),(1507199,0,82),(2065483,32,81),(2068774,76,80),(2073144,32,71),(2078591,76,82),(2096128,0,83),(2096495,0,84),(2096958,76,84),(2097023,0,85)]),(372479,[(101599,0,44),(304763,8,47),(338621,76,44),(1113163,8,70),(1146005,72,74),(1343032,8,80),(1441535,0,86),(2065483,32,80),(2066581,24,74),(2073144,32,70),(2076415,76,86),(2096128,0,87),(2096351,0,88),(2096829,76,88),(2096895,0,89)]),(372479,[]),(372479,[(1343032,8,82),(2073144,32,72),(2096128,0,90)]),(372479,[(1211686,8,86),(2068774,32,86),(2096128,0,91)]),(372479,[(2096128,0,92)]),(372479,[(101599,0,49),(169327,0,59),(203191,72,62),(304763,8,49),(338621,72,51),(406334,76,62),(507903,0,68),(2065483,24,83),(2066581,24,75),(2068774,24,87),(2072063,24,90),(2073144,32,75),(2076415,24,91),(2078591,32,90),(2080767,24,92)]),(372479,[]),(372479,[(203191,72,63),(338621,72,52),(406334,76,63)]),(372479,[(406334,76,64),(2068774,24,88),(2073144,32,77)]),(372479,[(338621,72,53),(2066581,24,76),(2073144,32,76)]),(372479,[(304763,8,50),(2065483,24,84),(2073144,32,78)]),(372479,[(2073144,32,79)]),(372479,[(2068774,24,89)]),(372479,[(2065483,24,85)]),(372479,[(203191,24,65),(338621,72,54),(406334,32,65)]),(372479,[(406334,32,66)]),(372479,[(338621,72,55)]),(372479,[]),(372479,[]),(744439,[(406334,0,93),(676838,0,94),(812024,0,95),(1211686,0,96),(1343032,3,95),(1605568,0,97),(1998846,0,98),(2068774,0,99),(2073144,3,93),(2081728,3,96),(2094078,0,100),(2096128,3,94),(2096958,3,100),(2097144,3,98),(2097150,0,101)]),(744439,[(406334,0,102),(2068774,0,103),(2073144,3,102)]),(372479,[]),(372479,[(338621,0,104),(609237,0,105),(812024,0,106),(1146005,8,106),(1343032,8,105),(1605568,13,104),(2066581,0,107),(2073144,8,107),(2081728,13,107),(2092029,0,108),(2096128,17,107),(2096829,8,108),(2097109,13,108),(2097144,17,108),(2097149,0,109)]),(372479,[(338621,0,110),(609237,0,111),(812024,0,112),(1146005,8,112),(1343032,8,111),(1605568,13,110),(2066581,0,113),(2073144,8,113),(2081728,13,113),(2092029,0,114),(2096128,17,113),(2096829,8,114),(2097109,13,114),(2097144,17,114),(2097149,0,115)]),(372479,[(304763,8,93),(306939,8,102),(575435,13,94),(812024,0,116),(1113163,17,96),(1343032,0,117),(1605568,0,118),(1900539,0,119),(2065483,3,107),(2073144,0,120),(2076363,3,113),(2081728,0,121),(2091003,0,122),(2093051,0,123),(2096128,15,121),(2097099,0,124),(2097144,0,125),(2097147,0,126)]),(744439,[(169327,0,104),(180207,0,110),(575435,13,97),(676838,13,118),(1113163,15,97),(1211686,17,118),(1605568,0,127),(1769455,0,128),(2065483,3,104),(2068774,0,129),(2076363,3,110),(2080751,0,130),(2081728,19,118),(2086895,0,131),(2096128,15,118),(2096495,3,131),(2097099,3,128),(2097135,0,132)]),(372479,[]),(372479,[(1605568,13,128),(2081728,19,124),(2096128,15,124)]),(372479,[(169327,0,105),(180207,0,111),(304763,11,95),(406334,8,117),(1113163,15,95),(1211686,17,117),(1343032,0,133),(1507199,0,134),(1507327,0,135),(2065483,11,106),(2068774,0,136),(2073144,11,116),(2076363,11,112),(2078591,0,137),(2080751,0,138),(2096128,15,116),(2096495,13,137),(2096958,0,139),(2097023,0,140)]),(372479,[]),(372479,[(1343032,8,134),(2073144,11,122),(2096128,15,122)]),(372479,[(1343032,8,135),(2073144,11,123),(2096128,15,123)]),(372479,[(1211686,17,119),(2068774,0,141),(2096128,15,119)]),(372479,[(1113163,17,98),(2065483,11,108),(2076363,11,114),(2096128,15,125)]),(372479,[(2096128,15,126)]),(372479,[(2068774,0,142)]),(372479,[(2065483,3,109),(2076363,3,115)]),(372479,[(101599,0,99),(110303,0,103),(304763,8,99),(306939,8,103),(338621,0,129),(575435,13,99),(585675,13,103),(609237,0,136),(812024,11,136),(913407,0,141),(1113163,15,99),(1113803,15,103),(1146005,3,136),(1343032,8,136),(1441535,3,141),(1605568,13,129),(1703903,13,141),(1900539,17,141),(1966079,0,142)]),(372479,[(812024,11,137),(1343032,8,137),(1605568,13,131)]),(372479,[(338621,0,130),(609237,0,138),(812024,11,138),(1146005,3,138),(1343032,8,138),(1605568,13,130)]),(372479,[(1605568,13,132)]),(372479,[(304763,11,100),(1113163,15,100),(1343032,8,139)]),(372479,[(1343032,8,140)]),(372479,[(1113163,15,101)]),(372479,[(270907,0,143),(304763,0,144),(541635,0,145),(575435,0,146),(812024,0,147),(1080323,0,148),(1113163,0,149),(1343032,0,150),(1605568,0,151),(1900539,0,152),(2064387,4,143),(2065483,4,144),(2073144,0,153),(2081728,4,147),(2089979,0,154),(2091003,0,155),(2096128,4,150),(2097099,4,152),(2097144,0,156),(2097147,0,157)]),(744439,[(135471,0,158),(169327,0,159),(541641,1,158),(575435,1,159),(676838,0,160),(1080329,2,158),(1113163,2,159),(1211686,8,160),(1605568,0,161),(1769455,0,162),(2064393,3,158),(2065483,3,159),(2068774,1,161),(2081728,10,160),(2086895,1,162),(2096128,2,160),(2096495,2,162),(2097099,3,162),(2097135,0,163)]),(744439,[(203191,0,164),(609237,1,164),(676838,0,165),(1080947,0,166),(1146005,0,167),(1211686,0,168),(1605568,77,168),(1802231,0,169),(2065011,1,166),(2066581,1,167),(2068774,76,168),(2081728,1,168),(2087927,1,169),(2096128,0,170),(2096567,0,171),(2096887,0,172),(2097109,1,171),(2097143,0,173)]),(372479,[(338621,0,174),(609237,0,175),(812024,0,176),(1146005,8,176),(1343032,8,175),(1605568,0,177),(2066581,0,178),(2073144,8,178),(2081728,0,179),(2092029,0,180),(2096128,8,179),(2096829,8,180),(2097109,0,181),(2097144,8,181),(2097149,0,182)]),(744439,[(203191,0,183),(338621,0,184),(406334,0,185),(609237,49,185),(676838,56,185),(812024,0,186),(1014783,0,187),(1146005,0,188),(1211686,4,188),(1343032,0,189),(1540031,0,190),(1605568,0,191),(1802231,0,192),(1998846,0,193),(2064383,0,194),(2066581,4,185),(2068774,4,184),(2073144,0,195),(2081728,4,186),(2087927,4,187),(2092029,0,196),(2094078,4,196),(2096127,0,197),(2096128,4,189),(2096567,4,190),(2096829,0,198),(2096958,4,198),(2097087,0,199),(2097109,4,193),(2097143,4,194),(2097144,0,200),(2097149,0,201),(2097150,4,201)]),(744439,[(406334,0,202),(676838,0,203),(812024,0,204),(1211686,0,205),(1343032,0,206),(1605568,0,207),(1998846,0,208),(2068774,24,203),(2073144,24,204),(2081728,0,209),(2094078,0,210),(2096128,24,207),(2096958,24,208),(2097144,0,211),(2097150,0,212)]),(744439,[(203191,24,184),(338621,0,213),(406334,32,184),(609237,27,184),(676838,0,214),(812024,34,184),(1014783,0,215),(1146005,26,184),(1211686,8,214),(1343032,35,184),(1540031,8,215),(1605568,0,216),(1802231,0,217),(1998846,8,217),(2064383,0,218),(2066581,25,184),(2068774,1,216),(2073144,33,184),(2081728,10,214),(2087927,1,217),(2092029,10,215),(2094078,10,217),(2096127,1,218),(2096128,2,214),(2096567,2,217),(2096829,2,215),(2096958,9,217),(2097087,2,218),(2097109,3,217),(2097143,0,219),(2097144,11,217),(2097149,3,218),(2097150,8,219)]),(744439,[(1,0,2),(2,36,9),(4,100,9),(6,28,146),(8,32,8),(10,8,144),(16,76,8),(20,72,144),(24,32,159),(30,0,220),(32,60,3),(38,0,42),(64,6,15),(67,48,61),(128,49,14),(192,53,147),(256,132,12),(512,137,13),(560,100,57),(704,1,45),(768,133,150),(1024,7,17),(1034,60,44),(2048,51,17),(2068,104,44),(2177,6,62),(3072,30,151),(3102,8,164),(4096,64,23),(4354,13,70),(8192,114,24),(8712,38,80),(11264,2,48),(12288,61,160),(13066,64,168),(16384,82,27),(17152,136,49),(22528,98,71),(32768,5,14),(32840,70,74),(33793,50,62),(36043,6,179),(44747,0,93),(65536,50,15),(65541,4,61),(65680,154,74),(67799,48,178),(68343,25,95),(98304,29,147),(98520,10,167),(99407,4,178),(101525,50,179),(131072,88,12),(131360,113,59),(135172,97,70),(135990,100,175),(154422,60,94),(169327,0,185),(203191,24,185),(237055,0,202),(262144,113,13),(262184,36,57),(270352,102,80),(270910,32,174),(273982,112,97),(304763,32,184),(338621,76,184),(360448,25,45),(361583,1,95),(369400,32,104),(371861,24,93),(393216,89,150),(397614,36,175),(402232,113,177),(405524,128,168),(440191,60,203),(474047,104,203),(507903,0,221),(524288,118,29),(524608,12,69),(540800,99,75),(547779,133,117),(575435,1,186),(609237,27,195),(643039,1,204),(676838,132,189),(720896,96,69),(725351,36,105),(738288,53,116),(743573,48,107),(778239,0,222),(812024,136,191),(913407,0,223),(947198,136,207),(1014783,0,224),(1048575,0,225),(1048576,58,27),(1053696,14,71),(1073152,143,83),(1081098,30,118),(1113163,2,189),(1146005,26,189),(1178847,2,206),(1211686,60,214),(1343032,112,216),(1441535,0,226),(1441792,112,49),(1447214,104,94),(1467192,68,99),(1473556,54,118),(1507199,0,227),(1540031,24,227),(1572863,0,228),(1605568,0,229),(1605632,15,75),(1611083,4,107),(1631176,31,121),(1637505,39,136),(1703903,0,230),(1769455,0,231),(1802231,0,232),(1835007,0,233),(1900539,0,234),(1966079,0,235),(1998846,0,236),(2031615,0,237),(2064383,0,238),(2064744,29,116),(2065483,3,195),(2066581,25,186),(2067679,25,204),(2068774,88,189),(2069509,89,117),(2072063,24,222),(2073144,112,191),(2076415,24,223),(2077502,112,207),(2078591,24,224),(2080767,24,225),(2081728,0,239),(2086895,0,240),(2087927,24,240),(2088959,0,241),(2089104,55,121),(2091003,0,242),(2092029,24,242),(2093055,0,243),(2094078,0,244),(2095103,0,245),(2096127,24,245),(2096128,24,229),(2096351,24,230),(2096495,24,232),(2096567,24,231),(2096639,24,233),(2096829,24,234),(2096895,24,235),(2096958,24,236),(2097023,24,238),(2097087,24,237),(2097099,0,246),(2097109,24,246),(2097119,0,247),(2097135,0,248),(2097143,24,248),(2097144,0,249),(2097147,0,250),(2097149,24,250),(2097150,0,251)]),(744439,[(406334,0,221),(676838,56,227),(812024,1,223),(1211686,0,252),(1343032,2,226),(1605568,82,236),(1998846,0,253),(2068774,80,227),(2073144,25,223),(2081728,0,254),(2094078,0,255),(2096128,58,236),(2096958,24,253),(2097144,0,256),(2097150,0,257)]),(744439,[(406334,0,222),(676838,56,221),(812024,1,222),(1211686,0,258),(1343032,26,230),(1605568,82,224),(1998846,0,259),(2068774,81,224),(2073144,25,230),(2081728,1,258),(2094078,1,259),(2096128,58,244),(2096958,0,260),(2097144,1,260),(2097150,0,261)]),(744439,[(169327,0,187),(304763,0,215),(406334,0,224),(575435,1,187),(676838,56,226),(812024,1,224),(1113163,2,198),(1211686,0,262),(1343032,26,234),(1507199,0,263),(1605568,82,232),(1769455,0,264),(1900539,0,265),(1998846,0,266),(2031615,0,267),(2065483,3,198),(2068774,81,232),(2073144,25,234),(2078591,1,265),(2081728,1,262),(2086895,1,264),(2091003,1,263),(2094078,1,266),(2095103,1,267),(2096128,58,249),(2096495,0,268),(2096958,0,269),(2097023,0,270),(2097099,1,268),(2097135,0,271),(2097144,1,269),(2097147,1,270),(2097150,0,272)]),(744439,[(406334,0,225),(676838,56,228),(812024,1,225),(1211686,0,273),(1343032,26,235),(1605568,82,238),(1998846,0,274),(2068774,81,238),(2073144,25,235),(2081728,1,273),(2094078,1,274),(2096128,58,251),(2096958,0,275),(2097144,1,275),(2097150,0,276)]),(744439,[(1,0,4),(2,4,11),(4,48,11),(6,28,149),(8,8,22),(16,72,22),(24,33,161),(32,60,22),(38,0,47),(64,6,10),(67,49,58),(128,49,10),(192,31,153),(256,108,10),(512,62,34),(560,101,81),(704,1,51),(1024,7,11),(1026,16,149),(1034,64,47),(2048,51,11),(2052,120,149),(2068,128,47),(2177,6,58),(3072,30,149),(3078,5,277),(3102,8,165),(4096,64,4),(4354,86,58),(8192,61,22),(8224,112,161),(8712,38,81),(11264,2,47),(11302,60,165),(16384,86,10),(16640,94,153),(17152,116,51),(22528,108,58),(32768,5,10),(32840,62,87),(33793,50,58),(36043,6,176),(44747,0,96),(65536,50,10),(65541,5,58),(65680,106,87),(67799,49,176),(68343,26,96),(98304,29,153),(98520,10,170),(99407,5,176),(101525,50,176),(131072,84,10),(131360,141,87),(135172,110,58),(153894,108,176),(154422,64,96),(169327,4,188),(203191,48,188),(237055,0,205),(262144,63,34),(262184,37,81),(270352,102,81),(273982,33,127),(304763,8,214),(338621,72,214),(360448,3,51),(361583,2,96),(369400,32,129),(371861,24,96),(406334,60,214),(507903,0,252),(524288,66,38),(524608,12,73),(540800,99,73),(547779,38,133),(575435,6,186),(609237,49,186),(643039,1,209),(676838,108,186),(720896,96,73),(725351,84,106),(738288,53,120),(743573,49,106),(778239,0,258),(812024,1,239),(913407,1,254),(1014783,0,262),(1048575,0,273),(1048576,110,10),(1053696,84,58),(1073152,143,87),(1080578,86,176),(1081098,129,96),(1113163,7,188),(1146005,51,188),(1178847,2,205),(1179648,93,153),(1185062,84,176),(1204512,140,170),(1211396,110,176),(1244527,64,205),(1277367,128,205),(1310207,0,278),(1343032,61,214),(1441535,2,252),(1441792,117,51),(1447214,128,96),(1467192,68,129),(1473556,65,96),(1507199,64,252),(1540031,128,252),(1572863,0,279),(1605568,86,186),(1605632,15,73),(1611083,5,106),(1631176,31,120),(1637505,86,106),(1703903,26,258),(1736678,116,209),(1769455,64,258),(1802231,129,258),(1835007,0,280),(1900539,26,262),(1966079,26,273),(1998846,116,254),(2031615,64,273),(2064383,129,273),(2064744,29,120),(2065483,5,186),(2066581,50,186),(2067679,3,209),(2068774,84,186),(2069509,37,133),(2072063,24,258),(2073144,3,239),(2076415,3,254),(2078591,24,262),(2080767,24,273),(2081728,0,281),(2086895,0,282),(2087927,24,282),(2088959,0,283),(2089104,55,120),(2091003,0,284),(2092029,24,284),(2093055,0,285),(2094078,64,284),(2095103,0,286),(2096127,24,286),(2096128,110,186),(2096351,2,258),(2096422,117,209),(2096495,65,258),(2096567,128,258),(2096639,2,280),(2096829,2,262),(2096895,2,273),(2096958,117,254),(2097023,65,273),(2097087,128,273),(2097099,2,282),(2097109,26,282),(2097119,2,283),(2097135,64,283),(2097143,128,283),(2097144,65,284),(2097147,2,286),(2097149,26,286),(2097150,64,285)]),(744439,[(203191,24,190),(338621,72,215),(406334,0,227),(609237,27,196),(676838,56,231),(812024,1,242),(1014783,0,263),(1146005,26,190),(1211686,64,252),(1343032,2,227),(1540031,0,287),(1605568,82,234),(1802231,0,288),(1998846,0,289),(2064383,0,290),(2066581,25,196),(2068774,80,234),(2073144,3,242),(2081728,1,284),(2087927,0,291),(2092029,0,292),(2094078,0,293),(2096127,0,294),(2096128,58,231),(2096567,2,288),(2096829,2,263),(2096958,2,289),(2097087,2,290),(2097109,2,291),(2097143,0,295),(2097144,2,293),(2097149,2,294),(2097150,0,296)]),(744439,[(406334,0,228),(676838,56,237),(812024,1,243),(1211686,0,279),(1343032,2,228),(1605568,82,237),(1998846,0,297),(2068774,80,237),(2073144,3,243),(2081728,1,285),(2094078,0,298),(2096128,58,237),(2096958,2,297),(2097144,2,298),(2097150,0,299)]),(744439,[(203191,48,190),(338621,26,217),(406334,0,231),(609237,49,187),(676838,56,222),(812024,1,240),(1014783,0,264),(1146005,26,192),(1211686,64,258),(1343032,26,232),(1540031,26,288),(1605568,82,223),(1802231,0,300),(1998846,0,301),(2064383,0,302),(2066581,50,193),(2068774,80,242),(2073144,3,246),(2081728,1,282),(2087927,0,303),(2092029,27,291),(2094078,0,304),(2096127,0,305),(2096128,58,240),(2096567,0,306),(2096829,2,268),(2096958,0,307),(2097087,0,308),(2097109,27,303),(2097143,0,309),(2097144,0,310),(2097149,0,311),(2097150,0,312)]),(744439,[(406334,0,233),(676838,56,225),(812024,1,241),(1211686,0,280),(1343032,26,233),(1605568,82,225),(1998846,0,313),(2068774,80,245),(2073144,3,247),(2081728,1,283),(2094078,0,314),(2096128,58,245),(2096958,0,315),(2097144,26,314),(2097150,0,316)]),(744439,[(1,0,6),(2,4,19),(4,48,18),(6,52,152),(8,8,25),(16,73,25),(24,34,162),(32,136,32),(38,0,50),(64,6,16),(67,49,64),(128,49,16),(192,31,155),(256,56,28),(512,62,35),(560,101,82),(704,1,53),(1024,7,18),(1034,60,86),(1098,17,317),(2048,51,19),(2068,105,86),(2177,6,64),(2196,120,317),(3072,30,152),(3102,8,169),(3294,0,318),(4096,116,33),(4354,13,72),(8192,114,32),(8712,38,82),(11264,26,50),(16384,82,28),(17152,114,68),(22528,98,72),(32768,5,20),(32840,62,88),(33793,51,65),(36043,6,180),(44747,0,98),(65536,50,20),(65541,4,65),(65680,107,88),(67799,49,180),(68343,26,98),(98304,29,156),(98520,10,171),(99407,4,181),(101525,51,181),(131072,80,30),(131360,141,90),(135172,97,78),(154422,52,119),(169327,0,193),(203191,48,198),(237055,0,208),(262144,63,36),(262184,36,84),(270352,103,84),(273982,34,128),(274174,34,319),(304763,8,217),(338621,73,217),(360448,3,54),(361583,1,100),(369400,35,131),(371861,27,100),(406334,0,236),(507903,0,253),(524288,66,39),(524608,12,76),(540800,99,76),(547779,38,134),(575435,6,196),(609237,49,196),(643039,1,210),(676838,56,230),(678902,0,320),(720896,96,77),(725351,100,137),(738288,53,122),(743573,49,108),(778239,0,259),(812024,1,244),(913407,1,255),(1014783,0,266),(1048575,0,274),(1048576,58,30),(1053696,14,78),(1073152,167,90),(1081098,30,119),(1113163,7,198),(1146005,26,193),(1178847,26,208),(1211686,116,254),(1343032,26,236),(1441535,26,253),(1441792,142,91),(1447214,28,124),(1467192,69,141),(1473556,54,124),(1507199,0,289),(1540031,26,289),(1572863,0,297),(1605568,82,230),(1605578,26,320),(1605632,15,77),(1611083,6,108),(1631176,31,122),(1637505,39,137),(1703903,26,259),(1769455,0,301),(1802231,26,301),(1835007,0,313),(1900539,26,266),(1966079,26,274),(1966080,143,321),(1971566,44,322),(1991672,1,323),(1997972,151,322),(2031615,0,324),(2064383,26,324),(2064744,29,125),(2065483,3,200),(2066581,25,200),(2067679,3,211),(2068774,80,246),(2069509,37,139),(2072063,24,260),(2073144,3,249),(2076415,3,256),(2078591,24,269),(2080767,24,275),(2081728,66,284),(2086895,1,304),(2087927,25,310),(2088959,1,314),(2089104,55,125),(2091003,1,293),(2092029,27,293),(2093055,1,298),(2094078,0,325),(2095103,0,326),(2096127,0,327),(2096128,58,246),(2096351,2,260),(2096495,2,307),(2096567,24,307),(2096639,2,315),(2096829,2,269),(2096895,2,275),(2096958,0,328),(2097023,0,329),(2097087,26,329),(2097099,3,310),(2097109,27,304),(2097119,27,314),(2097135,0,330),(2097143,26,330),(2097144,26,325),(2097147,26,327),(2097149,26,326),(2097150,0,331)]),(744439,[(203191,24,199),(338621,26,218),(406334,0,237),(609237,27,197),(676838,56,233),(812024,1,245),(1014783,0,267),(1146005,26,194),(1211686,64,273),(1343032,26,238),(1540031,26,290),(1605568,82,235),(1802231,26,302),(1998846,0,324),(2064383,0,332),(2066581,25,201),(2068774,80,250),(2073144,3,250),(2081728,1,286),(2087927,25,311),(2092029,27,294),(2094078,1,326),(2096127,0,333),(2096128,58,248),(2096567,24,308),(2096829,2,270),(2096958,2,329),(2097087,0,334),(2097109,27,305),(2097143,0,335),(2097144,27,327),(2097149,27,333),(2097150,0,336)]),(744439,[(203191,48,194),(338621,24,219),(406334,0,248),(609237,49,194),(676838,56,241),(812024,1,248),(1014783,0,271),(1146005,51,194),(1211686,64,283),(1343032,2,248),(1540031,24,295),(1605568,82,243),(1802231,26,309),(1998846,0,330),(2064383,26,335),(2066581,50,194),(2068774,80,243),(2073144,3,248),(2081728,66,283),(2087927,25,309),(2092029,25,295),(2094078,1,330),(2096127,25,335),(2096128,58,241),(2096567,24,309),(2096829,2,271),(2096958,2,330),(2097087,24,335),(2097109,27,309),(2097143,0,337),(2097144,3,330),(2097149,27,335),(2097150,0,338)]),(744439,[(1,0,7),(2,4,21),(4,48,21),(6,28,157),(8,8,26),(16,72,26),(24,32,163),(32,60,37),(38,0,55),(64,6,21),(67,48,66),(128,49,21),(192,31,157),(256,56,31),(512,62,37),(560,100,85),(704,1,55),(1024,7,21),(1034,60,89),(2048,51,21),(2068,104,89),(2177,6,66),(3072,30,157),(3102,8,173),(4096,64,40),(4354,13,79),(8192,61,37),(8712,38,85),(11264,2,55),(16384,82,31),(17152,140,92),(22528,98,79),(32768,5,21),(32840,62,89),(33793,50,66),(33866,20,339),(36043,6,182),(44747,0,101),(65536,50,21),(65541,4,66),(65680,106,89),(67732,144,339),(67799,48,182),(68343,25,101),(98304,29,157),(98520,10,173),(99407,4,182),(101525,50,182),(101598,0,340),(131072,80,31),(131360,141,92),(135172,97,79),(154422,52,126),(169327,4,201),(203191,48,201),(237055,0,212),(262144,63,37),(262184,36,85),(270352,102,85),(273982,33,132),(304763,8,219),(338621,72,219),(360448,3,55),(361583,1,101),(369400,32,132),(371861,24,101),(372478,0,341),(406334,0,251),(507903,0,257),(524288,66,40),(524608,12,79),(540800,99,79),(547779,38,140),(575435,6,201),(609237,49,201),(643039,1,212),(676838,56,247),(720896,96,79),(725351,36,140),(738288,53,126),(743573,48,109),(744438,0,342),(778239,0,261),(812024,1,251),(913407,1,257),(1014783,0,272),(1048575,0,276),(1048576,58,31),(1053696,14,79),(1073152,143,92),(1081098,30,126),(1113163,7,201),(1146005,51,201),(1178847,2,212),(1211686,64,285),(1343032,2,251),(1441535,2,257),(1441792,142,92),(1447214,28,126),(1467192,68,142),(1473556,54,126),(1507199,0,296),(1540031,24,296),(1572863,0,299),(1605568,82,247),(1605632,15,79),(1611083,4,109),(1631176,31,126),(1637505,39,140),(1638346,26,342),(1703903,26,261),(1769455,0,312),(1802231,26,312),(1835007,0,316),(1900539,26,272),(1966079,26,276),(1998846,0,331),(2031615,0,336),(2064383,26,336),(2064744,29,126),(2065483,5,201),(2066581,50,201),(2067679,3,212),(2068774,80,247),(2069509,37,140),(2069870,24,342),(2072063,24,261),(2073144,3,251),(2076415,3,257),(2078591,24,272),(2080767,24,276),(2081728,66,285),(2086895,1,312),(2087927,25,312),(2088959,1,316),(2089104,55,126),(2091003,1,296),(2092029,25,296),(2093055,1,299),(2094078,1,331),(2095103,1,336),(2096127,25,336),(2096128,58,247),(2096276,2,342),(2096351,2,261),(2096495,2,312),(2096567,24,312),(2096639,2,316),(2096829,2,272),(2096895,2,276),(2096958,2,331),(2097023,2,336),(2097087,24,336),(2097099,3,312),(2097109,27,312),(2097119,3,316),(2097135,0,338),(2097143,24,338),(2097144,3,331),(2097147,3,336),(2097149,27,336)]),(372479,[(1080395,0,343),(1113163,0,317),(2064459,1,343),(2065483,1,317),(2096128,0,321)]),(372479,[(338621,0,319),(2066581,0,322),(2073144,8,322)]),(744439,[(1343032,105,320),(2073144,106,320),(2096128,58,323)]),(372479,[(812024,62,300),(1343032,105,266),(1605568,82,266),(2073144,113,301),(2081728,66,301),(2096128,58,325),(2097144,0,344)]),(372479,[(676838,56,287),(1211686,64,289),(1605568,90,289),(2068774,88,289),(2081728,66,289),(2096128,58,328)]),(372479,[(1605568,90,324),(2081728,66,324),(2096128,58,331)]),(372479,[(406334,60,259),(676838,56,263),(812024,107,303),(1211686,64,288),(1343032,105,264),(1605568,82,253),(1998846,0,345),(2068774,80,293),(2073144,113,310),(2081728,131,307),(2094078,0,346),(2096128,59,269),(2096958,0,347),(2097144,83,347),(2097150,0,348)]),(372479,[(338621,72,255),(609237,98,265),(812024,137,306),(1146005,121,306),(1343032,105,265),(1605568,86,255),(2066581,97,304),(2073144,113,304),(2081728,118,304),(2092029,76,346),(2096128,110,304),(2096829,72,346),(2097109,86,346),(2097144,94,346),(2097149,0,349)]),(372479,[(812024,137,309),(1343032,105,267),(1605568,82,274),(2073144,113,312),(2081728,66,330),(2096128,58,326),(2097144,0,350)]),(372479,[(676838,56,290),(1211686,64,290),(1605568,82,297),(2068774,80,296),(2081728,66,329),(2096128,58,329)]),(372479,[(575435,13,302),(1113163,17,302),(1605568,82,313),(2065483,29,272),(2081728,130,327),(2096128,134,327),(2097099,0,351)]),(372479,[(203191,52,260),(338621,72,256),(406334,60,260),(609237,53,268),(676838,56,291),(812024,71,268),(1014783,76,344),(1146005,51,268),(1211686,64,291),(1343032,61,268),(1540031,72,344),(1605568,87,256),(1802231,120,347),(1998846,136,347),(2064383,0,351),(2066581,55,291),(2068774,80,292),(2073144,63,291),(2081728,67,260),(2087927,96,346),(2092029,131,347),(2094078,118,346),(2096127,76,350),(2096128,59,260),(2096567,110,346),(2096829,135,347),(2096958,112,346),(2097087,72,350),(2097109,87,344),(2097143,87,350),(2097144,95,344),(2097149,15,351),(2097150,95,350)]),(372479,[(406334,60,261),(676838,56,294),(812024,137,311),(1211686,64,295),(1343032,61,271),(1605568,83,275),(1998846,136,348),(2068774,80,294),(2073144,113,311),(2081728,67,315),(2094078,32,349),(2096128,59,275),(2096958,112,348),(2097144,115,351),(2097150,0,352)]),(372479,[(338621,72,257),(609237,53,270),(812024,137,308),(1146005,121,308),(1343032,61,270),(1605568,86,298),(2066581,97,305),(2073144,113,305),(2081728,118,314),(2092029,76,348),(2096128,110,314),(2096829,72,348),(2097109,111,350),(2097144,119,350),(2097149,72,352)]),(372479,[(2065483,0,339)]),(744439,[(2073144,63,342)]),(744439,[(338621,72,341)]),(372479,[(1605568,82,332),(2081728,66,336),(2096128,58,336)]),(372479,[(1146005,51,337),(2066581,50,338),(2096128,58,338)]),(372479,[(812024,62,316),(1343032,61,333),(1605568,86,333),(2073144,113,335),(2081728,66,335),(2096128,58,276),(2097144,115,352)]),(372479,[(676838,56,299),(1211686,64,334),(1605568,90,334),(2068774,88,334),(2081728,66,334),(2096128,58,299)])]
def F2 : ℕ → Bool := rowAt L2 E2 L3
def E3 : Array (G × List Link) := #[(744439,[]),(744439,[]),(744439,[(1605568,0,0),(2081728,0,1),(2096128,24,0)]),(1474366,[(1343032,26,0),(2073144,25,0),(2096128,0,2)]),(744439,[(812024,1,1),(2073144,3,1),(2081728,0,3)]),(744439,[]),(744439,[]),(744439,[]),(744439,[(1605568,0,4),(2081728,0,5),(2096128,0,6)]),(372479,[(1343032,0,7),(2073144,0,8),(2096128,0,9)]),(372479,[(1146005,0,10),(2066581,25,7),(2096128,0,11)]),(372479,[(812024,0,10),(2073144,0,12),(2081728,0,13)]),(372479,[(609237,0,7),(2066581,25,8),(2081728,0,14)]),(372479,[(338621,0,4),(2066581,25,9),(2073144,0,15)]),(372479,[(609237,0,8),(1146005,0,12),(1605568,0,15)]),(372479,[(338621,0,5),(1146005,0,13),(1343032,0,14)]),(372479,[]),(372479,[(338621,0,6),(609237,0,9),(812024,0,11)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(1474366,[(1146005,26,4),(2066581,25,4),(2096128,0,16)]),(744439,[(609237,27,5),(2066581,25,5),(2081728,0,17)]),(744439,[(203191,24,6),(2066581,25,6),(2068774,0,18)]),(744439,[]),(744439,[]),(372479,[(101599,0,0),(2065483,3,15),(2066581,25,11)]),(372479,[]),(372479,[(101599,0,1),(1113163,2,14),(1146005,26,14)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[(101599,0,2),(304763,0,16),(338621,24,18)]),(372479,[]),(372479,[]),(372479,[]),(372479,[(101599,0,3),(304763,0,17),(338621,24,17)]),(372479,[]),(372479,[]),(744439,[]),(744439,[(541670,0,19),(1080358,0,20),(1605568,0,21),(2064422,24,19),(2081728,0,22),(2096128,24,21)]),(744439,[(406334,0,19)]),(1474366,[(1343032,0,23),(2073144,0,24),(2096128,0,25)]),(744439,[(1211686,0,26),(2068774,24,24),(2096128,0,27)]),(744439,[(406334,0,20)]),(744439,[(812024,0,26),(2073144,24,26),(2081728,0,28)]),(744439,[(676838,0,23),(2068774,24,23),(2081728,0,29)]),(744439,[(406334,0,21),(2068774,24,25),(2073144,24,27)]),(744439,[]),(744439,[(406334,0,22),(1211686,0,28),(1343032,0,29)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(372479,[(338621,76,19)]),(372479,[(1343032,0,30),(2073144,0,31),(2096128,0,32)]),(372479,[(1146005,0,33),(2066581,0,34),(2096128,0,35)]),(372479,[(338621,72,22),(2066581,0,36),(2073144,8,36)]),(372479,[(338621,72,20)]),(372479,[(812024,0,34),(1343032,8,31),(1605568,0,36)]),(372479,[(338621,76,21),(1146005,8,35),(1343032,8,32)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[(406334,76,34),(2068774,0,37),(2073144,0,38)]),(372479,[(338621,72,24),(2066581,0,39),(2073144,32,37)]),(372479,[(203191,72,31),(2066581,0,40),(2068774,0,41)]),(372479,[]),(372479,[(406334,32,33),(1211686,0,39),(1343032,0,40)]),(372479,[(338621,76,26),(1146005,0,37),(1343032,0,41)]),(372479,[(203191,24,36),(338621,76,27),(406334,76,35)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[(304763,8,23),(2065483,0,42),(2073144,32,41)]),(372479,[(169327,0,30),(2065483,0,43),(2068774,72,42)]),(372479,[]),(372479,[(169327,0,32),(304763,8,29),(406334,76,32)]),(372479,[]),(372479,[]),(372479,[]),(372479,[(101599,0,25),(304763,8,28),(338621,76,25)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[(1605568,0,44),(2081728,0,45),(2096128,0,46)]),(1474366,[(1343032,0,47),(2073144,3,46),(2096128,0,48)]),(744439,[(1211686,0,49),(2068774,0,50),(2096128,3,47)]),(744439,[(812024,0,49),(2073144,3,45),(2081728,0,51)]),(744439,[(406334,0,44),(2068774,0,52),(2073144,3,44)]),(744439,[]),(744439,[(812024,0,50),(1343032,3,50),(1605568,0,52)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(1605568,0,53),(2081728,0,54),(2096128,8,54)]),(372479,[(1343032,0,55),(2073144,0,56),(2096128,13,56)]),(372479,[(1146005,0,57),(2066581,0,58),(2096128,17,58)]),(372479,[(812024,0,58),(1343032,8,56),(1605568,13,54)]),(372479,[]),(372479,[]),(744439,[(1605568,0,59),(2081728,0,60),(2096128,8,60)]),(372479,[(1343032,0,61),(2073144,0,62),(2096128,13,62)]),(372479,[(1146005,0,63),(2066581,0,64),(2096128,17,64)]),(372479,[(812024,0,64),(1343032,8,62),(1605568,13,60)]),(372479,[]),(372479,[]),(372479,[(1113163,17,49),(2065483,11,56),(2076363,11,62),(2096128,0,65)]),(372479,[(575435,13,47),(2065483,3,58),(2076363,3,64),(2081728,19,65)]),(372479,[(304763,8,44),(2065483,15,54),(2073144,0,66),(2076363,15,60)]),(372479,[]),(372479,[(575435,13,48),(1113163,15,51),(1605568,0,66)]),(372479,[(304763,8,46),(1113163,15,45),(1343032,19,65)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[(169327,0,53),(180207,0,59),(2065483,3,53),(2068774,0,67),(2076363,3,59),(2080751,0,68)]),(744439,[]),(744439,[(575435,13,52),(1113163,15,52),(1605568,0,67)]),(744439,[(1605568,0,68)]),(744439,[]),(744439,[]),(372479,[(169327,0,55),(180207,0,61),(2065483,3,57),(2068774,0,69),(2076363,3,63),(2080751,0,70)]),(372479,[]),(372479,[]),(372479,[(304763,11,50),(1113163,15,50),(1343032,0,69)]),(372479,[]),(372479,[(1343032,0,70)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(1474366,[(1605568,0,71),(2081728,0,72),(2096128,0,73)]),(372479,[]),(372479,[(1343032,0,74),(2073144,0,75),(2096128,4,74)]),(372479,[(1113163,0,76),(2065483,4,72),(2096128,0,77)]),(372479,[]),(372479,[(812024,0,76),(2073144,0,78),(2081728,4,76)]),(372479,[(575435,0,74),(2065483,4,73),(2081728,4,77)]),(372479,[(304763,0,71),(2065483,4,71),(2073144,0,79)]),(372479,[]),(372479,[(575435,0,75),(1113163,0,78),(1605568,0,79)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[]),(744439,[(1605568,0,80),(2081728,0,81),(2096128,8,81)]),(1474366,[(1113163,9,81),(2065483,11,81),(2096128,0,82)]),(744439,[(169327,0,80),(2065483,3,80),(2068774,0,83)]),(744439,[]),(744439,[]),(1474366,[(1080947,0,84),(1605568,0,85),(2065011,76,84),(2081728,76,85),(2096128,0,86)]),(1474366,[(1080947,0,87),(1146005,0,88),(2065011,1,87),(2066581,1,88),(2096128,0,89),(2096887,0,90)]),(744439,[(203191,0,84),(609237,77,84),(676838,0,87)]),(744439,[(676838,0,88),(2068774,0,91),(2081728,77,91)]),(744439,[(609237,77,85),(2066581,76,91),(2081728,0,92)]),(744439,[]),(744439,[(203191,0,86),(609237,1,86),(676838,0,89)]),(744439,[]),(744439,[(676838,0,90)]),(744439,[]),(744439,[(1605568,0,93),(2081728,0,94),(2096128,8,94)]),(372479,[(1343032,0,95),(2073144,0,96),(2096128,0,97)]),(372479,[(1146005,0,98),(2066581,0,99),(2096128,0,100)]),(372479,[(338621,0,93),(2066581,0,101),(2073144,8,101)]),(372479,[(812024,0,99),(1343032,8,96),(1605568,0,101)]),(372479,[(338621,0,94),(1146005,8,100),(1343032,8,97)]),(372479,[]),(372479,[]),(372479,[]),(1474366,[(812024,0,102),(1343032,0,103),(1605568,48,103),(2073144,24,102),(2081728,4,102),(2096128,4,103),(2097144,0,104)]),(744439,[(406334,0,105),(676838,0,106),(812024,0,107),(1211686,0,108),(1343032,0,109),(1605568,0,110),(1998846,0,111),(2068774,0,112),(2073144,78,109),(2081728,0,113),(2094078,0,114),(2096128,0,115),(2096958,0,116),(2097144,0,117),(2097150,0,118)]),(744439,[(338621,0,105),(609237,0,119),(812024,0,120),(1146005,0,121),(1343032,60,106),(1605568,0,122),(2066581,0,123),(2073144,36,119),(2081728,0,124),(2092029,0,125),(2096128,0,126),(2096829,0,127),(2097109,0,128),(2097144,0,129),(2097149,0,130)]),(744439,[(203191,0,102),(338621,0,107),(406334,0,120),(609237,27,123),(676838,56,121),(879613,0,131),(947198,0,132),(1014783,0,133),(1146005,0,134),(1211686,0,135),(1343032,0,136),(1540031,0,137),(1605568,90,136),(1802231,0,138),(1867768,0,139),(1998846,0,140),(2064383,0,141),(2066581,4,124),(2068774,4,113),(2073144,0,142),(2081728,0,143),(2087927,0,144),(2092029,0,145),(2094078,0,146),(2096127,0,147),(2096128,0,148),(2096567,0,149),(2096829,0,150),(2096958,0,151),(2097087,0,152),(2097109,0,153),(2097143,0,154),(2097144,0,155),(2097149,0,156),(2097150,0,157)]),(744439,[(812024,0,133),(1343032,0,158),(1605568,0,159),(2073144,0,160),(2081728,4,144),(2096128,0,161),(2097144,0,162)]),(744439,[(406334,0,121),(676838,56,120),(812024,0,134),(1211686,0,163),(1343032,26,121),(1605568,82,120),(1998846,0,164),(2068774,4,108),(2073144,0,165),(2081728,4,135),(2094078,0,166),(2096128,51,108),(2096958,0,167),(2097144,26,166),(2097150,0,168)]),(744439,[(203191,0,103),(338621,0,109),(406334,60,106),(609237,49,124),(676838,56,122),(812024,0,136),(1014783,0,158),(1146005,26,121),(1211686,64,108),(1408701,0,169),(1540031,0,170),(1605568,0,171),(1802231,0,172),(1867768,0,173),(1998846,0,174),(2064383,0,175),(2066581,4,126),(2068774,4,115),(2073144,138,171),(2081728,4,148),(2087927,4,161),(2092029,0,176),(2094078,0,177),(2096127,0,178),(2096128,0,179),(2096567,0,180),(2096696,0,181),(2096829,0,182),(2096958,0,183),(2097087,0,184),(2097109,0,185),(2097143,0,186),(2097144,0,187),(2097149,0,188),(2097150,0,189)]),(744439,[(812024,0,137),(1343032,0,170),(1605568,0,190),(2073144,0,191),(2081728,4,149),(2096128,4,180),(2097144,0,192)]),(744439,[(203191,48,103),(338621,0,110),(406334,0,122),(609237,49,119),(676838,56,119),(812024,90,136),(1014783,0,159),(1146005,82,120),(1211686,86,120),(1343032,0,171),(1540031,0,190),(1671125,0,193),(1736678,4,193),(1802231,0,194),(1867768,0,195),(1998846,0,196),(2064383,0,197),(2066581,4,122),(2068774,4,110),(2073144,0,198),(2081728,87,136),(2087927,4,159),(2092029,0,199),(2094078,4,199),(2096127,0,200),(2096128,4,171),(2096567,4,190),(2096829,0,201),(2096958,4,201),(2097087,0,202),(2097088,4,195),(2097109,4,196),(2097143,4,197),(2097144,0,203),(2097149,0,204),(2097150,4,204)]),(744439,[(812024,0,138),(1343032,0,172),(1605568,0,194),(2073144,0,205),(2081728,4,138),(2096128,4,172),(2097144,0,206)]),(744439,[(338621,0,111),(609237,49,125),(812024,0,140),(1146005,0,164),(1343032,0,174),(1605568,0,196),(2066581,4,128),(2073144,0,207),(2081728,4,153),(2092029,0,208),(2096128,4,185),(2096829,0,209),(2097109,0,210),(2097144,0,211),(2097149,0,212)]),(744439,[(812024,0,141),(1343032,0,175),(1605568,0,197),(2073144,0,213),(2081728,4,154),(2096128,4,186),(2097144,0,214)]),(744439,[(203191,24,102),(338621,78,109),(406334,36,119),(609237,49,126),(676838,56,126),(812024,0,142),(1014783,0,160),(1146005,0,165),(1211686,4,165),(1343032,138,171),(1540031,0,191),(1605568,0,198),(1802231,0,205),(1998846,0,207),(2064383,0,213),(2066581,25,119),(2068774,89,109),(2075325,0,215),(2077502,4,215),(2081728,4,142),(2087927,4,160),(2092029,0,216),(2094078,4,216),(2096127,0,217),(2096128,134,171),(2096567,4,191),(2096696,0,218),(2096829,0,219),(2096958,4,219),(2097087,0,220),(2097109,4,207),(2097143,4,213),(2097144,0,221),(2097149,0,222),(2097150,4,222)]),(744439,[(406334,0,125),(676838,56,127),(812024,0,145),(1211686,4,166),(1343032,0,176),(1605568,0,199),(1998846,0,208),(2068774,4,114),(2073144,0,216),(2081728,4,146),(2094078,0,223),(2096128,4,177),(2096958,0,224),(2097144,0,225),(2097150,0,226)]),(744439,[(812024,0,147),(1343032,0,178),(1605568,0,200),(2073144,0,217),(2081728,4,147),(2096128,4,178),(2097144,0,227)]),(744439,[(406334,0,127),(676838,56,129),(812024,0,150),(1211686,4,167),(1343032,0,182),(1605568,0,201),(1998846,0,209),(2068774,4,116),(2073144,0,219),(2081728,4,151),(2094078,4,224),(2096128,4,183),(2096958,0,228),(2097144,0,229),(2097150,0,230)]),(744439,[(812024,0,152),(1343032,0,184),(1605568,0,202),(2073144,0,220),(2081728,4,152),(2096128,4,184),(2097144,0,231)]),(744439,[(203191,0,104),(338621,0,117),(406334,0,129),(609237,49,128),(676838,56,128),(812024,0,155),(1014783,0,162),(1146005,26,166),(1211686,40,166),(1343032,0,187),(1474360,0,232),(1540031,0,192),(1605568,0,203),(1802231,0,206),(1998846,0,211),(2064383,0,214),(2066581,4,129),(2068774,4,117),(2073144,0,221),(2081728,4,155),(2087927,4,162),(2092029,0,225),(2094078,4,225),(2096127,0,227),(2096128,4,187),(2096272,4,232),(2096567,4,192),(2096829,0,229),(2096958,4,229),(2097087,0,231),(2097109,4,211),(2097143,4,214),(2097149,0,233),(2097150,4,233)]),(744439,[(406334,0,130),(676838,56,130),(812024,0,156),(1211686,4,168),(1343032,0,188),(1605568,0,204),(1998846,0,212),(2068774,4,118),(2073144,0,222),(2081728,4,157),(2094078,4,226),(2096128,4,189),(2096958,4,230),(2097144,0,233),(2097150,0,234)]),(744439,[(812024,136,193),(1343032,0,235),(1605568,0,236),(2073144,112,193),(2081728,0,237),(2096128,24,236),(2097144,0,238)]),(1474366,[(812024,133,169),(1343032,0,239),(1605568,157,215),(2073144,0,240),(2081728,109,131),(2096128,0,241),(2097144,0,242)]),(744439,[(406334,136,193),(676838,133,169),(947198,0,243),(1211686,0,244),(1343032,114,195),(1605568,90,173),(1867768,0,245),(1998846,0,246),(2068774,24,240),(2073144,0,247),(2081728,0,248),(2094078,0,249),(2096128,0,250),(2096958,0,251),(2097144,0,252),(2097150,0,253)]),(744439,[(812024,0,244),(1343032,0,254),(1605568,86,132),(2073144,24,244),(2081728,0,255),(2096128,110,132),(2097144,0,256)]),(744439,[(406334,0,235),(676838,0,239),(812024,114,195),(1211686,0,254),(1605568,91,181),(1867768,0,257),(1998846,0,258),(2068774,24,239),(2073144,138,195),(2081728,0,259),(2094078,0,260),(2096128,135,181),(2096696,24,257),(2096958,24,258),(2097144,0,261),(2097150,0,262)]),(744439,[(406334,0,236),(676838,157,215),(812024,90,173),(1211686,86,132),(1343032,91,181),(1736678,86,243),(1867768,90,257),(1998846,0,263),(2068774,24,241),(2073144,24,250),(2081728,87,139),(2094078,0,264),(2096128,95,218),(2096958,0,265),(2097088,87,245),(2097144,0,266),(2097150,0,267)]),(744439,[(812024,0,246),(1343032,0,258),(1605568,0,263),(2073144,24,251),(2081728,0,268),(2096128,24,265),(2097144,0,269)]),(744439,[(406334,0,237),(676838,109,131),(812024,0,248),(1211686,0,255),(1343032,0,259),(1605568,87,139),(1998846,0,268),(2068774,85,131),(2073144,24,248),(2085862,0,270),(2094078,0,271),(2096128,111,139),(2096958,24,268),(2097088,0,272),(2097144,0,273),(2097150,0,274)]),(744439,[(812024,0,249),(1343032,0,260),(1605568,0,264),(2073144,24,249),(2081728,0,271),(2096128,24,264),(2097144,0,275)]),(744439,[(406334,0,238),(676838,0,242),(812024,0,252),(1211686,0,256),(1343032,0,261),(1474360,0,276),(1605568,0,266),(1998846,0,269),(2068774,24,242),(2073144,24,252),(2081728,0,273),(2094078,0,275),(2096128,24,266),(2096958,24,269),(2097150,0,277)]),(744439,[(812024,0,253),(1343032,0,262),(1605568,0,267),(2073144,24,253),(2081728,0,274),(2096128,24,267),(2097144,0,277)]),(744439,[(676838,0,278),(1211686,8,278),(1605568,26,278),(2068774,24,278),(2081728,10,278),(2096128,2,278)]),(1474366,[(203191,24,112),(338621,0,278),(406334,32,108),(609237,27,112),(812024,34,108),(947198,132,254),(1014783,0,279),(1146005,26,110),(1211686,108,143),(1343032,35,113),(1540031,0,280),(1605568,94,142),(1736678,108,248),(1802231,0,281),(1998846,0,282),(2064383,0,283),(2066581,25,110),(2068774,92,142),(2073144,33,113),(2081728,109,143),(2085862,109,248),(2087927,1,281),(2092029,1,280),(2094078,1,282),(2096127,1,283),(2096128,0,284),(2096567,0,285),(2096829,0,286),(2096958,0,287),(2097087,0,288),(2097109,1,285),(2097143,0,289),(2097144,1,287),(2097149,1,288),(2097150,0,290)]),(744439,[(676838,0,279),(1211686,8,280),(1605568,0,291),(2068774,1,291),(2081728,10,280),(2096128,2,286)]),(744439,[(203191,24,115),(338621,26,278),(406334,32,115),(609237,27,106),(676838,94,142),(812024,34,106),(1014783,0,291),(1146005,26,106),(1211686,86,142),(1343032,35,106),(1540031,8,291),(1671125,82,235),(1736678,86,247),(1802231,0,292),(1867768,90,235),(1998846,8,292),(2064383,0,293),(2066581,25,115),(2068774,0,294),(2073144,33,115),(2081728,87,142),(2087927,0,295),(2092029,11,291),(2094078,11,295),(2096127,0,296),(2096128,95,142),(2096567,3,295),(2096829,3,291),(2096958,8,295),(2097087,3,296),(2097088,87,247),(2097109,3,292),(2097143,0,297),(2097144,11,292),(2097149,3,293),(2097150,8,297)]),(744439,[(406334,32,116),(676838,0,281),(812024,34,111),(1211686,8,282),(1343032,35,114),(1605568,0,292),(1998846,0,298),(2068774,1,295),(2073144,33,117),(2081728,10,287),(2094078,0,299),(2096128,2,285),(2096958,9,299),(2097144,0,300),(2097150,0,301)]),(744439,[(676838,0,283),(1211686,8,283),(1605568,0,293),(2068774,1,296),(2081728,10,288),(2096128,2,288)]),(744439,[(406334,32,118),(676838,0,289),(812024,34,118),(1211686,8,290),(1343032,35,118),(1605568,0,297),(1998846,8,301),(2068774,1,297),(2073144,33,118),(2081728,10,290),(2094078,10,301),(2096128,2,289),(2096958,9,301),(2097144,11,301),(2097150,0,302)]),(744439,[(541662,0,303),(1605568,0,304),(2064414,24,303),(2081728,0,305),(2096128,24,304)]),(744439,[(1605568,0,306),(2081728,0,307),(2096128,24,306)]),(744439,[(812024,136,194),(1343032,136,292),(1605568,0,308),(2073144,113,196),(2081728,0,309),(2096128,0,310),(2097144,0,311)]),(744439,[(676838,132,170),(1211686,60,281),(1605568,0,312),(2068774,88,174),(2081728,0,313),(2096128,0,314)]),(744439,[(575435,1,133),(1113163,2,182),(1605568,136,308),(2065483,3,219),(2081728,0,315),(2096128,0,316),(2097099,0,317)]),(744439,[(1605568,0,318),(2081728,0,319),(2096128,0,320)]),(744439,[(676838,132,183),(1211686,60,279),(1605568,0,321),(2068774,88,183),(2081728,0,322),(2096128,24,321)]),(744439,[(609237,27,216),(1146005,26,170),(1605568,136,321),(2066581,25,145),(2081728,0,323),(2096128,112,312),(2097109,0,324)]),(744439,[(1605568,0,325),(2081728,0,326),(2096128,24,325)]),(744439,[(1,0,0),(2,36,9),(4,100,8),(6,52,74),(8,32,6),(10,8,71),(16,76,5),(20,72,72),(24,76,81),(30,0,304),(32,136,0),(38,0,21),(64,6,5),(67,49,31),(128,49,8),(192,31,72),(256,157,8),(512,167,9),(560,100,31),(704,27,24),(768,133,74),(1024,7,6),(1034,60,23),(1088,6,81),(2048,51,9),(2068,104,24),(2176,98,74),(2177,82,21),(3072,30,71),(3102,8,85),(3264,82,304),(4096,161,5),(4352,116,72),(4354,94,24),(8192,166,6),(8704,114,71),(8712,90,23),(11264,26,23),(11968,30,85),(12288,161,81),(13056,136,304),(13066,114,85),(16384,82,0),(17152,136,21),(22528,157,31),(32768,5,15),(32840,70,41),(33793,51,32),(36043,6,94),(44747,0,44),(65536,50,14),(65541,4,36),(65680,154,37),(67799,49,96),(68343,26,47),(98304,29,77),(98520,10,91),(99407,4,101),(101525,51,97),(131072,88,14),(131360,137,36),(135172,125,37),(135990,100,96),(154422,60,47),(169327,0,122),(203191,24,126),(237055,0,236),(262144,113,15),(262184,36,32),(270352,135,41),(270910,76,94),(273982,136,44),(304763,32,115),(338621,76,113),(360448,25,27),(361583,1,50),(369400,76,54),(371861,24,46),(393216,165,77),(397614,36,97),(402232,137,101),(405524,153,91),(440191,60,239),(474047,104,240),(507903,0,306),(524288,163,14),(524608,12,37),(540800,151,36),(547776,157,96),(547779,90,47),(575435,6,113),(609237,83,126),(643039,27,240),(676838,140,126),(720896,96,38),(725351,100,56),(738288,157,56),(743573,49,56),(778239,0,308),(812024,136,122),(913407,0,312),(947198,136,236),(1014783,136,308),(1048575,0,318),(1048576,159,15),(1053696,14,41),(1073152,167,32),(1081088,161,94),(1081098,82,44),(1113163,7,115),(1146005,82,122),(1178847,26,239),(1211686,161,113),(1343032,166,115),(1441535,0,321),(1441792,164,27),(1447214,140,46),(1467192,152,50),(1473556,161,54),(1507199,136,321),(1540031,136,312),(1572863,0,325),(1572864,111,77),(1578304,41,91),(1598400,167,97),(1604736,151,101),(1605632,87,27),(1611083,6,54),(1631176,83,46),(1637505,86,50),(1671125,82,236),(1703903,82,306),(1736678,94,240),(1769455,82,312),(1802231,82,308),(1835007,82,318),(1867768,90,239),(1900539,82,321),(1966079,82,325),(1998846,136,306),(2031615,136,325),(2064383,136,318),(2064744,29,65),(2065483,3,198),(2066581,25,148),(2067679,25,250),(2068774,164,148),(2069509,111,65),(2072063,24,310),(2073144,112,198),(2076415,24,314),(2077502,164,250),(2078591,24,316),(2080767,24,320),(2081728,87,148),(2086895,0,327),(2087927,0,328),(2088959,0,329),(2089104,165,65),(2091003,0,330),(2092029,136,327),(2093055,0,331),(2094078,140,310),(2095103,0,332),(2096127,136,329),(2096128,95,198),(2096351,83,316),(2096495,82,330),(2096567,82,327),(2096639,82,332),(2096829,136,330),(2096895,0,333),(2096958,140,314),(2097023,136,333),(2097087,136,331),(2097088,87,250),(2097099,83,314),(2097109,83,310),(2097119,83,320),(2097135,82,331),(2097143,82,329),(2097144,140,316),(2097147,82,333),(2097149,136,332),(2097150,140,320)]),(744439,[(676838,132,182),(812024,136,196),(947198,136,263),(1211686,60,282),(1343032,114,292),(1605568,82,306),(1998846,0,334),(2068774,88,187),(2073144,112,203),(2077502,112,266),(2081728,0,335),(2094078,0,336),(2096128,59,316),(2096958,0,337),(2097144,0,338),(2097150,0,339)]),(744439,[(338621,76,114),(609237,49,160),(812024,136,190),(1146005,26,172),(1343032,114,291),(1605568,82,312),(2066581,25,153),(2073144,112,199),(2081728,0,340),(2092029,0,341),(2096128,58,327),(2096829,0,342),(2097109,0,343),(2097144,0,344),(2097149,0,345)]),(744439,[(304763,32,116),(575435,1,144),(812024,136,159),(1113163,2,180),(1343032,136,291),(1605568,82,308),(1900539,0,346),(2065483,5,207),(2073144,112,201),(2081728,0,347),(2091003,0,348),(2096128,58,330),(2097099,0,349),(2097144,0,350),(2097147,0,351)]),(744439,[(812024,136,197),(1343032,114,293),(1605568,82,318),(2073144,112,204),(2081728,0,352),(2096128,58,332),(2097144,0,353)]),(744439,[(203191,24,127),(609237,27,160),(676838,132,180),(1146005,26,158),(1211686,60,280),(1605568,82,321),(1802231,0,346),(2066581,25,150),(2068774,88,177),(2081728,0,354),(2087927,0,355),(2096128,112,330),(2096567,24,342),(2097109,0,356),(2097143,0,357)]),(744439,[(676838,132,184),(1211686,60,283),(1605568,82,325),(2068774,88,189),(2081728,0,358),(2096128,24,333)]),(744439,[(575435,1,146),(609237,49,216),(643039,1,249),(1113163,2,183),(1146005,26,174),(1178847,26,258),(1605568,136,306),(1703903,0,334),(2065483,3,221),(2066581,25,155),(2067679,25,252),(2081728,118,323),(2096128,164,314),(2096351,24,337),(2097099,0,359),(2097109,0,360),(2097119,0,361)]),(744439,[(609237,27,217),(1146005,26,175),(1605568,136,325),(2066581,25,156),(2081728,0,362),(2096128,112,331),(2097109,0,363)]),(744439,[(575435,1,147),(1113163,2,184),(1605568,136,318),(2065483,3,222),(2081728,0,364),(2096128,112,333),(2097099,0,365)]),(744439,[(1,0,1),(2,36,7),(4,100,7),(6,28,75),(8,32,4),(10,8,73),(16,76,4),(20,72,73),(24,32,80),(30,0,305),(32,60,2),(38,0,22),(64,6,13),(67,48,34),(128,49,12),(192,53,76),(256,132,7),(512,137,4),(560,100,30),(704,1,26),(768,141,73),(1024,7,11),(1034,60,25),(2048,51,11),(2068,104,25),(2177,7,35),(3072,30,79),(3102,8,86),(4096,64,17),(4354,13,39),(8192,69,18),(8712,23,42),(11264,2,29),(12288,61,82),(13066,64,92),(16384,87,11),(17152,140,25),(22528,98,40),(32768,5,12),(32832,18,76),(32840,66,26),(33793,51,35),(36043,7,100),(44747,0,45),(65536,50,13),(65541,4,34),(65664,122,76),(65680,130,26),(67799,48,99),(68343,25,49),(98304,29,76),(98496,4,366),(98520,10,88),(99407,4,99),(101525,51,100),(131072,88,7),(131328,92,75),(131360,118,22),(135172,97,39),(135990,100,95),(154422,60,48),(169327,0,124),(203191,24,124),(237055,0,237),(262144,113,4),(262184,36,30),(262656,113,80),(270352,102,42),(270910,32,93),(273982,112,52),(304763,32,110),(338621,76,110),(360448,25,26),(361152,62,88),(361583,1,49),(369400,32,53),(371861,24,45),(393216,165,73),(393984,118,305),(397614,36,95),(402232,113,93),(405524,128,92),(440191,60,241),(474047,104,241),(507903,0,307),(524288,118,1),(524608,85,34),(540800,111,35),(547779,109,58),(575435,1,135),(609237,49,165),(643039,1,244),(676838,118,124),(720896,109,34),(725351,36,55),(738240,109,99),(738288,66,49),(743573,48,58),(778239,0,309),(812024,137,110),(913407,0,313),(947198,140,241),(1014783,0,315),(1048575,0,319),(1048576,111,11),(1053696,14,40),(1064960,95,79),(1073152,119,29),(1081098,30,66),(1113163,7,148),(1146005,51,148),(1178847,2,259),(1211686,60,284),(1343032,68,294),(1441535,0,322),(1441792,164,25),(1447214,104,48),(1458944,141,86),(1467192,68,52),(1473556,54,66),(1507199,0,323),(1540031,24,323),(1572863,0,326),(1605568,87,148),(1605632,87,35),(1611083,4,58),(1622976,87,100),(1631176,118,45),(1637505,39,69),(1703903,0,335),(1769455,0,340),(1802231,0,347),(1835007,0,352),(1900539,0,354),(1966079,0,358),(1998846,118,323),(2031615,0,362),(2064383,0,364),(2064704,85,99),(2064744,130,49),(2065483,5,165),(2066581,25,135),(2067679,25,244),(2068774,162,124),(2069509,85,58),(2072063,24,309),(2073144,113,110),(2076415,24,313),(2077502,164,241),(2078591,24,315),(2080767,24,319),(2080896,111,100),(2082763,66,244),(2083797,130,244),(2084831,0,367),(2085862,118,237),(2086895,118,309),(2087927,162,309),(2088959,0,368),(2089104,162,45),(2091003,118,313),(2092029,162,313),(2093055,0,369),(2094078,118,307),(2095103,118,319),(2096127,162,319),(2096128,111,148),(2096351,24,335),(2096495,24,347),(2096567,24,340),(2096639,24,352),(2096829,24,354),(2096895,24,358),(2096958,162,323),(2097023,24,364),(2097087,24,362),(2097088,119,259),(2097099,118,335),(2097109,162,335),(2097119,0,370),(2097135,118,352),(2097143,162,352),(2097144,118,322),(2097147,118,358),(2097149,162,358),(2097150,118,326)]),(744439,[(338621,76,111),(609237,49,191),(812024,137,190),(1146005,26,185),(1343032,112,295),(1605568,0,327),(2066581,25,138),(2073144,113,159),(2081728,118,309),(2092029,0,371),(2096128,24,328),(2096829,24,355),(2097109,0,372),(2097144,0,373),(2097149,0,374)]),(744439,[(812024,137,197),(1343032,112,297),(1605568,0,329),(2073144,113,197),(2081728,0,368),(2096128,24,329),(2097144,0,375)]),(744439,[(203191,24,125),(609237,27,191),(676838,132,172),(1146005,26,176),(1211686,60,285),(1605568,0,330),(1802231,0,348),(2066581,25,137),(2068774,88,158),(2081728,118,313),(2087927,24,371),(2096128,112,327),(2096567,24,341),(2097109,0,376),(2097143,0,377)]),(744439,[(676838,132,175),(1211686,60,289),(1605568,0,331),(2068774,88,175),(2081728,0,369),(2096128,24,331)]),(744439,[(575435,1,140),(609237,49,219),(643039,1,246),(1113163,2,187),(1146005,26,187),(1178847,2,261),(1605568,140,310),(1703903,0,336),(2065483,5,219),(2066581,25,140),(2067679,25,246),(2081728,118,307),(2096128,164,310),(2096351,24,336),(2097099,0,378),(2097109,24,378),(2097119,0,379)]),(744439,[(609237,27,220),(1146005,26,188),(1605568,0,332),(2066581,25,141),(2081728,118,319),(2096128,112,329),(2097109,0,380)]),(744439,[(203191,24,128),(338621,76,117),(474047,104,242),(609237,27,205),(676838,132,185),(812024,137,201),(947198,136,265),(1014783,0,317),(1146005,51,161),(1211686,60,287),(1343032,114,295),(1540031,24,324),(1605568,83,314),(1802231,0,349),(1998846,0,359),(2064383,0,365),(2066581,25,149),(2068774,88,176),(2073144,113,199),(2077502,112,264),(2081728,118,335),(2087927,24,372),(2092029,24,376),(2094078,0,378),(2096127,24,380),(2096128,59,310),(2096567,24,343),(2096829,24,356),(2096958,24,360),(2097087,24,363),(2097109,0,381),(2097143,0,382),(2097144,0,383),(2097149,0,384),(2097150,0,385)]),(744439,[(676838,132,188),(812024,137,204),(947198,136,267),(1211686,60,290),(1343032,114,297),(1605568,83,320),(1998846,0,361),(2068774,88,188),(2073144,113,204),(2077502,112,267),(2081728,0,370),(2094078,0,379),(2096128,59,320),(2096958,24,361),(2097144,0,386),(2097150,0,387)]),(744439,[(338621,76,118),(609237,49,213),(812024,136,202),(1146005,26,186),(1343032,112,296),(1605568,82,331),(2066581,25,154),(2073144,112,200),(2081728,118,352),(2092029,24,377),(2096128,58,329),(2096829,24,357),(2097109,24,382),(2097144,0,388),(2097149,0,389)]),(744439,[(169327,0,129),(203191,24,129),(237055,0,238),(575435,1,151),(609237,27,207),(643039,1,251),(676838,140,161),(778239,0,311),(1113163,2,177),(1146005,26,177),(1178847,2,260),(1211686,60,286),(1605568,140,316),(1703903,0,338),(1769455,0,344),(1802231,0,350),(1835007,0,353),(2065483,3,207),(2066581,25,151),(2067679,25,251),(2068774,164,161),(2072063,24,311),(2081728,118,322),(2086895,0,373),(2087927,24,373),(2088959,0,375),(2096128,164,316),(2096351,24,338),(2096495,24,350),(2096567,24,344),(2096639,24,353),(2097099,0,383),(2097109,24,383),(2097119,0,386),(2097135,0,388),(2097143,24,388)]),(744439,[(203191,24,130),(609237,27,213),(676838,132,186),(1146005,26,178),(1211686,60,288),(1605568,82,333),(1802231,0,351),(2066581,25,152),(2068774,88,178),(2081728,118,358),(2087927,24,374),(2096128,112,332),(2096567,24,345),(2097109,24,384),(2097143,24,389)]),(744439,[(575435,1,157),(609237,49,222),(643039,1,253),(1113163,2,189),(1146005,26,189),(1178847,2,262),(1605568,140,320),(1703903,0,339),(2065483,5,222),(2066581,25,157),(2067679,25,253),(2081728,118,326),(2096128,164,320),(2096351,24,339),(2097099,0,385),(2097109,24,385),(2097119,0,387)]),(744439,[(812024,1,313),(1343032,61,279),(1605568,86,146),(2073144,25,313),(2081728,0,390),(2096128,110,146),(2097144,0,391)]),(744439,[(1605568,82,334),(2081728,0,392),(2096128,58,359)]),(744439,[(406334,0,307),(676838,109,145),(812024,62,281),(1211686,0,390),(1343032,2,322),(1605568,87,155),(1998846,0,392),(2068774,85,145),(2073144,106,281),(2085862,118,271),(2094078,0,393),(2096128,111,155),(2096958,24,392),(2097088,119,273),(2097144,0,394),(2097150,0,395)]),(744439,[(1605568,82,360),(2081728,0,393),(2096128,58,360)]),(744439,[(676838,56,324),(1211686,0,391),(1605568,83,337),(2068774,80,324),(2081728,0,394),(2096128,59,337)]),(744439,[(1605568,82,361),(2081728,0,395),(2096128,58,361)]),(744439,[(812024,1,309),(1343032,105,282),(1605568,86,133),(2073144,25,335),(2081728,0,396),(2096128,110,140),(2097144,0,397)]),(744439,[(1343032,26,334),(2073144,25,338),(2096128,58,378)]),(744439,[(812024,1,311),(1343032,26,337),(1605568,82,317),(2073144,25,336),(2081728,1,397),(2096128,58,336),(2097144,0,398)]),(744439,[(1343032,26,339),(2073144,25,339),(2096128,58,379)]),(744439,[(304763,8,280),(575435,6,144),(812024,1,315),(1113163,7,167),(1343032,105,280),(1605568,86,144),(1900539,0,399),(2065483,5,151),(2073144,25,354),(2081728,0,400),(2091003,0,401),(2096128,110,151),(2097099,0,402),(2097144,129,401),(2097147,0,403)]),(744439,[(1605568,82,346),(2081728,1,401),(2096128,58,344)]),(744439,[(1343032,26,346),(2073144,25,356),(2096128,58,373)]),(744439,[(1211686,0,399),(2068774,81,350),(2096128,59,350)]),(744439,[(1113163,2,228),(2065483,3,229),(2096128,58,383)]),(744439,[(2096128,58,388)]),(744439,[(812024,1,317),(1343032,2,342),(1605568,82,348),(2073144,25,355),(2081728,1,402),(2096128,58,311),(2097144,0,404)]),(744439,[(575435,1,162),(1113163,2,209),(1605568,82,349),(2065483,5,224),(2081728,130,401),(2096128,58,338),(2097099,1,404)]),(744439,[(1605568,82,351),(2081728,1,403),(2096128,58,353)]),(744439,[(1343032,26,357),(2073144,25,357),(2096128,58,375)]),(744439,[(1113163,2,230),(2065483,3,230),(2096128,58,386)]),(744439,[(812024,1,319),(1343032,105,283),(1605568,86,147),(2073144,25,358),(2081728,0,405),(2096128,110,157),(2097144,0,406)]),(744439,[(2096128,58,385)]),(744439,[(1605568,82,365),(2081728,1,406),(2096128,58,339)]),(744439,[(2096128,58,387)]),(372479,[(68093,0,407),(1080680,17,407),(1146005,0,408),(2066581,0,366),(2096128,17,366),(2096637,0,409)]),(744439,[(812024,1,367),(2073144,3,367),(2081728,0,410)]),(744439,[(812024,1,369),(2073144,3,369),(2081728,0,411)]),(744439,[(812024,1,368),(2073144,3,370),(2081728,0,412)]),(744439,[(1,0,3),(2,4,10),(4,48,10),(6,28,78),(8,8,16),(16,72,16),(24,32,83),(32,60,16),(38,0,28),(64,6,10),(67,48,33),(128,49,10),(192,31,78),(256,108,10),(512,62,16),(560,100,43),(704,1,28),(1024,7,10),(1026,16,78),(1034,64,28),(2048,51,10),(2052,120,78),(2068,128,28),(2177,6,33),(3072,30,78),(3078,5,408),(3102,8,89),(4096,64,3),(4354,41,33),(8192,61,16),(8224,68,83),(8712,22,43),(11264,2,28),(11302,60,89),(16384,86,10),(16640,94,78),(17152,116,28),(22528,108,33),(32768,5,10),(32832,18,78),(32840,66,28),(33793,50,33),(36043,6,98),(44747,0,51),(65536,50,10),(65541,4,33),(65664,122,78),(65680,130,28),(67799,48,98),(68343,25,51),(98304,29,78),(98496,4,408),(98520,10,89),(99407,4,98),(101525,50,98),(131072,84,10),(131328,92,78),(131360,118,28),(135172,110,33),(153894,108,98),(154422,64,51),(169327,4,134),(203191,48,134),(237055,0,255),(262144,63,16),(262184,20,43),(262656,70,83),(270352,102,43),(273982,33,67),(304763,8,284),(338621,72,284),(360448,3,28),(361152,62,89),(361583,1,51),(369400,32,67),(371861,24,51),(406334,60,284),(507903,0,390),(524288,66,3),(524608,42,33),(540800,111,33),(547779,43,57),(575435,6,134),(609237,49,134),(643039,1,255),(676838,108,134),(720896,109,33),(725351,40,57),(738240,109,98),(738288,66,51),(743573,48,57),(778239,0,396),(812024,62,284),(913407,1,390),(1014783,0,400),(1048575,0,405),(1048576,110,10),(1053696,40,33),(1064960,95,78),(1073152,119,28),(1080578,41,98),(1081098,117,51),(1113163,7,134),(1146005,51,134),(1178847,2,255),(1179648,93,78),(1185062,40,98),(1196288,40,408),(1204512,140,89),(1211396,110,98),(1244527,64,255),(1277367,128,255),(1310207,0,410),(1343032,61,284),(1441535,2,390),(1441792,117,28),(1447214,116,51),(1458944,141,89),(1467192,68,67),(1473556,65,51),(1507199,64,390),(1540031,128,390),(1572863,0,411),(1605568,86,134),(1605632,43,33),(1611083,4,57),(1622976,43,98),(1631176,118,51),(1637505,41,57),(1703903,26,396),(1736678,116,255),(1769455,64,396),(1802231,129,396),(1835007,0,412),(1900539,26,400),(1966079,26,405),(1998846,116,390),(2031615,64,405),(2064383,129,405),(2064704,42,98),(2064744,119,51),(2065483,5,134),(2066581,50,134),(2067679,3,255),(2068774,84,134),(2069509,42,57),(2072063,24,396),(2073144,63,284),(2076415,3,390),(2078591,24,400),(2080767,24,405),(2080896,111,98),(2082763,66,255),(2083797,130,255),(2084831,1,410),(2085862,118,255),(2086895,66,396),(2087927,130,396),(2088959,1,412),(2089104,67,51),(2091003,66,390),(2092029,130,390),(2093055,1,411),(2094078,118,390),(2095103,66,405),(2096127,130,405),(2096128,110,134),(2096351,2,396),(2096422,117,255),(2096495,65,396),(2096567,128,396),(2096639,2,412),(2096829,2,400),(2096895,2,405),(2096958,117,390),(2097023,65,405),(2097087,128,405),(2097088,119,255),(2097099,67,396),(2097109,131,396),(2097119,3,412),(2097126,116,410),(2097135,116,412),(2097143,160,412),(2097144,119,390),(2097147,67,405),(2097149,131,405),(2097150,116,411)]),(744439,[(338621,72,287),(609237,49,137),(812024,1,340),(1146005,51,164),(1343032,61,287),(1605568,86,137),(2066581,50,138),(2073144,25,347),(2081728,66,396),(2092029,0,413),(2096128,110,138),(2096829,2,402),(2097109,0,414),(2097144,64,413),(2097149,0,415)]),(744439,[(812024,1,352),(1343032,61,290),(1605568,86,141),(2073144,25,352),(2081728,1,412),(2096128,110,141),(2097144,0,416)]),(744439,[(203191,48,166),(338621,72,286),(406334,60,285),(609237,49,149),(676838,108,153),(812024,1,323),(1014783,0,401),(1146005,51,166),(1277367,128,256),(1343032,61,285),(1540031,128,391),(1605568,86,150),(1736678,116,268),(1802231,129,397),(1998846,116,392),(2064383,129,406),(2066581,50,149),(2068774,84,150),(2073144,3,323),(2081728,66,390),(2087927,24,413),(2092029,0,417),(2094078,0,418),(2096127,0,419),(2096128,110,153),(2096422,117,268),(2096567,128,397),(2096829,2,401),(2096958,117,392),(2097087,128,406),(2097109,26,413),(2097143,128,416),(2097144,2,418),(2097149,2,419),(2097150,0,420)]),(744439,[(406334,60,289),(676838,108,156),(812024,1,326),(1343032,61,289),(1605568,86,156),(1736678,116,274),(1998846,116,395),(2068774,84,156),(2073144,3,326),(2081728,1,411),(2094078,64,420),(2096128,110,156),(2096422,117,274),(2096958,117,395),(2097144,65,420),(2097150,0,421)]),(744439,[(338621,72,288),(609237,49,152),(812024,1,362),(1146005,51,168),(1343032,61,288),(1605568,86,152),(2066581,50,154),(2073144,25,364),(2081728,66,405),(2092029,24,419),(2096128,110,154),(2096829,2,403),(2097109,26,415),(2097144,65,419),(2097149,0,422)]),(744439,[(2081728,1,417)]),(744439,[(812024,27,371),(2073144,3,376),(2081728,27,413)]),(744439,[(609237,27,223),(2066581,25,225),(2081728,1,418)]),(744439,[(2081728,1,419)]),(744439,[(812024,1,348),(1343032,2,324),(1605568,82,355),(2073144,25,341),(2081728,130,397),(2096128,58,341),(2097144,0,423)]),(744439,[(676838,56,342),(1211686,64,391),(1605568,83,342),(2068774,81,342),(2081728,130,391),(2096128,58,342)]),(744439,[(609237,27,224),(1146005,26,192),(1605568,82,356),(2066581,25,208),(2081728,118,392),(2096128,58,343),(2097109,2,423)]),(744439,[(1605568,82,357),(2081728,130,406),(2096128,58,345)]),(744439,[(812024,1,377),(2073144,3,377),(2081728,130,416)]),(744439,[(609237,27,226),(2066581,25,226),(2081728,1,420)]),(744439,[(2081728,66,420)]),(744439,[(1605568,82,363),(2081728,118,395),(2096128,58,363)]),(744439,[(2081728,1,421)]),(744439,[(2073144,3,381)]),(744439,[(338621,26,298),(2066581,50,211),(2073144,3,383)]),(744439,[(2073144,3,384)]),(744439,[(1343032,26,349),(2073144,25,343),(2096128,58,371)]),(744439,[(338621,26,300),(1146005,26,206),(1343032,26,350),(2066581,25,210),(2073144,25,360),(2096128,58,372),(2096829,2,404)]),(744439,[(1343032,26,351),(2073144,25,363),(2096128,58,374)]),(744439,[(812024,1,372),(2073144,25,372),(2081728,1,414)]),(744439,[(338621,72,299),(609237,49,162),(812024,1,373),(2066581,50,208),(2073144,3,378),(2081728,66,413),(2092029,27,423)]),(744439,[(812024,1,374),(2073144,25,380),(2081728,1,415)]),(744439,[(2073144,3,382)]),(744439,[(203191,48,192),(338621,26,299),(406334,0,344),(2066581,50,209),(2068774,80,376),(2073144,3,359)]),(744439,[(406334,0,345),(2068774,80,377),(2073144,3,365)]),(744439,[(338621,26,301),(2066581,50,212),(2073144,3,385)]),(744439,[(2073144,3,386)]),(744439,[(1343032,26,353),(2073144,25,361),(2096128,58,380)]),(744439,[(812024,1,375),(2073144,3,379),(2081728,1,416)]),(744439,[(2073144,3,387)]),(372479,[]),(744439,[(2067678,0,424)]),(744439,[]),(1474366,[(2065483,5,232)]),(372479,[]),(372479,[]),(744439,[(1113163,2,232),(1146005,26,232),(1178847,2,276)]),(744439,[(2066581,25,233)]),(744439,[(1113163,7,229),(1146005,26,211),(1178847,26,269),(2065483,5,229),(2066581,25,211),(2067679,25,269),(2096128,58,381),(2096351,2,398)]),(744439,[(1146005,26,212),(2066581,25,214),(2096128,58,382)]),(744439,[(1113163,7,230),(2065483,3,231),(2096128,58,384)]),(744439,[(575435,6,225),(609237,49,225),(643039,1,275),(2065483,5,225),(2066581,50,225),(2067679,3,275),(2081728,66,417)]),(744439,[(609237,49,226),(2066581,25,227),(2081728,66,419)]),(744439,[(338621,73,301),(2066581,50,214),(2073144,3,388)]),(744439,[(2065483,5,233),(2066581,50,233),(2067679,3,277)]),(744439,[]),(744439,[(2096128,58,389)]),(744439,[(2081728,1,422)]),(744439,[(2073144,25,389)]),(744439,[(2066581,25,234)]),(744439,[]),(744439,[(338621,24,302)]),(372479,[]),(744439,[]),(744439,[]),(1474366,[]),(372479,[]),(372479,[(2096128,135,398)]),(372479,[]),(372479,[(2096128,111,404)]),(372479,[(2081728,119,423)]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[])]
def F3 : ℕ → Bool := rowAt L3 E3 L4
def E4 : Array (G × List Link) := #[(744439,[]),(744439,[]),(1474366,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(1474366,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(2089976,[]),(1474366,[]),(1474366,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[]),(744439,[]),(744439,[]),(2089976,[]),(1474366,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[]),(744439,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[]),(744439,[]),(372479,[]),(372479,[]),(1474366,[]),(1474366,[]),(1474366,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[]),(744439,[]),(1474366,[]),(744439,[]),(1474366,[]),(1474366,[]),(1474366,[]),(1474366,[]),(1474366,[]),(1474366,[]),(1474366,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(372479,[]),(1474366,[(1343032,0,0),(1605568,52,0),(1867768,0,1),(2073144,0,2),(2081728,48,2),(2096128,0,3),(2097144,0,4)]),(2089976,[(812024,0,0),(1605568,0,5),(1867768,0,6),(2073144,24,0),(2081728,4,3),(2096128,24,5),(2096696,24,6),(2097144,0,7)]),(1474366,[(812024,0,4),(1343032,0,7),(1605568,48,7),(2073144,24,4),(2081728,4,4),(2096128,4,7)]),(744439,[(1605568,0,8),(2081728,76,8),(2096128,0,9)]),(1474366,[(812024,0,10),(1343032,0,11),(1605568,0,12),(2073144,0,13),(2081728,0,14),(2096128,0,15),(2097144,0,16)]),(744439,[(676838,0,10),(1211686,0,17),(1605568,77,17),(2068774,0,18),(2081728,77,18),(2096128,0,19)]),(744439,[(812024,0,17),(1343032,0,20),(1605568,0,21),(2073144,0,22),(2081728,0,23),(2096128,0,24),(2097144,0,25)]),(744439,[(676838,0,11),(1211686,0,20),(1605568,79,22),(2068774,0,26),(2081728,0,27),(2096128,79,13)]),(744439,[(406334,0,8),(676838,0,12),(812024,77,17),(1211686,0,21),(1343032,79,22),(1736678,0,28),(1867768,0,29),(1998846,0,30),(2068774,0,31),(2073144,78,27),(2081728,0,32),(2094078,0,33),(2096128,0,34),(2096958,0,35),(2097088,0,36),(2097144,0,37),(2097150,0,38)]),(744439,[(1605568,0,30),(2081728,0,39),(2096128,0,40)]),(744439,[(812024,0,18),(1343032,0,26),(1605568,0,31),(2073144,78,20),(2081728,4,18),(2096128,4,26),(2097144,0,41)]),(744439,[(406334,76,8),(676838,0,14),(812024,77,18),(1211686,0,23),(1343032,0,27),(1605568,0,32),(1998846,0,39),(2068774,4,18),(2073144,78,26),(2085862,0,42),(2094078,0,43),(2096128,0,44),(2096958,0,45),(2097088,0,46),(2097144,0,47),(2097150,0,48)]),(744439,[(1605568,0,33),(2081728,0,43),(2096128,0,49)]),(744439,[(406334,0,9),(676838,0,15),(812024,0,19),(1211686,0,24),(1343032,79,13),(1605568,0,34),(1998846,0,40),(2068774,4,26),(2073144,78,11),(2081728,0,44),(2094078,0,49),(2096422,0,50),(2096696,0,51),(2096958,0,52),(2097088,0,53),(2097144,0,54),(2097150,0,55)]),(744439,[(1605568,0,35),(2081728,0,45),(2096128,0,52)]),(744439,[(676838,0,16),(1211686,0,25),(1605568,0,37),(2068774,0,41),(2081728,0,47),(2096128,0,54)]),(744439,[(1605568,0,38),(2081728,0,48),(2096128,0,55)]),(2089976,[(812024,0,56),(1343032,60,12),(1605568,0,57),(2073144,36,57),(2081728,0,58),(2096128,0,59),(2097144,0,60)]),(744439,[(609237,0,56),(1146005,0,61),(1605568,0,62),(2066581,0,63),(2081728,137,21),(2096128,0,64),(2097109,0,65)]),(744439,[(812024,0,61),(1343032,60,10),(1605568,82,62),(2073144,36,58),(2081728,0,66),(2096128,51,24),(2097144,0,67)]),(744439,[(338621,0,8),(609237,0,57),(812024,0,62),(1146005,82,62),(1343032,60,11),(1671125,0,68),(1867768,0,69),(2066581,0,70),(2073144,36,59),(2081728,0,71),(2092029,0,72),(2096128,0,73),(2096829,0,74),(2097088,0,75),(2097109,0,76),(2097144,0,77),(2097149,0,78)]),(744439,[(812024,0,63),(1343032,60,14),(1605568,0,70),(2073144,25,56),(2081728,4,63),(2096128,50,14),(2097144,0,79)]),(744439,[(338621,76,8),(609237,0,58),(812024,137,21),(1146005,0,66),(1343032,60,15),(1605568,0,71),(2066581,4,63),(2073144,113,12),(2083797,0,80),(2092029,0,81),(2096128,0,82),(2096829,0,83),(2097088,0,84),(2097109,0,85),(2097144,0,86),(2097149,0,87)]),(744439,[(1605568,0,72),(2081728,0,81),(2096128,0,88)]),(744439,[(338621,0,9),(609237,0,59),(812024,0,64),(1146005,51,24),(1343032,60,13),(1605568,0,73),(2066581,50,14),(2073144,112,57),(2081728,0,82),(2092029,0,88),(2096696,0,89),(2096829,0,90),(2097088,0,91),(2097109,0,92),(2097144,0,93),(2097149,0,94)]),(744439,[(1605568,0,74),(2081728,0,83),(2096128,0,90)]),(744439,[(812024,0,65),(1343032,60,16),(1605568,0,76),(2073144,36,60),(2081728,0,85),(2096128,0,92),(2097144,0,95)]),(744439,[(609237,0,60),(1146005,0,67),(1605568,0,77),(2066581,0,79),(2081728,0,86),(2096128,0,93),(2097109,0,95)]),(744439,[(1605568,0,78),(2081728,0,87),(2096128,0,94)]),(744439,[(1211686,0,96),(2068774,4,42),(2096128,0,97)]),(744439,[(1146005,0,98),(2066581,4,80),(2096128,0,99)]),(744439,[(2096128,0,100)]),(744439,[(406334,0,61),(676838,56,61),(947198,0,98),(1211686,0,101),(1343032,26,61),(1605568,82,61),(1867768,26,98),(1998846,0,102),(2068774,4,23),(2073144,0,103),(2081728,0,104),(2094078,0,105),(2096128,51,23),(2096958,0,106),(2097144,26,105),(2097150,0,107)]),(744439,[(338621,0,17),(609237,49,63),(879613,0,96),(1146005,0,101),(1343032,64,17),(1605568,86,63),(1867768,64,96),(2066581,4,66),(2073144,0,108),(2081728,4,104),(2092029,0,109),(2096128,40,66),(2096829,0,110),(2097109,0,111),(2097144,64,109),(2097149,0,112)]),(744439,[(203191,0,0),(609237,27,63),(676838,114,62),(1146005,26,61),(1211686,64,17),(1605568,90,0),(1802231,0,113),(2066581,4,82),(2068774,4,44),(2081728,115,32),(2087927,0,114),(2096128,115,71),(2096567,0,115),(2097109,0,116),(2097143,0,117)]),(744439,[(1605568,90,113),(2081728,0,118),(2096128,0,119)]),(744439,[(1343032,0,113),(2073144,0,120),(2096128,0,121)]),(744439,[(203191,0,1),(1146005,26,98),(1211686,64,96),(2066581,4,84),(2068774,4,46),(2096128,0,122),(2096567,0,123)]),(744439,[(1146005,0,102),(2066581,4,85),(2096128,0,124)]),(744439,[(2096128,0,125)]),(744439,[(203191,0,2),(609237,107,14),(676838,141,24),(1146005,0,103),(1211686,0,108),(1605568,167,44),(1802231,0,120),(2066581,106,12),(2068774,89,26),(2081728,0,126),(2087927,0,127),(2096128,143,34),(2096567,0,128),(2097109,0,129),(2097143,0,130)]),(744439,[(203191,48,2),(338621,77,18),(406334,137,21),(1146005,0,104),(1211686,4,104),(1343032,115,32),(1540031,0,118),(2066581,130,21),(2068774,85,18),(2073144,0,126),(2096128,119,32),(2096567,4,118),(2096829,0,131),(2096958,4,131),(2097087,0,132)]),(744439,[(1343032,0,114),(2073144,0,127),(2096128,0,133)]),(744439,[(1211686,0,109),(2068774,4,43),(2096128,0,134)]),(744439,[(1146005,0,105),(2066581,4,81),(2096128,0,135)]),(744439,[(2096128,0,136)]),(744439,[(203191,0,3),(338621,0,19),(406334,0,64),(609237,27,70),(676838,56,66),(879613,0,97),(947198,0,99),(1014783,0,100),(1146005,51,23),(1211686,40,66),(1343032,115,71),(1540031,0,119),(1605568,167,82),(1802231,0,121),(1867768,0,122),(1998846,0,124),(2064383,0,125),(2066581,50,15),(2068774,4,27),(2073144,143,34),(2081728,119,32),(2087927,0,133),(2092029,0,134),(2094078,0,135),(2096127,0,136),(2096422,0,137),(2096567,0,138),(2096696,0,139),(2096829,0,140),(2096958,0,141),(2097087,0,142),(2097088,0,143),(2097109,0,144),(2097143,0,145),(2097144,0,146),(2097149,0,147),(2097150,0,148)]),(744439,[(1343032,0,115),(1605568,90,116),(1867768,0,123),(2073144,0,128),(2081728,4,118),(2096128,0,138),(2097144,0,149)]),(744439,[(676838,56,67),(1211686,0,110),(1605568,90,115),(2068774,4,45),(2081728,0,131),(2096128,0,140)]),(744439,[(609237,27,79),(1146005,0,106),(1605568,90,114),(2066581,4,83),(2081728,4,131),(2096128,0,141),(2097109,0,150)]),(744439,[(1605568,90,117),(2081728,0,132),(2096128,0,142)]),(744439,[(406334,0,65),(1211686,0,111),(1343032,0,116),(2068774,4,39),(2073144,0,129),(2096128,0,144),(2096958,0,150)]),(744439,[(1343032,0,117),(2073144,0,130),(2096128,0,145)]),(744439,[(203191,0,4),(1146005,26,105),(1211686,64,109),(2066581,4,86),(2068774,4,47),(2096128,0,146),(2096567,0,149)]),(744439,[(1211686,0,112),(2068774,4,48),(2096128,0,147)]),(744439,[(1146005,0,107),(2066581,4,87),(2096128,0,148)]),(744439,[(1605568,0,151),(2081728,4,133),(2096128,0,152)]),(744439,[(1343032,0,151),(2073144,0,153),(2096128,0,154)]),(744439,[(1605568,0,153),(2081728,4,127),(2096128,0,155)]),(744439,[(812024,0,100),(1343032,0,152),(1605568,0,154),(2073144,0,155),(2081728,4,114),(2096696,0,156),(2097088,0,157),(2097144,0,158)]),(744439,[(2096128,0,158)]),(744439,[(812024,0,101),(2073144,0,159),(2081728,4,101)]),(744439,[(812024,0,102),(2073144,0,160),(2081728,4,111)]),(744439,[(406334,36,58),(676838,56,64),(812024,0,103),(1211686,0,159),(1343032,103,58),(1605568,82,64),(1998846,0,160),(2068774,4,22),(2077502,0,161),(2081728,4,108),(2094078,0,162),(2096128,51,22),(2096696,26,161),(2096958,0,163),(2097144,26,162),(2097150,0,164)]),(744439,[(812024,0,105),(1343032,26,67),(1605568,82,65),(2073144,0,162),(2081728,4,109),(2096128,51,25),(2097144,0,165)]),(744439,[(812024,0,106),(2073144,0,163),(2081728,4,110)]),(744439,[(812024,0,107),(2073144,0,164),(2081728,4,112)]),(744439,[(676838,56,69),(2068774,4,50),(2081728,4,137)]),(744439,[(2081728,4,138)]),(744439,[(203191,0,5),(338621,79,22),(406334,60,11),(609237,49,58),(676838,56,57),(812024,90,0),(1014783,0,151),(2066581,4,73),(2068774,4,34),(2073144,139,73),(2081728,163,82),(2087927,4,154),(2092029,0,166),(2094078,166,155),(2096127,0,167)]),(744439,[(812024,0,113),(2073144,138,166),(2081728,4,121)]),(744439,[(203191,0,6),(609237,49,80),(676838,56,68),(2066581,4,91),(2068774,4,53),(2081728,4,143),(2087927,4,157)]),(744439,[(609237,49,81),(2066581,4,92),(2081728,4,144)]),(744439,[(2081728,4,145)]),(744439,[(676838,56,74),(1211686,64,25),(1605568,0,166),(2068774,4,49),(2081728,4,135),(2096128,135,152)]),(744439,[(609237,49,83),(1146005,26,67),(1605568,166,155),(2066581,4,88),(2081728,4,134),(2096128,142,152),(2097109,0,168)]),(744439,[(1605568,0,167),(2081728,4,136),(2096128,0,169)]),(744439,[(203191,24,5),(338621,79,13),(406334,60,13),(609237,49,71),(676838,56,71),(812024,115,71),(1014783,0,152),(2066581,50,13),(2068774,93,13),(2073144,134,5),(2081728,119,71),(2087927,4,152),(2092029,135,152),(2094078,142,152),(2096127,0,169)]),(744439,[(812024,0,115),(2073144,138,151),(2081728,4,119)]),(744439,[(203191,24,6),(609237,49,84),(676838,56,75),(2066581,4,89),(2068774,4,51),(2081728,4,139),(2087927,4,156)]),(744439,[(676838,56,77),(2068774,4,52),(2081728,4,141)]),(744439,[(609237,49,86),(2066581,4,90),(2081728,4,140)]),(744439,[(2081728,4,142)]),(744439,[(406334,60,16),(676838,56,72),(812024,0,116),(2068774,4,40),(2073144,139,154),(2081728,4,124),(2094078,0,168)]),(744439,[(812024,0,117),(2073144,138,167),(2081728,4,125)]),(744439,[(203191,0,7),(609237,49,85),(676838,56,76),(2066581,4,93),(2068774,4,54),(2081728,4,146),(2087927,4,158)]),(744439,[(676838,56,78),(2068774,4,55),(2081728,4,148)]),(744439,[(609237,49,87),(2066581,4,94),(2081728,4,147)]),(744439,[(812024,90,113),(2073144,0,170),(2081728,87,116)]),(744439,[(1605568,0,170),(2081728,4,128),(2096128,134,151)]),(744439,[(2081728,4,149)]),(744439,[(406334,0,68),(2068774,4,28),(2073144,0,171)]),(744439,[(2073144,0,172)]),(744439,[(203191,52,6),(338621,0,29),(406334,0,69),(2066581,4,75),(2068774,4,36),(2073144,0,173)]),(744439,[(338621,0,30),(2066581,4,76),(2073144,0,174)]),(744439,[(2073144,0,175)]),(744439,[(203191,24,3),(338621,78,27),(406334,36,59),(609237,49,59),(676838,56,59),(812024,167,44),(1014783,0,153),(1146005,82,64),(1211686,86,64),(1343032,139,73),(1540031,0,170),(1671125,0,171),(1736678,4,171),(1802231,0,172),(1867768,0,173),(1998846,0,174),(2064383,0,175),(2066581,25,59),(2068774,89,27),(2075325,0,176),(2077502,4,176),(2081728,163,44),(2087927,4,153),(2092029,0,177),(2094078,4,177),(2096127,0,178),(2096128,143,73),(2096567,4,170),(2096696,0,179),(2096829,0,180),(2096958,4,180),(2097087,0,181),(2097088,4,173),(2097109,4,174),(2097143,4,175),(2097144,0,182),(2097149,0,183),(2097150,4,183)]),(744439,[(406334,0,72),(1211686,86,65),(1343032,0,166),(2068774,4,33),(2073144,0,177),(2096128,159,155),(2096958,0,184)]),(744439,[(1343032,0,167),(2073144,0,178),(2096128,4,167)]),(744439,[(406334,0,74),(676838,56,60),(812024,90,115),(2068774,4,35),(2073144,0,180),(2081728,87,114),(2094078,4,184)]),(744439,[(812024,90,117),(2073144,0,181),(2081728,87,117)]),(744439,[(203191,48,7),(338621,0,37),(406334,0,77),(2066581,4,77),(2068774,4,37),(2073144,0,182)]),(744439,[(406334,0,78),(2068774,4,38),(2073144,0,183)]),(744439,[(812024,0,120),(1343032,138,166),(1605568,0,172),(2081728,4,120),(2096128,134,166),(2096696,0,185),(2097144,0,186)]),(744439,[(2073144,0,186)]),(744439,[(609237,49,88),(1146005,0,160),(1605568,0,174),(2066581,25,60),(2081728,4,129),(2096128,143,154),(2097109,0,187)]),(744439,[(2096128,4,168)]),(744439,[(2081728,4,150)]),(744439,[(2073144,0,187)]),(744439,[(2066581,4,95)]),(744439,[]),(744439,[(1605568,0,175),(2081728,4,130),(2096128,134,167)]),(744439,[]),(744439,[(676838,56,89),(1211686,4,161),(1605568,0,176)]),(744439,[(676838,56,90),(1211686,4,162),(1605568,0,177)]),(744439,[(1605568,0,178)]),(744439,[(203191,24,1),(609237,49,91),(676838,56,91),(1146005,26,161),(1211686,40,161),(1605568,0,179),(1802231,0,185)]),(744439,[(676838,56,93),(1211686,4,163),(1605568,0,180)]),(744439,[(1605568,0,181)]),(744439,[(203191,24,4),(609237,49,92),(676838,56,92),(1146005,26,162),(1211686,40,162),(1605568,0,182),(1802231,0,186)]),(744439,[(676838,56,94),(1211686,4,164),(1605568,0,183)]),(744439,[]),(744439,[(1605568,0,184)]),(744439,[(1211686,4,165)]),(744439,[]),(744439,[]),(744439,[]),(744439,[(676838,56,95)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(1605568,166,51),(2081728,0,188),(2096128,142,51)]),(744439,[(812024,136,68),(1343032,166,51),(1867768,0,189),(2073144,112,171),(2081728,87,122),(2096128,95,179),(2097088,0,190),(2097144,0,191)]),(744439,[(812024,137,28),(1343032,0,188),(1605568,87,122),(2073144,113,28),(2096128,111,122),(2097088,0,192),(2097144,0,193)]),(744439,[(1605568,0,191),(2081728,0,193),(2096128,24,191)]),(2089976,[(812024,114,69),(1605568,166,89),(1867768,114,189),(2073144,138,173),(2081728,109,97),(2096128,142,139),(2096696,0,194),(2097144,0,195)]),(1474366,[(812024,141,50),(1343032,138,173),(1605568,157,176),(2081728,118,42),(2096128,143,143),(2096696,0,196),(2097144,0,197)]),(1474366,[(812024,141,137),(1343032,142,139),(1605568,94,161),(2073144,143,143),(2081728,109,96),(2096696,0,198),(2097088,0,199),(2097144,0,200)]),(1474366,[(1343032,0,195),(2073144,0,197),(2096128,0,200)]),(744439,[(2096128,0,201)]),(744439,[(1343032,114,29),(1605568,161,80),(1867768,167,199),(2073144,0,202),(2081728,0,203),(2096128,110,99),(2097144,0,204)]),(744439,[(1211686,167,199),(2068774,24,196),(2096128,115,190)]),(744439,[(2096128,0,205)]),(744439,[(676838,141,50),(1211686,0,202),(1605568,167,53),(2068774,165,50),(2081728,0,206),(2096128,143,53)]),(744439,[(406334,137,28),(1211686,0,203),(1343032,115,36),(2068774,162,42),(2073144,0,206),(2096128,119,46),(2096958,0,207)]),(744439,[(2096128,0,208)]),(744439,[(406334,136,171),(676838,141,137),(947198,0,201),(1211686,110,99),(1343032,115,75),(1605568,167,91),(1867768,115,190),(1998846,0,205),(2068774,93,176),(2073144,143,53),(2081728,119,46),(2094078,0,208),(2096422,110,201),(2096696,135,194),(2096958,0,209),(2097088,159,196),(2097144,0,210),(2097150,0,211)]),(744439,[(1605568,167,157),(2081728,0,207),(2096128,0,209)]),(744439,[(1211686,0,204),(2068774,24,197),(2096128,0,210)]),(744439,[(2096128,0,211)]),(744439,[(812024,114,29),(2073144,138,29),(2081728,0,212)]),(744439,[(812024,0,203),(1343032,0,212),(1605568,86,98),(2073144,24,203),(2096128,110,98),(2097088,0,213),(2097144,0,214)]),(744439,[(812024,0,204),(2073144,24,204),(2081728,0,214)]),(744439,[(676838,114,189),(2068774,24,194),(2081728,166,198)]),(744439,[(2081728,0,215)]),(744439,[(406334,0,188),(676838,109,97),(812024,115,36),(1211686,0,212),(1605568,163,84),(1867768,166,198),(1998846,0,215),(2068774,85,97),(2073144,139,36),(2085862,0,216),(2094078,0,217),(2096128,119,84),(2096696,142,198),(2096958,24,215),(2097088,119,192),(2097144,0,218),(2097150,0,219)]),(744439,[(1605568,166,156),(2081728,0,217),(2096128,142,156)]),(744439,[(676838,0,195),(2068774,24,195),(2081728,0,218)]),(744439,[(2081728,0,219)]),(744439,[(2073144,24,209)]),(744439,[(1343032,166,156),(2073144,24,208),(2096128,95,185)]),(744439,[(812024,167,157),(2073144,24,205),(2081728,87,123)]),(744439,[(406334,0,191),(2068774,24,200),(2073144,24,210)]),(744439,[(2073144,24,211)]),(744439,[(1343032,0,215),(2073144,24,207),(2096128,111,123)]),(744439,[]),(744439,[(1343032,0,216)]),(744439,[(1343032,0,217)]),(744439,[(406334,0,192),(1211686,0,213),(1343032,119,192)]),(744439,[(406334,0,193),(1211686,0,214),(1343032,0,218)]),(744439,[(1343032,0,219)]),(744439,[]),(744439,[]),(744439,[]),(1474366,[(1211686,108,126),(1605568,94,126),(1736678,108,206),(2068774,92,126),(2081728,109,126),(2085862,109,206),(2096128,0,220)]),(1474366,[(2096128,0,221)]),(1474366,[(1605568,94,127),(2081728,109,131),(2096128,0,222)]),(1474366,[(1343032,35,43),(2073144,33,47),(2096128,0,223)]),(1474366,[(1146005,26,30),(2066581,25,37),(2096128,0,224)]),(1474366,[(2096128,0,225)]),(1474366,[(203191,24,31),(338621,0,220),(406334,32,23),(609237,27,31),(812024,34,23),(947198,132,212),(1014783,0,221),(1146005,26,31),(1211686,116,104),(1343032,35,23),(1540031,0,222),(1605568,94,103),(1736678,108,203),(1802231,0,223),(1998846,0,224),(2064383,0,225),(2066581,25,31),(2068774,92,103),(2073144,33,23),(2081728,118,104),(2085862,109,203),(2087927,1,223),(2092029,1,222),(2094078,1,224),(2096127,1,225),(2096422,110,203),(2096567,2,223),(2096696,134,212),(2096829,2,221),(2096958,2,224),(2097087,2,225),(2097088,111,203),(2097109,3,223),(2097126,0,226),(2097143,0,227),(2097144,3,224),(2097149,3,225),(2097150,0,228)]),(1474366,[(812024,34,25),(1343032,35,45),(1605568,94,128),(2073144,33,39),(2081728,109,118),(2096128,2,223),(2097144,0,229)]),(1474366,[(1211686,116,131),(1605568,94,129),(1736678,108,207),(2068774,92,129),(2081728,118,131),(2085862,109,207),(2096128,2,221)]),(1474366,[(609237,27,41),(1146005,26,35),(1605568,94,120),(2066581,25,33),(2081728,118,118),(2096128,2,224),(2097109,1,229)]),(1474366,[(1605568,94,130),(2081728,109,132),(2096128,2,225)]),(1474366,[(1343032,35,48),(2073144,33,48),(2096128,0,227)]),(1474366,[(1146005,26,38),(2066581,25,38),(2096128,0,228)]),(744439,[(1211686,86,127),(2068774,0,230),(2096128,95,129)]),(744439,[(406334,32,52),(2068774,0,231),(2073144,33,54)]),(744439,[(2068774,0,232)]),(744439,[(203191,24,15),(338621,24,220),(406334,32,15),(609237,27,15),(676838,92,108),(812024,34,15),(1014783,0,230),(1146005,26,15),(1211686,84,108),(1343032,35,15),(1540031,8,230),(1671125,82,188),(1736678,86,202),(1802231,0,231),(1867768,90,188),(1998846,8,231),(2064383,0,232),(2066581,25,15),(2070967,80,188),(2073144,33,15),(2077502,88,188),(2081728,85,108),(2085862,85,202),(2087927,1,231),(2092029,10,230),(2094078,10,231),(2096127,1,232),(2096128,93,108),(2096422,84,202),(2096567,2,231),(2096829,2,230),(2096958,9,231),(2097087,2,232),(2097088,87,202),(2097109,3,231),(2097126,0,233),(2097143,0,234),(2097144,11,231),(2097149,3,232),(2097150,8,234)]),(744439,[(406334,32,40),(1211686,86,120),(1343032,35,16),(2068774,1,231),(2073144,33,49),(2096128,95,128),(2096958,0,235)]),(744439,[(1211686,86,130),(2068774,1,232),(2096128,95,130)]),(744439,[(406334,32,55),(2068774,0,234),(2073144,33,55)]),(744439,[]),(744439,[(2096128,2,229)]),(744439,[(2068774,1,235)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(2081728,87,146),(2096128,95,182),(2097088,87,210)]),(744439,[(1605568,87,146),(2096128,111,146),(2097088,119,218)]),(744439,[(1343032,166,52),(2073144,113,174),(2096128,95,180)]),(744439,[(1343032,136,231),(2073144,113,30),(2096128,111,124)]),(744439,[(812024,136,172),(1343032,142,54),(1605568,95,180),(2073144,112,76),(2081728,111,124),(2096696,134,195),(2097088,111,205),(2097144,0,236)]),(744439,[(2096128,0,236)]),(744439,[(1211686,161,43),(2068774,164,144),(2096128,95,177)]),(744439,[(1211686,60,223),(2068774,162,81),(2096128,111,135)]),(744439,[(676838,140,138),(1211686,117,47),(1605568,95,177),(2068774,164,92),(2081728,111,135),(2096422,158,197),(2097088,111,208)]),(744439,[(1113163,7,141),(2065483,5,163),(2096128,111,141)]),(744439,[(575435,1,100),(1113163,58,77),(1605568,159,174),(2065483,59,93),(2081728,111,141),(2096203,58,191),(2097088,111,209),(2097099,59,236)]),(744439,[(2096128,59,236)]),(744439,[(2096128,95,183)]),(744439,[(2096128,111,148)]),(744439,[(1605568,95,183),(2081728,111,148),(2097088,111,211)]),(744439,[(676838,140,90),(2068774,164,140),(2081728,87,134)]),(744439,[(676838,118,86),(1211686,60,221),(1605568,87,134),(2068774,162,86),(2085862,118,193),(2096128,111,134),(2097088,119,217)]),(744439,[(609237,49,162),(1146005,51,138),(1605568,87,140),(2066581,25,109),(2083797,130,204),(2096128,111,144),(2097088,119,215),(2097109,0,237)]),(744439,[(2081728,0,237)]),(744439,[(2081728,87,147)]),(744439,[(1605568,87,147),(2096128,111,147),(2097088,119,219)]),(744439,[(338621,76,39),(1146005,82,72),(1343032,166,49),(2066581,25,121),(2073144,113,153),(2096128,95,170),(2096829,0,238)]),(744439,[(304763,32,40),(1113163,7,40),(1343032,166,40),(2065483,5,170),(2073144,113,170),(2096128,159,170)]),(744439,[(1343032,166,55),(2073144,113,175),(2096128,95,181)]),(744439,[(203191,24,88),(1146005,82,74),(1211686,161,45),(2066581,25,119),(2068774,164,133),(2096128,95,153),(2096567,82,238)]),(744439,[(1211686,161,48),(2068774,164,145),(2096128,95,178)]),(744439,[(1146005,82,78),(2066581,25,125),(2096128,95,175)]),(744439,[(676838,140,94),(2068774,164,142),(2081728,87,136)]),(744439,[]),(744439,[(1211686,60,224),(1343032,114,231),(2068774,162,85),(2073144,113,37),(2077502,164,200),(2096128,111,100),(2096958,162,237)]),(744439,[(2096128,164,236)]),(744439,[(2081728,162,237)]),(744439,[(2068774,164,158)]),(744439,[]),(744439,[(338621,76,33),(1146005,51,121),(1343032,69,230),(2066581,25,111),(2073144,113,33),(2096128,111,121),(2096829,0,239)]),(744439,[(2096128,58,238)]),(744439,[(2081728,0,239)]),(744439,[(2073144,112,184)]),(744439,[(2066581,25,150)]),(744439,[]),(744439,[]),(744439,[(304763,32,35),(1113163,7,119),(1343032,136,230),(2065483,5,160),(2073144,113,35),(2096128,111,119)]),(744439,[(2096128,112,238)]),(744439,[(2073144,113,184)]),(744439,[(2065483,3,187)]),(744439,[]),(744439,[(1343032,114,232),(2073144,113,38),(2096128,111,125)]),(744439,[]),(744439,[(203191,24,83),(1146005,51,133),(1211686,60,222),(2066581,25,110),(2068774,162,83),(2096128,111,133),(2096567,24,239)]),(744439,[(2096128,24,238)]),(744439,[(2068774,88,168)]),(744439,[]),(744439,[(1211686,60,225),(2068774,162,87),(2096128,111,136)]),(744439,[(2066581,25,149)]),(744439,[(2065483,3,186)]),(744439,[]),(744439,[(1146005,51,145),(2066581,25,112),(2096128,111,145)]),(744439,[]),(744439,[(1113163,7,142),(2065483,5,164),(2096128,111,142)]),(744439,[]),(372479,[]),(744439,[(1211686,60,226),(1343032,68,233)]),(744439,[(1343032,68,234)]),(744439,[(1211686,60,227)]),(744439,[(1211686,60,228),(1343032,69,234)]),(744439,[]),(744439,[(1343032,112,235)]),(744439,[(1146005,26,168)]),(744439,[]),(744439,[]),(744439,[(1211686,60,229)]),(744439,[]),(744439,[(1146005,51,158)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(203191,24,95)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(812024,62,223),(1343032,61,221),(1605568,86,105),(2073144,106,223),(2096128,110,105),(2097088,119,214),(2097144,0,240)]),(744439,[(2081728,0,240)]),(744439,[(2096128,111,149)]),(744439,[]),(744439,[(1211686,0,240)]),(744439,[]),(744439,[(1343032,105,224),(2073144,106,224),(2096128,110,102)]),(744439,[(2073144,117,237)]),(744439,[]),(744439,[]),(744439,[(304763,8,222),(1113163,7,106),(1343032,105,222),(2065483,5,106),(2073144,106,222),(2096128,110,106)]),(744439,[(2096128,110,150)]),(744439,[(2073144,3,239)]),(744439,[]),(744439,[]),(744439,[(1343032,105,225),(2073144,106,225),(2096128,110,107)]),(744439,[]),(372479,[]),(372479,[]),(372479,[]),(744439,[(812024,62,226),(2073144,63,226)]),(744439,[(812024,62,227),(2073144,63,227)]),(744439,[(2073144,63,228)]),(744439,[(1343032,105,229)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(1146005,51,165)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[])]
def F4 : ℕ → Bool := rowAt L4 E4 L5
def E5 : Array (G × List Link) := #[(1638347,[(1605568,0,0),(2081728,0,1),(2096128,0,2)]),(1474366,[(2096128,0,3)]),(1474366,[(1605568,52,1),(2081728,0,4),(2096128,28,1)]),(1474366,[(1343032,0,2),(1605568,52,2),(1867768,0,3),(2073144,28,1),(2081728,4,1),(2096696,0,5),(2097088,52,5),(2097144,0,6)]),(1474366,[(2096128,0,6)]),(2089976,[(812024,0,0),(2073144,24,2),(2081728,48,2)]),(2089976,[(2081728,48,5)]),(2089976,[(2081728,4,6)]),(744439,[(2081728,0,7),(2096128,0,8),(2097088,0,9)]),(744439,[(1605568,0,8),(2081728,76,8),(2097088,0,10)]),(1474366,[(2096128,0,11)]),(2089976,[(1605568,0,12),(2081728,0,13),(2096128,0,14)]),(1474366,[(1343032,0,12),(2073144,0,15),(2096128,0,16)]),(1474366,[(1605568,0,15),(2081728,0,17),(2096128,78,14)]),(1474366,[(1343032,0,13),(2073144,0,17),(2096128,0,18)]),(1474366,[(812024,0,11),(1343032,0,14),(1605568,0,16),(2073144,78,14),(2081728,0,18),(2096696,0,19),(2097088,0,20),(2097144,0,21)]),(1474366,[(2096128,0,21)]),(744439,[(1605568,0,22),(2081728,0,23),(2096128,0,24)]),(744439,[(1605568,77,23),(2081728,0,25),(2096128,0,26)]),(744439,[(676838,0,11),(1211686,0,24),(1605568,77,24),(2068774,0,26),(2081728,77,26),(2096422,0,27),(2097088,77,27)]),(744439,[(2081728,0,28)]),(744439,[(812024,0,22),(2073144,0,29),(2081728,0,30)]),(744439,[(1605568,0,29),(2081728,0,31),(2096128,78,12)]),(744439,[(812024,0,23),(1343032,0,28),(1605568,0,30),(2073144,0,31),(2096128,0,32),(2097088,0,33),(2097144,0,34)]),(744439,[(812024,0,24),(2073144,78,12),(2081728,0,32)]),(744439,[(2081728,0,34)]),(744439,[(1605568,79,31),(2081728,4,26),(2096128,79,17)]),(744439,[(676838,0,13),(1211686,0,28),(1605568,79,29),(2068774,4,26),(2085862,0,35),(2096128,79,15),(2097088,0,36)]),(744439,[(2073144,78,36)]),(744439,[(2068774,0,37)]),(744439,[]),(744439,[(812024,77,23),(1343032,79,31),(1867768,0,37),(2073144,78,28),(2081728,85,23),(2096128,93,31),(2097088,4,37),(2097144,0,38)]),(744439,[(406334,0,7),(1211686,0,30),(1343032,79,29),(2068774,85,23),(2073144,155,26),(2096128,87,1),(2096958,0,39)]),(744439,[(2096128,0,40)]),(744439,[(406334,0,8),(676838,0,16),(812024,77,24),(2068774,93,31),(2073144,78,13),(2081728,87,1),(2094078,0,40)]),(744439,[(2081728,0,39)]),(744439,[(406334,0,9),(2068774,4,37),(2073144,78,35)]),(744439,[(2068774,0,38)]),(744439,[]),(744439,[(2096128,0,41)]),(744439,[(2081728,0,41)]),(744439,[(1605568,0,38)]),(744439,[(1343032,0,35)]),(744439,[]),(744439,[(406334,76,8),(676838,0,18),(812024,77,26),(1211686,0,32),(1343032,79,15),(1605568,87,1),(1998846,0,41)]),(744439,[(1605568,0,39)]),(744439,[(406334,76,9),(1211686,0,33),(1343032,0,36)]),(744439,[(1211686,0,34)]),(744439,[]),(744439,[(1605568,0,40)]),(744439,[(812024,0,27)]),(744439,[(676838,0,19)]),(744439,[]),(744439,[(406334,0,10),(676838,0,20),(812024,77,27)]),(744439,[(676838,0,21)]),(744439,[]),(1638347,[(2096128,0,42)]),(2089976,[(1343032,60,12),(2073144,0,43),(2096128,49,43)]),(1638347,[(1343032,60,16),(2073144,113,12),(2096128,0,44)]),(2089976,[(812024,0,42),(1343032,60,15),(1605568,49,43),(2073144,36,43),(2081728,0,44),(2096696,0,45),(2097088,0,46),(2097144,0,47)]),(2089976,[(2096128,0,47)]),(744439,[(1605568,0,48),(2081728,137,30),(2096128,51,32)]),(744439,[(1146005,0,48),(2066581,0,49),(2096128,167,44)]),(744439,[(1605568,0,49),(2081728,130,22),(2096128,50,18)]),(744439,[(609237,0,42),(1146005,51,32),(1605568,167,44),(2066581,50,18),(2081728,137,29),(2097088,0,50),(2097109,0,51)]),(744439,[(2096128,0,51)]),(744439,[(812024,137,30),(1343032,60,11),(1605568,82,49),(2073144,113,16),(2096128,51,24),(2097088,0,52),(2097144,0,53)]),(744439,[(2081728,0,53)]),(744439,[(2073144,36,46)]),(744439,[(2066581,0,54)]),(744439,[(812024,0,49),(1343032,60,13),(1867768,0,54),(2073144,25,42),(2081728,4,49),(2096128,50,13),(2097088,4,54),(2097144,0,55)]),(744439,[(338621,0,7),(1146005,82,49),(1343032,60,14),(2066581,4,49),(2073144,113,15),(2096128,87,2),(2096829,0,56)]),(744439,[(2096128,0,57)]),(744439,[(338621,0,8),(609237,49,43),(812024,167,44),(2066581,50,13),(2073144,112,43),(2081728,87,2),(2092029,0,57)]),(744439,[(2081728,0,56)]),(744439,[(338621,0,9),(2066581,4,54),(2073144,36,45)]),(744439,[(2073144,36,47)]),(744439,[(2066581,0,55)]),(744439,[]),(744439,[(1605568,0,55)]),(744439,[(1343032,60,20)]),(744439,[]),(744439,[(338621,76,8),(609237,0,44),(812024,137,29),(1146005,51,24),(1343032,142,14),(1605568,87,2)]),(744439,[(1605568,0,56)]),(744439,[(338621,76,9),(1146005,0,52),(1343032,60,19)]),(744439,[(1343032,60,21)]),(744439,[(1146005,0,53)]),(744439,[]),(744439,[(1605568,0,57)]),(744439,[(609237,0,45)]),(744439,[]),(744439,[(338621,0,10),(609237,0,46),(812024,0,50)]),(744439,[(812024,0,51)]),(744439,[(609237,0,47)]),(744439,[]),(744439,[]),(744439,[(2096128,40,52)]),(744439,[(1211686,40,52),(2068774,4,35),(2096422,0,58)]),(744439,[(2096128,51,33)]),(744439,[(1146005,51,33),(2066581,50,20)]),(744439,[]),(744439,[(2073144,0,59),(2081728,0,60)]),(744439,[]),(744439,[(676838,141,32),(1211686,0,59),(1605568,167,32),(2068774,4,31),(2081728,0,61),(2096128,51,31)]),(744439,[(406334,137,30),(1211686,0,60),(1343032,115,30),(2068774,4,23),(2073144,0,61),(2096128,51,23),(2096958,0,62)]),(744439,[(2096128,51,34)]),(744439,[(2081728,0,62)]),(744439,[]),(744439,[(609237,107,18),(1146005,0,59),(1605568,167,18),(2066581,106,16),(2081728,4,61),(2096128,143,16),(2097109,0,63)]),(744439,[(2096128,40,53)]),(744439,[(2081728,4,62)]),(744439,[(2073144,0,63)]),(744439,[]),(744439,[]),(744439,[(2096128,115,56)]),(744439,[(2081728,115,39)]),(744439,[(2068774,4,41)]),(744439,[]),(744439,[(2096128,119,39)]),(744439,[(2081728,119,39)]),(744439,[(2096128,143,40)]),(744439,[(2073144,143,40)]),(744439,[(203191,0,3),(2066581,50,19),(2068774,4,36)]),(744439,[]),(744439,[(2066581,50,21)]),(744439,[]),(744439,[(203191,0,4),(1146005,0,61),(1211686,4,61)]),(744439,[]),(744439,[(1605568,167,41)]),(744439,[(1211686,0,63)]),(744439,[]),(744439,[(1211686,4,62)]),(744439,[]),(744439,[(1343032,115,56)]),(744439,[(1211686,40,53)]),(744439,[(1146005,51,34)]),(744439,[]),(744439,[(338621,0,27),(609237,49,54),(879613,0,58)]),(744439,[]),(744439,[(203191,0,5),(609237,27,54),(676838,56,52)]),(744439,[(676838,56,53)]),(744439,[(609237,27,55)]),(744439,[]),(744439,[(203191,52,5),(338621,77,27),(406334,0,50)]),(744439,[(406334,0,51)]),(744439,[]),(744439,[(203191,0,6)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(2081728,119,56)]),(744439,[(2096128,143,57)]),(744439,[(2073144,143,57)]),(744439,[(1605568,143,57)]),(744439,[]),(744439,[]),(744439,[]),(744439,[(812024,0,59),(2081728,4,59)]),(744439,[(2081728,4,63)]),(744439,[(1605568,82,50)]),(744439,[(1605568,82,51)]),(744439,[]),(744439,[]),(744439,[]),(744439,[(2068774,4,40)]),(744439,[]),(744439,[]),(744439,[]),(744439,[(2081728,163,41)]),(744439,[(406334,36,46),(2068774,89,36),(2077502,0,64)]),(744439,[]),(744439,[(203191,24,5),(2066581,25,45),(2068774,89,35)]),(744439,[(2066581,25,47)]),(744439,[]),(744439,[(676838,56,45),(1211686,86,50),(1736678,4,64)]),(744439,[(1211686,86,51)]),(744439,[]),(744439,[(203191,24,3),(609237,49,46),(676838,56,46)]),(744439,[(676838,56,47)]),(744439,[]),(744439,[(203191,24,6)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(1605568,166,19),(2096128,142,19),(2097088,0,65)]),(744439,[]),(744439,[(2073144,112,64)]),(744439,[]),(744439,[(1343032,0,65)]),(744439,[]),(2089976,[(2081728,109,58)]),(2089976,[]),(1474366,[(1605568,94,64)]),(1474366,[]),(1474366,[(812024,141,58)]),(1474366,[]),(1474366,[]),(744439,[]),(744439,[(1605568,167,20),(2081728,0,66),(2096128,143,20)]),(744439,[(1343032,114,37),(2073144,0,66),(2096128,119,33)]),(744439,[]),(744439,[]),(744439,[(1211686,0,66)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[(812024,114,37),(2073144,138,37)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(1474366,[(1211686,116,61),(1605568,94,61),(1736678,108,66),(2068774,92,61),(2081728,118,61),(2085862,109,66),(2096422,110,66),(2097088,111,66),(2097126,0,67)]),(1474366,[]),(1474366,[(2081728,118,62)]),(1474366,[(2073144,33,34)]),(1474366,[(2066581,25,38)]),(1474366,[]),(1474366,[(338621,0,67)]),(1474366,[]),(1474366,[]),(1474366,[]),(744439,[(2096128,93,63)]),(744439,[(2073144,33,21)]),(744439,[]),(744439,[(338621,24,67)]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[]),(744439,[])]
def F5 : ℕ → Bool := rowAt L5 E5 L6
def E6 : Array G := #[2096277,1638347,1638347,1474366,1474366,1474366,1474366,744439,744439,744439,744439,1474366,2089976,1638347,2089976,1474366,1474366,1474366,1474366,1474366,1474366,1474366,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,1638347,2096277,1638347,2089976,2089976,2089976,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,744439,1474366]
def F6 : ℕ → Bool := bottomAt L6 E6
end PEqualNP.Outside.Fano1023

namespace PEqualNP.Outside.Fano1023
set_option maxHeartbeats 100000000
set_option maxRecDepth 200000
private theorem check6_0 : checkChunk 68 F6 0 = true := by decide +kernel
private theorem check6_1 : checkChunk 68 F6 1 = true := by decide +kernel
private theorem check6_2 : checkChunk 68 F6 2 = true := by decide +kernel
private theorem check6_3 : checkChunk 68 F6 3 = true := by decide +kernel
private theorem check6_4 : checkChunk 68 F6 4 = true := by decide +kernel
private theorem check6_5 : checkChunk 68 F6 5 = true := by decide +kernel
private theorem check6_6 : checkChunk 68 F6 6 = true := by decide +kernel
private theorem check6_7 : checkChunk 68 F6 7 = true := by decide +kernel
private theorem check6_8 : checkChunk 68 F6 8 = true := by decide +kernel
private theorem layer6 (i : Fin L6.size) : ¬Reach 0 (L6[i.val]).toFinset := by
  apply bottomLayer (instructions := E6)
  change ∀ j : Fin 68, F6 j.val = true
  apply checkedChunk
  intro b
  change Fin 9 at b
  fin_cases b
  · exact check6_0
  · exact check6_1
  · exact check6_2
  · exact check6_3
  · exact check6_4
  · exact check6_5
  · exact check6_6
  · exact check6_7
  · exact check6_8
private theorem check5_0 : checkChunk 241 F5 0 = true := by decide +kernel
private theorem check5_1 : checkChunk 241 F5 1 = true := by decide +kernel
private theorem check5_2 : checkChunk 241 F5 2 = true := by decide +kernel
private theorem check5_3 : checkChunk 241 F5 3 = true := by decide +kernel
private theorem check5_4 : checkChunk 241 F5 4 = true := by decide +kernel
private theorem check5_5 : checkChunk 241 F5 5 = true := by decide +kernel
private theorem check5_6 : checkChunk 241 F5 6 = true := by decide +kernel
private theorem check5_7 : checkChunk 241 F5 7 = true := by decide +kernel
private theorem check5_8 : checkChunk 241 F5 8 = true := by decide +kernel
private theorem check5_9 : checkChunk 241 F5 9 = true := by decide +kernel
private theorem check5_10 : checkChunk 241 F5 10 = true := by decide +kernel
private theorem check5_11 : checkChunk 241 F5 11 = true := by decide +kernel
private theorem check5_12 : checkChunk 241 F5 12 = true := by decide +kernel
private theorem check5_13 : checkChunk 241 F5 13 = true := by decide +kernel
private theorem check5_14 : checkChunk 241 F5 14 = true := by decide +kernel
private theorem check5_15 : checkChunk 241 F5 15 = true := by decide +kernel
private theorem check5_16 : checkChunk 241 F5 16 = true := by decide +kernel
private theorem check5_17 : checkChunk 241 F5 17 = true := by decide +kernel
private theorem check5_18 : checkChunk 241 F5 18 = true := by decide +kernel
private theorem check5_19 : checkChunk 241 F5 19 = true := by decide +kernel
private theorem check5_20 : checkChunk 241 F5 20 = true := by decide +kernel
private theorem check5_21 : checkChunk 241 F5 21 = true := by decide +kernel
private theorem check5_22 : checkChunk 241 F5 22 = true := by decide +kernel
private theorem check5_23 : checkChunk 241 F5 23 = true := by decide +kernel
private theorem check5_24 : checkChunk 241 F5 24 = true := by decide +kernel
private theorem check5_25 : checkChunk 241 F5 25 = true := by decide +kernel
private theorem check5_26 : checkChunk 241 F5 26 = true := by decide +kernel
private theorem check5_27 : checkChunk 241 F5 27 = true := by decide +kernel
private theorem check5_28 : checkChunk 241 F5 28 = true := by decide +kernel
private theorem check5_29 : checkChunk 241 F5 29 = true := by decide +kernel
private theorem check5_30 : checkChunk 241 F5 30 = true := by decide +kernel
private theorem layer5 (i : Fin L5.size) : ¬Reach 1 (L5[i.val]).toFinset := by
  apply nodeLayer (instructions := E5) (next := L6) ?_ layer6
  change ∀ j : Fin 241, F5 j.val = true
  apply checkedChunk
  intro b
  change Fin 31 at b
  fin_cases b
  · exact check5_0
  · exact check5_1
  · exact check5_2
  · exact check5_3
  · exact check5_4
  · exact check5_5
  · exact check5_6
  · exact check5_7
  · exact check5_8
  · exact check5_9
  · exact check5_10
  · exact check5_11
  · exact check5_12
  · exact check5_13
  · exact check5_14
  · exact check5_15
  · exact check5_16
  · exact check5_17
  · exact check5_18
  · exact check5_19
  · exact check5_20
  · exact check5_21
  · exact check5_22
  · exact check5_23
  · exact check5_24
  · exact check5_25
  · exact check5_26
  · exact check5_27
  · exact check5_28
  · exact check5_29
  · exact check5_30
private theorem check4_0 : checkChunk 425 F4 0 = true := by decide +kernel
private theorem check4_1 : checkChunk 425 F4 1 = true := by decide +kernel
private theorem check4_2 : checkChunk 425 F4 2 = true := by decide +kernel
private theorem check4_3 : checkChunk 425 F4 3 = true := by decide +kernel
private theorem check4_4 : checkChunk 425 F4 4 = true := by decide +kernel
private theorem check4_5 : checkChunk 425 F4 5 = true := by decide +kernel
private theorem check4_6 : checkChunk 425 F4 6 = true := by decide +kernel
private theorem check4_7 : checkChunk 425 F4 7 = true := by decide +kernel
private theorem check4_8 : checkChunk 425 F4 8 = true := by decide +kernel
private theorem check4_9 : checkChunk 425 F4 9 = true := by decide +kernel
private theorem check4_10 : checkChunk 425 F4 10 = true := by decide +kernel
private theorem check4_11 : checkChunk 425 F4 11 = true := by decide +kernel
private theorem check4_12 : checkChunk 425 F4 12 = true := by decide +kernel
private theorem check4_13 : checkChunk 425 F4 13 = true := by decide +kernel
private theorem check4_14 : checkChunk 425 F4 14 = true := by decide +kernel
private theorem check4_15 : checkChunk 425 F4 15 = true := by decide +kernel
private theorem check4_16 : checkChunk 425 F4 16 = true := by decide +kernel
private theorem check4_17 : checkChunk 425 F4 17 = true := by decide +kernel
private theorem check4_18 : checkChunk 425 F4 18 = true := by decide +kernel
private theorem check4_19 : checkChunk 425 F4 19 = true := by decide +kernel
private theorem check4_20 : checkChunk 425 F4 20 = true := by decide +kernel
private theorem check4_21 : checkChunk 425 F4 21 = true := by decide +kernel
private theorem check4_22 : checkChunk 425 F4 22 = true := by decide +kernel
private theorem check4_23 : checkChunk 425 F4 23 = true := by decide +kernel
private theorem check4_24 : checkChunk 425 F4 24 = true := by decide +kernel
private theorem check4_25 : checkChunk 425 F4 25 = true := by decide +kernel
private theorem check4_26 : checkChunk 425 F4 26 = true := by decide +kernel
private theorem check4_27 : checkChunk 425 F4 27 = true := by decide +kernel
private theorem check4_28 : checkChunk 425 F4 28 = true := by decide +kernel
private theorem check4_29 : checkChunk 425 F4 29 = true := by decide +kernel
private theorem check4_30 : checkChunk 425 F4 30 = true := by decide +kernel
private theorem check4_31 : checkChunk 425 F4 31 = true := by decide +kernel
private theorem check4_32 : checkChunk 425 F4 32 = true := by decide +kernel
private theorem check4_33 : checkChunk 425 F4 33 = true := by decide +kernel
private theorem check4_34 : checkChunk 425 F4 34 = true := by decide +kernel
private theorem check4_35 : checkChunk 425 F4 35 = true := by decide +kernel
private theorem check4_36 : checkChunk 425 F4 36 = true := by decide +kernel
private theorem check4_37 : checkChunk 425 F4 37 = true := by decide +kernel
private theorem check4_38 : checkChunk 425 F4 38 = true := by decide +kernel
private theorem check4_39 : checkChunk 425 F4 39 = true := by decide +kernel
private theorem check4_40 : checkChunk 425 F4 40 = true := by decide +kernel
private theorem check4_41 : checkChunk 425 F4 41 = true := by decide +kernel
private theorem check4_42 : checkChunk 425 F4 42 = true := by decide +kernel
private theorem check4_43 : checkChunk 425 F4 43 = true := by decide +kernel
private theorem check4_44 : checkChunk 425 F4 44 = true := by decide +kernel
private theorem check4_45 : checkChunk 425 F4 45 = true := by decide +kernel
private theorem check4_46 : checkChunk 425 F4 46 = true := by decide +kernel
private theorem check4_47 : checkChunk 425 F4 47 = true := by decide +kernel
private theorem check4_48 : checkChunk 425 F4 48 = true := by decide +kernel
private theorem check4_49 : checkChunk 425 F4 49 = true := by decide +kernel
private theorem check4_50 : checkChunk 425 F4 50 = true := by decide +kernel
private theorem check4_51 : checkChunk 425 F4 51 = true := by decide +kernel
private theorem check4_52 : checkChunk 425 F4 52 = true := by decide +kernel
private theorem check4_53 : checkChunk 425 F4 53 = true := by decide +kernel
private theorem layer4 (i : Fin L4.size) : ¬Reach 2 (L4[i.val]).toFinset := by
  apply nodeLayer (instructions := E4) (next := L5) ?_ layer5
  change ∀ j : Fin 425, F4 j.val = true
  apply checkedChunk
  intro b
  change Fin 54 at b
  fin_cases b
  · exact check4_0
  · exact check4_1
  · exact check4_2
  · exact check4_3
  · exact check4_4
  · exact check4_5
  · exact check4_6
  · exact check4_7
  · exact check4_8
  · exact check4_9
  · exact check4_10
  · exact check4_11
  · exact check4_12
  · exact check4_13
  · exact check4_14
  · exact check4_15
  · exact check4_16
  · exact check4_17
  · exact check4_18
  · exact check4_19
  · exact check4_20
  · exact check4_21
  · exact check4_22
  · exact check4_23
  · exact check4_24
  · exact check4_25
  · exact check4_26
  · exact check4_27
  · exact check4_28
  · exact check4_29
  · exact check4_30
  · exact check4_31
  · exact check4_32
  · exact check4_33
  · exact check4_34
  · exact check4_35
  · exact check4_36
  · exact check4_37
  · exact check4_38
  · exact check4_39
  · exact check4_40
  · exact check4_41
  · exact check4_42
  · exact check4_43
  · exact check4_44
  · exact check4_45
  · exact check4_46
  · exact check4_47
  · exact check4_48
  · exact check4_49
  · exact check4_50
  · exact check4_51
  · exact check4_52
  · exact check4_53
private theorem check3_0 : checkChunk 353 F3 0 = true := by decide +kernel
private theorem check3_1 : checkChunk 353 F3 1 = true := by decide +kernel
private theorem check3_2 : checkChunk 353 F3 2 = true := by decide +kernel
private theorem check3_3 : checkChunk 353 F3 3 = true := by decide +kernel
private theorem check3_4 : checkChunk 353 F3 4 = true := by decide +kernel
private theorem check3_5 : checkChunk 353 F3 5 = true := by decide +kernel
private theorem check3_6 : checkChunk 353 F3 6 = true := by decide +kernel
private theorem check3_7 : checkChunk 353 F3 7 = true := by decide +kernel
private theorem check3_8 : checkChunk 353 F3 8 = true := by decide +kernel
private theorem check3_9 : checkChunk 353 F3 9 = true := by decide +kernel
private theorem check3_10 : checkChunk 353 F3 10 = true := by decide +kernel
private theorem check3_11 : checkChunk 353 F3 11 = true := by decide +kernel
private theorem check3_12 : checkChunk 353 F3 12 = true := by decide +kernel
private theorem check3_13 : checkChunk 353 F3 13 = true := by decide +kernel
private theorem check3_14 : checkChunk 353 F3 14 = true := by decide +kernel
private theorem check3_15 : checkChunk 353 F3 15 = true := by decide +kernel
private theorem check3_16 : checkChunk 353 F3 16 = true := by decide +kernel
private theorem check3_17 : checkChunk 353 F3 17 = true := by decide +kernel
private theorem check3_18 : checkChunk 353 F3 18 = true := by decide +kernel
private theorem check3_19 : checkChunk 353 F3 19 = true := by decide +kernel
private theorem check3_20 : checkChunk 353 F3 20 = true := by decide +kernel
private theorem check3_21 : checkChunk 353 F3 21 = true := by decide +kernel
private theorem check3_22 : checkChunk 353 F3 22 = true := by decide +kernel
private theorem check3_23 : checkChunk 353 F3 23 = true := by decide +kernel
private theorem check3_24 : checkChunk 353 F3 24 = true := by decide +kernel
private theorem check3_25 : checkChunk 353 F3 25 = true := by decide +kernel
private theorem check3_26 : checkChunk 353 F3 26 = true := by decide +kernel
private theorem check3_27 : checkChunk 353 F3 27 = true := by decide +kernel
private theorem check3_28 : checkChunk 353 F3 28 = true := by decide +kernel
private theorem check3_29 : checkChunk 353 F3 29 = true := by decide +kernel
private theorem check3_30 : checkChunk 353 F3 30 = true := by decide +kernel
private theorem check3_31 : checkChunk 353 F3 31 = true := by decide +kernel
private theorem check3_32 : checkChunk 353 F3 32 = true := by decide +kernel
private theorem check3_33 : checkChunk 353 F3 33 = true := by decide +kernel
private theorem check3_34 : checkChunk 353 F3 34 = true := by decide +kernel
private theorem check3_35 : checkChunk 353 F3 35 = true := by decide +kernel
private theorem check3_36 : checkChunk 353 F3 36 = true := by decide +kernel
private theorem check3_37 : checkChunk 353 F3 37 = true := by decide +kernel
private theorem check3_38 : checkChunk 353 F3 38 = true := by decide +kernel
private theorem check3_39 : checkChunk 353 F3 39 = true := by decide +kernel
private theorem check3_40 : checkChunk 353 F3 40 = true := by decide +kernel
private theorem check3_41 : checkChunk 353 F3 41 = true := by decide +kernel
private theorem check3_42 : checkChunk 353 F3 42 = true := by decide +kernel
private theorem check3_43 : checkChunk 353 F3 43 = true := by decide +kernel
private theorem check3_44 : checkChunk 353 F3 44 = true := by decide +kernel
private theorem layer3 (i : Fin L3.size) : ¬Reach 3 (L3[i.val]).toFinset := by
  apply nodeLayer (instructions := E3) (next := L4) ?_ layer4
  change ∀ j : Fin 353, F3 j.val = true
  apply checkedChunk
  intro b
  change Fin 45 at b
  fin_cases b
  · exact check3_0
  · exact check3_1
  · exact check3_2
  · exact check3_3
  · exact check3_4
  · exact check3_5
  · exact check3_6
  · exact check3_7
  · exact check3_8
  · exact check3_9
  · exact check3_10
  · exact check3_11
  · exact check3_12
  · exact check3_13
  · exact check3_14
  · exact check3_15
  · exact check3_16
  · exact check3_17
  · exact check3_18
  · exact check3_19
  · exact check3_20
  · exact check3_21
  · exact check3_22
  · exact check3_23
  · exact check3_24
  · exact check3_25
  · exact check3_26
  · exact check3_27
  · exact check3_28
  · exact check3_29
  · exact check3_30
  · exact check3_31
  · exact check3_32
  · exact check3_33
  · exact check3_34
  · exact check3_35
  · exact check3_36
  · exact check3_37
  · exact check3_38
  · exact check3_39
  · exact check3_40
  · exact check3_41
  · exact check3_42
  · exact check3_43
  · exact check3_44
private theorem check2_0 : checkChunk 139 F2 0 = true := by decide +kernel
private theorem check2_1 : checkChunk 139 F2 1 = true := by decide +kernel
private theorem check2_2 : checkChunk 139 F2 2 = true := by decide +kernel
private theorem check2_3 : checkChunk 139 F2 3 = true := by decide +kernel
private theorem check2_4 : checkChunk 139 F2 4 = true := by decide +kernel
private theorem check2_5 : checkChunk 139 F2 5 = true := by decide +kernel
private theorem check2_6 : checkChunk 139 F2 6 = true := by decide +kernel
private theorem check2_7 : checkChunk 139 F2 7 = true := by decide +kernel
private theorem check2_8 : checkChunk 139 F2 8 = true := by decide +kernel
private theorem check2_9 : checkChunk 139 F2 9 = true := by decide +kernel
private theorem check2_10 : checkChunk 139 F2 10 = true := by decide +kernel
private theorem check2_11 : checkChunk 139 F2 11 = true := by decide +kernel
private theorem check2_12 : checkChunk 139 F2 12 = true := by decide +kernel
private theorem check2_13 : checkChunk 139 F2 13 = true := by decide +kernel
private theorem check2_14 : checkChunk 139 F2 14 = true := by decide +kernel
private theorem check2_15 : checkChunk 139 F2 15 = true := by decide +kernel
private theorem check2_16 : checkChunk 139 F2 16 = true := by decide +kernel
private theorem check2_17 : checkChunk 139 F2 17 = true := by decide +kernel
private theorem layer2 (i : Fin L2.size) : ¬Reach 4 (L2[i.val]).toFinset := by
  apply nodeLayer (instructions := E2) (next := L3) ?_ layer3
  change ∀ j : Fin 139, F2 j.val = true
  apply checkedChunk
  intro b
  change Fin 18 at b
  fin_cases b
  · exact check2_0
  · exact check2_1
  · exact check2_2
  · exact check2_3
  · exact check2_4
  · exact check2_5
  · exact check2_6
  · exact check2_7
  · exact check2_8
  · exact check2_9
  · exact check2_10
  · exact check2_11
  · exact check2_12
  · exact check2_13
  · exact check2_14
  · exact check2_15
  · exact check2_16
  · exact check2_17
private theorem check1_0 : checkChunk 6 F1 0 = true := by decide +kernel
private theorem layer1 (i : Fin L1.size) : ¬Reach 5 (L1[i.val]).toFinset := by
  apply nodeLayer (instructions := E1) (next := L2) ?_ layer2
  change ∀ j : Fin 6, F1 j.val = true
  apply checkedChunk
  intro b
  change Fin 1 at b
  fin_cases b
  · exact check1_0
private theorem check0_0 : checkChunk 1 F0 0 = true := by decide +kernel
private theorem layer0 (i : Fin L0.size) : ¬Reach 6 (L0[i.val]).toFinset := by
  apply nodeLayer (instructions := E0) (next := L1) ?_ layer1
  change ∀ j : Fin 1, F0 j.val = true
  apply checkedChunk
  intro b
  change Fin 1 at b
  fin_cases b
  · exact check0_0
theorem terminal : ¬Reach 6 ∅ := layer0 ⟨0,by decide⟩
end PEqualNP.Outside.Fano1023

theorem PEqualNP.Outside.L_meta_1023 : ¬ (∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (w : Fin 7) (x : Fin 7 → Bool), ((Finset.univ.filter (fun p : Fin 7 => x p = false)).card = 4 ∨ (Finset.univ.filter (fun p : Fin 7 => x p = false)).card = 5) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) ∧ gates.length ≤ 13) := by
  rintro ⟨gs,ol,hg,he,hl⟩
  have hvalid (g) (h : g ∈ gs) : PEqualNP.Outside.Anchor1023.valid g := by
    obtain ⟨hop,hf⟩ := hg g h
    exact ⟨hop.imp_right Or.inl,hf⟩
  obtain ⟨hh,ht,hs,hq⟩ := PEqualNP.Outside.Fano1023.wide_history gs ol hvalid
    (fun g h => (hg g h).1) he hl
  exact PEqualNP.Outside.Fano1023.terminal (PEqualNP.Outside.Fano1023.reach_of_history hh ht hs hq)
