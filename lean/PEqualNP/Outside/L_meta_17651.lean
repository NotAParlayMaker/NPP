import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17651
open PEqualNP.HeptadCover

private abbrev V := Fin 13
private abbrev S := singerLines3
private abbrev Code := ℕ × ℕ × ℕ × Bool

private def graphInput (U W : Finset V) : Fin 26 → Bool :=
  Fin.append (fun p => decide (p ∈ U)) (fun l => decide (l ∈ W))

private def ok (f : (Fin 26 → Bool) → Bool × Bool) : Prop :=
  (∀ p l, p ∈ S l → f (graphInput {p} {l}) ≠ (false,false)) ∧
  ∀ Q, IsQuadrangle S Q → f (graphInput Q (missLines S Q)) = (false,false)

private def digit (a : ℕ) (i : V) : V := Fin.ofNat 13 ((a / (13^i.val)) % 13)

private def rflag (i : ℕ) : V × V := ([(0,4),(1,0),(1,1),(2,1)] : List (V × V)).getD i (0,0)

private def valid (d : Code) (u p l : V) : Prop :=
  let P := digit d.1
  let L := digit d.2.1
  let flag := rflag d.2.2.1
  let fstFlag := (P 0,L 0)
  let sndFlag := (P flag.1,L flag.2)
  (∀ a b, P a = P b → a = b) ∧ (∀ a b, L a = L b → a = b) ∧
  (∀ a b, P a ∈ S (L b) ↔ a ∈ S b) ∧
  13 * flag.1.val + flag.2.val ∈ ([4,13,14,27] : List ℕ) ∧
  (if d.2.2.2 then sndFlag = (u,0) ∧ fstFlag = (p,l) else
     fstFlag = (u,0) ∧ sndFlag = (p,l))

private instance (d : Code) (u p l : V) : Decidable (valid d u p l) := by
  unfold valid
  infer_instance

private def table0 : List Code :=
  [(0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (300771807240918, 300771807240918, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (292712634440538, 299880257189370, 0, false), (0, 0, 0, false),
    (184215622252974, 114361134130698, 0, false), (300771807240918, 300771807240918, 1, false), (300771807240918, 300771807240918, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (183727016788926, 114355075001466, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (128795459170482, 103555920080262, 2, false), (0, 0, 0, false), (0, 0, 0, false), (300771807240918, 300771807240918, 3, false),
    (205928427424590, 293593627151838, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (298364484230358, 297122900052966, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (245105782912278, 42145284342030, 2, true), (205928427424590, 293593627151838, 1, false),
    (0, 0, 0, false), (205928427424590, 293593627151838, 2, false), (181935426068058, 107187370206150, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (105339377994786, 99962708679054, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (184968488086278, 114631541568726, 3, false), (0, 0, 0, false), (181935426068058, 107187370206150, 3, false),
    (62257377028422, 45976836532410, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (135966779493402, 110727995364402, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (177798987362490, 107462025606702, 3, false),
    (0, 0, 0, false), (159032347435902, 135722652693138, 2, true), (183727016788926, 114355075001466, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (114301536399102, 108928252049214, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (246097512716094, 246097512716094, 3, false), (0, 0, 0, false), (269554095651438, 253273548590166, 3, false),
    (254782424524134, 250784326942266, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (124196316186078, 124100874489966, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (274677343142898, 275194317330066, 2, true),
    (0, 0, 0, false), (135253857038586, 110754451841514, 3, false), (105339377994786, 99962708679054, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (128795459170482, 103555920080262, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (300151870871658, 300703226467722, 3, false), (0, 0, 0, false), (67709257175586, 284560094827086, 3, false),
    (58907667768378, 291732952423770, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (158255748565026, 135416374389282, 2, true), (298364484230358, 297122900052966, 1, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (298364484230358, 297122900052966, 2, false),
    (0, 0, 0, false), (135966779493402, 110727995364402, 2, false), (114301536399102, 108928252049214, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (278097765788154, 254372985920898, 3, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (148027353377514, 238979653987854, 3, false), (0, 0, 0, false), (264174115130250, 247893574660602, 3, false),
    (61467730185534, 45796997235090, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (247609849055478, 247195389873510, 3, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (242509373795598, 249676655818278, 3, false),
    (0, 0, 0, false), (171569732832522, 264617113445526, 2, true), (149818442338734, 242564534310306, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (205146166159194, 293554997836074, 3, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (58745341844046, 291723747329586, 3, false), (0, 0, 0, false), (198751522414614, 290006308177638, 3, false),
    (275532215024910, 275532215024910, 2, true)]

private def table1 : List Code :=
  [(300771807240918, 300771807240918, 1, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (69171259678782, 46391903548770, 2, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (130590641089650, 125202950686242, 2, false), (0, 0, 0, false),
    (254448033249294, 42838317663570, 2, false), (0, 0, 0, false), (160569937123506, 135999112977078, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (254448033249294, 42838317663570, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (244872475274454, 41986173671910, 0, false), (0, 0, 0, false), (0, 0, 0, false), (293476162639662, 300219639541758, 2, true),
    (247046242616850, 37469520395034, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (113879833519206, 39202887642594, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (254448033249294, 42838317663570, 3, false), (247046242616850, 37469520395034, 1, false),
    (0, 0, 0, false), (247046242616850, 37469520395034, 2, false), (247277904952638, 37460778674514, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (291442100984022, 262480643375730, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (184067168202870, 114074855834382, 2, true), (0, 0, 0, false), (247277904952638, 37460778674514, 3, false),
    (69171259678782, 46391903548770, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (60698143717446, 35595055488018, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (200547268977186, 130642394256270, 3, false),
    (0, 0, 0, false), (160569937123506, 135999112977078, 3, false), (185900876279214, 114213456141426, 2, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (207757927418250, 132479773299666, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (200588865751626, 130683122490882, 3, false), (0, 0, 0, false), (278260075919442, 253137200719122, 2, true),
    (138968567759646, 134189009846814, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (130590641089650, 125202950686242, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (267763460414958, 274914091964850, 3, false),
    (0, 0, 0, false), (289406428570338, 273131781611286, 3, false), (291442100984022, 262480643375730, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (131361622441446, 103146123825678, 2, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (292601718416262, 300292677514926, 2, true), (0, 0, 0, false), (162359269172790, 123454609181358, 3, false),
    (139550163764766, 134160632300058, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (161193131959458, 135962517975414, 3, false), (113879833519206, 39202887642594, 1, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (113879833519206, 39202887642594, 2, false),
    (0, 0, 0, false), (60698143717446, 35595055488018, 2, false), (207757927418250, 132479773299666, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (269264531683170, 253685976684258, 2, true),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (115665337815210, 30243642144846, 3, false), (0, 0, 0, false), (114594389834250, 39186045795702, 3, false),
    (69654152629842, 46344646870782, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (178123618247550, 269566172492682, 3, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (289647058801218, 273228679039290, 3, false),
    (0, 0, 0, false), (172980068686842, 264208070315358, 3, false), (155449243021122, 243114442722006, 2, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (178356095971158, 269584176115254, 3, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (271343316557262, 271332698827554, 3, false), (0, 0, 0, false), (196704916676670, 289865442555258, 2, true),
    (268236570425838, 274980047325906, 3, false)]

private def table3 : List Code :=
  [(205928427424590, 293593627151838, 1, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (158781083117634, 88852570695486, 2, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (107136794869302, 78048077325894, 2, false), (0, 0, 0, false),
    (275403339479622, 65575305498534, 2, false), (247046242616850, 37469520395034, 1, true), (270207516636450, 67384876558038, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (270024801903834, 67365471304794, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (198800436681018, 172596969093822, 2, false), (0, 0, 0, false), (0, 0, 0, false), (277895465071278, 68077909879422, 3, true),
    (200297626397286, 293043718370886, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (138080222501574, 64431971012142, 3, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (268362202600182, 65434439847750, 3, true), (0, 0, 0, false),
    (0, 0, 0, false), (158781083117634, 88852570695486, 0, false), (275403339479622, 65575305498534, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (268701533406738, 65052649074894, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (293601794787642, 90674032063758, 3, false), (0, 0, 0, false), (178732992463770, 106908650634906, 2, true),
    (158781083117634, 88852570695486, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (298606736319258, 87124455015546, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (182273960336382, 107043193594170, 2, true),
    (0, 0, 0, false), (62003679967830, 69137994735030, 3, false), (270024801903834, 67365471304794, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (60539872393458, 58334374291830, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (247507848304086, 246233107264134, 2, true), (0, 0, 0, false), (293229014493678, 90704096765646, 3, false),
    (108505162272510, 85249496632482, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (107136794869302, 78048077325894, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (244303126963314, 181437018042774, 3, false),
    (0, 0, 0, false), (242235308258778, 179507248696230, 3, false), (114946677960810, 100103574102474, 2, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (198800436681018, 172596969093822, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (185523979766154, 183285570778986, 3, false), (0, 0, 0, false), (55811385421566, 283869320650962, 2, true),
    (255054868296738, 179649469853646, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (252987049631514, 181303896536022, 3, false), (135386805289518, 63741949761594, 1, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (135386805289518, 63741949761594, 2, false),
    (0, 0, 0, false), (298606736319258, 87124455015546, 2, false), (60539872393458, 58334374291830, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (185151201528582, 183266694617994, 3, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (162618642340398, 239671180947270, 2, true), (0, 0, 0, false), (195214054657170, 177968712198498, 3, false),
    (171184727449674, 170739327472038, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (245690497521090, 247058289304218, 2, true), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (135527922562230, 63745269862950, 3, false),
    (0, 0, 0, false), (62327509916766, 69082406986398, 3, false), (131794776277830, 56574613661670, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (199133603390058, 293696616554058, 2, true),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (108924432353298, 85211913991542, 3, false), (0, 0, 0, false), (155189869816842, 79890514510482, 3, false),
    (158827575989046, 88835263618530, 3, false)]

private def table9 : List Code :=
  [(298364484230358, 297122900052966, 1, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (274928607448998, 205574263334934, 2, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (69497522435454, 162555204519630, 2, false), (0, 0, 0, false),
    (159402656274546, 158989066327338, 2, false), (113879833519206, 39202887642594, 1, true), (183357482289198, 160655966605290, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (300402270514446, 230635268767722, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (150437611623594, 150024271483710, 2, false), (0, 0, 0, false), (0, 0, 0, false), (184640563781442, 161202110191266, 3, true),
    (177482482837194, 154035104140842, 3, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (289022233866810, 296018564682990, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (160049467804410, 158027102401986, 3, true), (135386805289518, 63741949761594, 1, true),
    (0, 0, 0, false), (181702948353078, 153625308255510, 2, false), (205970024150874, 200306651930502, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (56951805887622, 144628923052146, 2, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (278226641476242, 206543488751874, 3, true), (0, 0, 0, false), (199066683173622, 199618136445510, 3, true),
    (267505708724622, 204745635238278, 3, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (138532942659414, 109766031325530, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (247487460347730, 222938295033846, 3, true),
    (0, 0, 0, false), (243924608540358, 228307447570674, 3, true), (292215847914138, 230081595047322, 3, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (107779957292142, 108235971511170, 2, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (181052806252662, 153756244647606, 3, true), (0, 0, 0, false), (182855816990346, 160925706343914, 3, true),
    (242110486906554, 249812574418686, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (61183845710682, 162000777788574, 3, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (159695475992670, 159281322897090, 3, true),
    (0, 0, 0, false), (138201782392434, 110893811328930, 2, true), (66559105617882, 144908395179594, 3, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (154668618338202, 149756093861970, 3, true), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (269294722008450, 207088159102674, 3, true), (0, 0, 0, false), (104198957253438, 192469951197882, 3, true),
    (59681733393654, 291325415314578, 2, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (274638999876522, 205293537952710, 3, true), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (274928607448998, 205574263334934, 0, false),
    (0, 0, 0, false), (159402656274546, 158989066327338, 0, false), (160622106617046, 158875423960578, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (299878592063982, 230533130168718, 3, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (287853040166766, 216292995083646, 3, false), (0, 0, 0, false), (271087997435694, 248308641307710, 2, true),
    (125217591637602, 217978660463694, 3, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (205009944249834, 200224673794626, 3, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (254672295203142, 250640125225134, 2, true),
    (0, 0, 0, false), (103549355807478, 194809229104074, 3, false), (197003473485282, 196716963364194, 3, false), (0, 0, 0, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (247884744748026, 223345744975314, 3, false),
    (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false), (0, 0, 0, false),
    (0, 0, 0, false), (59392153502538, 291863106930534, 2, true), (0, 0, 0, false), (132384519723270, 219773997640314, 3, false),
    (244024939469346, 228446384468406, 3, false)]

private def lookup (u p l : V) : Code :=
  let t := if u = 0 then table0 else if u = 1 then table1 else if u = 3 then table3 else table9
  t.getD (13*p.val+l.val) (0,0,0,false)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check0 : ∀ p l : V, p ∈ S l → ((0 : V),0) ≠ (p,l) →
    valid (lookup 0 p l) 0 p l := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check1 : ∀ p l : V, p ∈ S l → ((1 : V),0) ≠ (p,l) →
    valid (lookup 1 p l) 1 p l := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check3 : ∀ p l : V, p ∈ S l → ((3 : V),0) ≠ (p,l) →
    valid (lookup 3 p l) 3 p l := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem check9 : ∀ p l : V, p ∈ S l → ((9 : V),0) ≠ (p,l) →
    valid (lookup 9 p l) 9 p l := by
  decide +kernel

private theorem norm (u p l : V) (hu : u ∈ S 0) (hp : p ∈ S l) (hd : (u,0) ≠ (p,l)) :
    valid (lookup u p l) u p l := by
  have h : u = 0 ∨ u = 1 ∨ u = 3 ∨ u = 9 := by
    have hsmall : ∀ u : V, u ∈ S 0 → u = 0 ∨ u = 1 ∨ u = 3 ∨ u = 9 := by decide +kernel
    exact hsmall u hu
  rcases h with rfl | rfl | rfl | rfl
  · simpa [lookup] using check0 p l hp hd
  · simpa [lookup] using check1 p l hp hd
  · simpa [lookup] using check3 p l hp hd
  · simpa [lookup] using check9 p l hp hd

private def addPerm (j : V) : Equiv.Perm V :=
  ⟨fun i => i+j, fun i => i-j, by intro i; simp, by intro i; simp⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem add_inc : ∀ j p l : V, p+j ∈ S (l+j) ↔ p ∈ S l := by
  decide +kernel

private def rename (P L : Equiv.Perm V) : Equiv.Perm (Fin 26) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr P.symm L.symm).trans finSumFinEquiv)

private theorem renameInput (P L : Equiv.Perm V) (U W : Finset V) :
    graphInput U W ∘ rename P L = graphInput (U.map P.toEmbedding) (W.map L.toEmbedding) := by
  funext i
  refine Fin.addCases (m:=13) (n:=13) (fun p => ?_) (fun l => ?_) i
  · have hh : rename P L (Fin.castAdd 13 p) = Fin.castAdd 13 (P.symm p) := by
      unfold rename
      rw [Equiv.trans_apply, Equiv.trans_apply, @finSumFinEquiv_symm_apply_castAdd 13 13 p]
      rfl
    change graphInput U W (rename P L (Fin.castAdd 13 p)) = _
    rw [hh]
    simp only [graphInput,Fin.append_left,Finset.mem_map_equiv]
  · have hh : rename P L (Fin.natAdd 13 l) = Fin.natAdd 13 (L.symm l) := by
      unfold rename
      rw [Equiv.trans_apply, Equiv.trans_apply, @finSumFinEquiv_symm_apply_natAdd 13 13 l]
      rfl
    change graphInput U W (rename P L (Fin.natAdd 13 l)) = _
    rw [hh]
    simp only [graphInput,Fin.append_right,Finset.mem_map_equiv]

private def swapIf (b : Bool) (r : Bool × Bool) : Bool × Bool :=
  if b = true then r.swap else r

private theorem preserve (P L : Equiv.Perm V) (inc : ∀ p l, P p ∈ S (L l) ↔ p ∈ S l)
    (b : Bool) (f : (Fin 26 → Bool) → Bool × Bool) (hf : ok f) :
    ok (fun x => swapIf b (f (x ∘ rename P L))) := by
  have line (l : V) : (S l).map P.toEmbedding = S (L l) := by
    ext i
    obtain ⟨p,rfl⟩ := P.surjective i
    exact (Finset.mem_map' P.toEmbedding).trans (inc p l).symm
  constructor
  · intro p l hi
    change swapIf b (f (graphInput {p} {l} ∘ rename P L)) ≠ _
    rw [renameInput]
    simp only [Finset.map_singleton, Equiv.toEmbedding_apply]
    have hn := hf.1 (P p) (L l) ((inc p l).mpr hi)
    cases b <;> cases he : f (graphInput {P p} {L l}) <;> simp_all [swapIf, Prod.ext_iff, and_comm]
  · intro Q hQ
    have hq : IsQuadrangle S (Q.map P.toEmbedding) := by
      refine ⟨by simpa using hQ.1,?_⟩
      intro i
      obtain ⟨l,rfl⟩ := L.surjective i
      rw [← line, ← Finset.map_inter, Finset.card_map]
      exact hQ.2 l
    have hm : (missLines S Q).map L.toEmbedding = missLines S (Q.map P.toEmbedding) := by
      ext i
      obtain ⟨l,rfl⟩ := L.surjective i
      rw [Finset.mem_map_equiv]
      simp only [Equiv.symm_apply_apply]
      change l ∈ missLines S Q ↔ L l ∈ missLines S (Q.map P.toEmbedding)
      simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, ← line, Finset.disjoint_map]
    change swapIf b (f (graphInput Q (missLines S Q) ∘ rename P L)) = _
    rw [renameInput, hm, hf.2 _ hq]
    cases b <;> rfl

private theorem normalize (u s p l : V) (hu : u ∈ S s) (hp : p ∈ S l) (hne : (u,s) ≠ (p,l)) :
    ∃ (P L : Equiv.Perm V) (b : Bool) (r t : V),
      (∀ i j, P i ∈ S (L j) ↔ i ∈ S j) ∧
      13*r.val+t.val ∈ ([4,13,14,27] : List ℕ) ∧
      (if b then (P r,L t) = (u,s) ∧ (P 0,L 0) = (p,l)
       else (P 0,L 0) = (u,s) ∧ (P r,L t) = (p,l)) := by
  have hu' : u-s ∈ S 0 := by
    apply (add_inc s (u-s) 0).mp
    simpa using hu
  have hp' : p-s ∈ S (l-s) := by
    apply (add_inc s (p-s) (l-s)).mp
    simpa using hp
  have ne : (u-s,0) ≠ (p-s,l-s) := by
    intro h
    apply hne
    have hh := congrArg (fun x : V × V => (x.1+s,x.2+s)) h
    simpa using hh
  let d := lookup (u-s) (p-s) (l-s)
  obtain ⟨hP,hL,hinc,hflag,hends⟩ := norm (u-s) (p-s) (l-s) hu' hp' ne
  let P₀ : Equiv.Perm V := Equiv.ofBijective (digit d.1) ⟨hP,Finite.injective_iff_surjective.mp hP⟩
  let L₀ : Equiv.Perm V := Equiv.ofBijective (digit d.2.1) ⟨hL,Finite.injective_iff_surjective.mp hL⟩
  let P := P₀.trans (addPerm s)
  let L := L₀.trans (addPerm s)
  refine ⟨P,L,d.2.2.2,(rflag d.2.2.1).1,(rflag d.2.2.1).2,?_,hflag,?_⟩
  · intro i j
    change digit d.1 i + s ∈ S (digit d.2.1 j+s) ↔ i ∈ S j
    exact (add_inc s _ _).trans (hinc i j)
  · have shift (x y a b : V) (he : (digit d.1 x,digit d.2.1 y) = (a-s,b-s)) :
        (P x,L y) = (a,b) := by
      have hh := congrArg (fun z : V × V => (z.1+s,z.2+s)) he
      change (digit d.1 x+s,digit d.2.1 y+s) = (a,b)
      simpa using hh
    have shift0 (x y : V) (he : (digit d.1 x,digit d.2.1 y) = (u-s,0)) :
        (P x,L y) = (u,s) := shift x y u s (by simpa using he)
    change (if d.2.2.2 then _ else _) at hends
    cases hb : d.2.2.2
    · simp only [hb, Bool.false_eq_true, ite_false] at hends ⊢
      exact ⟨shift0 _ _ hends.1,shift _ _ p l hends.2⟩
    · simp only [hb, ite_true] at hends ⊢
      exact ⟨shift0 _ _ hends.1,shift _ _ p l hends.2⟩

end PEqualNP.Outside.L_meta_17651

open PEqualNP.Outside.L_meta_17651

theorem PEqualNP.Outside.L_meta_17651 : (have x1 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x1 x2 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x1)) fun (x3 : Fin (13 : ℕ)) => Decidable.decide (x3 ∈ x2); have x2 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x2 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2 (x1 {x3} {x4}) ≠ (Bool.false, Bool.false)) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2 (x1 x3 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x3)) = (Bool.false, Bool.false); have x3 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Bool × Bool → Prop := fun (x3 : (Fin (26 : ℕ) → Bool) → Bool × Bool) (x4 : Bool × Bool) => ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (x1 {x5} {x6}) = x4; have x4 : ((Fin (26 : ℕ) → Bool) → Bool × Bool) → Prop := fun (x4 : (Fin (26 : ℕ) → Bool) → Bool × Bool) => x4 (x1 {(0 : Fin (13 : ℕ))} {(0 : Fin (13 : ℕ))}) = (Bool.true, Bool.false) ∧ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (13 : ℕ) * ↑x5 + ↑x6 ∈ [(4 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ)] ∧ x4 (x1 {x5} {x6}) = (Bool.false, Bool.true); have x5 : Bool → Bool × Bool → Bool × Bool := fun (x5 : Bool) (x6 : Bool × Bool) => if x5 = Bool.true then x6.swap else x6; ∀ (x6 : (Fin (26 : ℕ) → Bool) → Bool × Bool),   x2 x6 →     x3 x6 (Bool.true, Bool.false) →       x3 x6 (Bool.false, Bool.true) →         ∃ (x10 : Equiv.Perm (Fin (26 : ℕ))) (x11 : Bool),           have x12 : (Fin (26 : ℕ) → Bool) → Bool × Bool := fun (x12 : Fin (26 : ℕ) → Bool) => x5 x11 (x6 (x12 ∘ ⇑x10));           x2 x12 ∧ x4 x12) := by
  dsimp only
  intro f hf h1 h2
  obtain ⟨u,s,hu,hblue⟩ := h1
  obtain ⟨p,l,hp,hred⟩ := h2
  change f (graphInput {u} {s}) = (true,false) at hblue
  change f (graphInput {p} {l}) = (false,true) at hred
  have hne : (u,s) ≠ (p,l) := by
    intro h
    have he : u = p ∧ s = l := Prod.mk.inj h
    rcases he with ⟨rfl,rfl⟩
    rw [hblue] at hred
    contradiction
  obtain ⟨P,L,b,r,t,hinc,hrep,hends⟩ := normalize u s p l hu hp hne
  refine ⟨rename P L,b,preserve P L hinc b f hf,?_,⟨r,t,hrep,?_⟩⟩
  all_goals
    change swapIf b (f (graphInput _ _ ∘ rename P L)) = _
    rw [renameInput]
    simp only [Finset.map_singleton, Equiv.toEmbedding_apply]
  · cases hb : b <;> simp [hb] at hends
    · obtain ⟨a,σ⟩ := hends.1
      simp [swapIf,a,σ,hblue]
    · obtain ⟨a,σ⟩ := hends.2
      simp [swapIf,a,σ,hred]
  · cases hb : b <;> simp [hb] at hends
    · obtain ⟨a,σ⟩ := hends.2
      simp [swapIf,a,σ,hred]
    · obtain ⟨a,σ⟩ := hends.1
      simp [swapIf,a,σ,hblue]
