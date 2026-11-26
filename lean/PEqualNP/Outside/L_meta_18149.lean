import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18149


private abbrev R (p l : Fin 13) : Prop := p ≠ 0 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
private def readDigit (w : Nat) (x : Fin 13) : Fin 13 := Fin.ofNat 13 ((w >>> (4 * x.val)) % 16)
private def pairCode (a b : Nat) : Nat := 26 * min a b + max a b
private def representatives : List Nat := [0, 1, 13, 14, 27, 28, 29, 39, 40, 41, 43, 351, 352, 355, 378, 379]
private def p0 : Equiv.Perm (Fin 13) := { toFun := readDigit 3582863703552528, invFun := readDigit 3582863703552528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l0 : Equiv.Perm (Fin 13) := { toFun := readDigit 3582863703552528, invFun := readDigit 3582863703552528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel0 : ∀ p l, R (p0 p) (l0 l) ↔ R p l := by decide +kernel
private def p1 : Equiv.Perm (Fin 13) := { toFun := readDigit 2651478636741408, invFun := readDigit 1027809216897408, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l1 : Equiv.Perm (Fin 13) := { toFun := readDigit 117122534773548, invFun := readDigit 134387035545948, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel1 : ∀ p l, R (p1 p) (l1 l) ↔ R p l := by decide +kernel
private def p2 : Equiv.Perm (Fin 13) := { toFun := readDigit 1147648168658208, invFun := readDigit 2611767552025008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l2 : Equiv.Perm (Fin 13) := { toFun := readDigit 1143747532981548, invFun := readDigit 145562702483898, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel2 : ∀ p l, R (p2 p) (l2 l) ↔ R p l := by decide +kernel
private def p3 : Equiv.Perm (Fin 13) := { toFun := readDigit 3456556210954848, invFun := readDigit 3539639875629648, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l3 : Equiv.Perm (Fin 13) := { toFun := readDigit 3435666517037418, invFun := readDigit 3536271814866468, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel3 : ∀ p l, R (p3 p) (l3 l) ↔ R p l := by decide +kernel
private def p4 : Equiv.Perm (Fin 13) := { toFun := readDigit 2380565691732528, invFun := readDigit 2330125884854928, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l4 : Equiv.Perm (Fin 13) := { toFun := readDigit 3505636347905568, invFun := readDigit 3523332173091168, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel4 : ∀ p l, R (p4 p) (l4 l) ↔ R p l := by decide +kernel
private def p5 : Equiv.Perm (Fin 13) := { toFun := readDigit 424726844109648, invFun := readDigit 1765314087430848, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l5 : Equiv.Perm (Fin 13) := { toFun := readDigit 101259820054308, invFun := readDigit 2872302994743708, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel5 : ∀ p l, R (p5 p) (l5 l) ↔ R p l := by decide +kernel
private def p6 : Equiv.Perm (Fin 13) := { toFun := readDigit 3035182826341968, invFun := readDigit 3250682808456768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l6 : Equiv.Perm (Fin 13) := { toFun := readDigit 2986804112266068, invFun := readDigit 2969469891650868, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel6 : ∀ p l, R (p6 p) (l6 l) ↔ R p l := by decide +kernel
private def p7 : Equiv.Perm (Fin 13) := { toFun := readDigit 3537621279459408, invFun := readDigit 3474124220623008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l7 : Equiv.Perm (Fin 13) := { toFun := readDigit 3536811467618388, invFun := readDigit 3541193691510138, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel7 : ∀ p l, R (p7 p) (l7 l) ↔ R p l := by decide +kernel
private def p8 : Equiv.Perm (Fin 13) := { toFun := readDigit 3159490975745568, invFun := readDigit 1065054220169568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l8 : Equiv.Perm (Fin 13) := { toFun := readDigit 2850516460942188, invFun := readDigit 66492559534938, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel8 : ∀ p l, R (p8 p) (l8 l) ↔ R p l := by decide +kernel
private def p9 : Equiv.Perm (Fin 13) := { toFun := readDigit 2863519533069888, invFun := readDigit 2969051610565488, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l9 : Equiv.Perm (Fin 13) := { toFun := readDigit 2846166203004468, invFun := readDigit 2951730004236468, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel9 : ∀ p l, R (p9 p) (l9 l) ↔ R p l := by decide +kernel
private def p10 : Equiv.Perm (Fin 13) := { toFun := readDigit 1595630919619728, invFun := readDigit 2158429485569328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l10 : Equiv.Perm (Fin 13) := { toFun := readDigit 1295395211465088, invFun := readDigit 1260802769971488, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel10 : ∀ p l, R (p10 p) (l10 l) ↔ R p l := by decide +kernel
private def p11 : Equiv.Perm (Fin 13) := { toFun := readDigit 2676708384330048, invFun := readDigit 1817267590498848, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l11 : Equiv.Perm (Fin 13) := { toFun := readDigit 154374734779668, invFun := readDigit 2924956633552668, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel11 : ∀ p l, R (p11 p) (l11 l) ↔ R p l := by decide +kernel
private def p12 : Equiv.Perm (Fin 13) := { toFun := readDigit 923185059117408, invFun := readDigit 2033158621742208, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l12 : Equiv.Perm (Fin 13) := { toFun := readDigit 57663045773418, invFun := readDigit 1249468554589068, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel12 : ∀ p l, R (p12 p) (l12 l) ↔ R p l := by decide +kernel
private def p13 : Equiv.Perm (Fin 13) := { toFun := readDigit 1308655794820368, invFun := readDigit 1525248284202768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l13 : Equiv.Perm (Fin 13) := { toFun := readDigit 1154725088889168, invFun := readDigit 1225008543995568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel13 : ∀ p l, R (p13 p) (l13 l) ↔ R p l := by decide +kernel
private def p14 : Equiv.Perm (Fin 13) := { toFun := readDigit 3225120003364368, invFun := readDigit 2190453498090768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l14 : Equiv.Perm (Fin 13) := { toFun := readDigit 3012831831950928, invFun := readDigit 1333104196872528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel14 : ∀ p l, R (p14 p) (l14 l) ↔ R p l := by decide +kernel
private def p15 : Equiv.Perm (Fin 13) := { toFun := readDigit 3189245809006128, invFun := readDigit 1346443838887728, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l15 : Equiv.Perm (Fin 13) := { toFun := readDigit 2854920973497648, invFun := readDigit 1192460460628848, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel15 : ∀ p l, R (p15 p) (l15 l) ↔ R p l := by decide +kernel
private def p16 : Equiv.Perm (Fin 13) := { toFun := readDigit 767580822804528, invFun := readDigit 2456524906896528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l16 : Equiv.Perm (Fin 13) := { toFun := readDigit 3423997676251248, invFun := readDigit 3529922276776848, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel16 : ∀ p l, R (p16 p) (l16 l) ↔ R p l := by decide +kernel
private def p17 : Equiv.Perm (Fin 13) := { toFun := readDigit 2452265702227008, invFun := readDigit 763594628221008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l17 : Equiv.Perm (Fin 13) := { toFun := readDigit 3529786275167028, invFun := readDigit 3424339702585428, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel17 : ∀ p l, R (p17 p) (l17 l) ↔ R p l := by decide +kernel
private def p18 : Equiv.Perm (Fin 13) := { toFun := readDigit 1716868132653648, invFun := readDigit 1269556296508848, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l18 : Equiv.Perm (Fin 13) := { toFun := readDigit 2903172526649748, invFun := readDigit 1279932092134698, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel18 : ∀ p l, R (p18 p) (l18 l) ↔ R p l := by decide +kernel
private def p19 : Equiv.Perm (Fin 13) := { toFun := readDigit 2578026139591008, invFun := readDigit 1851347553323808, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l19 : Equiv.Perm (Fin 13) := { toFun := readDigit 119307668590938, invFun := readDigit 2920549761439788, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel19 : ∀ p l, R (p19 p) (l19 l) ↔ R p l := by decide +kernel
private def p20 : Equiv.Perm (Fin 13) := { toFun := readDigit 436202556924768, invFun := readDigit 2976976343410368, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l20 : Equiv.Perm (Fin 13) := { toFun := readDigit 101947799770938, invFun := readDigit 2973595470140988, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel20 : ∀ p l, R (p20 p) (l20 l) ↔ R p l := by decide +kernel
private def p21 : Equiv.Perm (Fin 13) := { toFun := readDigit 2132662278730848, invFun := readDigit 1189352705271648, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l21 : Equiv.Perm (Fin 13) := { toFun := readDigit 1231973273876538, invFun := readDigit 1179237417228138, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel21 : ∀ p l, R (p21 p) (l21 l) ↔ R p l := by decide +kernel
private def p22 : Equiv.Perm (Fin 13) := { toFun := readDigit 1339914773444448, invFun := readDigit 3159198117165648, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l22 : Equiv.Perm (Fin 13) := { toFun := readDigit 1191978638281578, invFun := readDigit 2850498413377428, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel22 : ∀ p l, R (p22 p) (l22 l) ↔ R p l := by decide +kernel
private def p23 : Equiv.Perm (Fin 13) := { toFun := readDigit 2273387820137568, invFun := readDigit 626087339272368, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l23 : Equiv.Perm (Fin 13) := { toFun := readDigit 3466146676509498, invFun := readDigit 3413311805986698, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel23 : ∀ p l, R (p23 p) (l23 l) ↔ R p l := by decide +kernel
private def p24 : Equiv.Perm (Fin 13) := { toFun := readDigit 1525190571443328, invFun := readDigit 1027225377986928, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l24 : Equiv.Perm (Fin 13) := { toFun := readDigit 1225022139044748, invFun := readDigit 134352360712548, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel24 : ∀ p l, R (p24 p) (l24 l) ↔ R p l := by decide +kernel
private def p25 : Equiv.Perm (Fin 13) := { toFun := readDigit 2152999385417088, invFun := readDigit 962423958305088, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l25 : Equiv.Perm (Fin 13) := { toFun := readDigit 1260457784555868, invFun := readDigit 63933693851268, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel25 : ∀ p l, R (p25 p) (l25 l) ↔ R p l := by decide +kernel
private def p26 : Equiv.Perm (Fin 13) := { toFun := readDigit 2868812555077248, invFun := readDigit 998775087020448, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l26 : Equiv.Perm (Fin 13) := { toFun := readDigit 2937975440970588, invFun := readDigit 136570129885338, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel26 : ∀ p l, R (p26 p) (l26 l) ↔ R p l := by decide +kernel
private def p27 : Equiv.Perm (Fin 13) := { toFun := readDigit 1567249731335328, invFun := readDigit 2024980607034528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l27 : Equiv.Perm (Fin 13) := { toFun := readDigit 1284601959688218, invFun := readDigit 1249811199976218, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel27 : ∀ p l, R (p27 p) (l27 l) ↔ R p l := by decide +kernel
private def p28 : Equiv.Perm (Fin 13) := { toFun := readDigit 360380601108768, invFun := readDigit 2629085384376768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l28 : Equiv.Perm (Fin 13) := { toFun := readDigit 22761064519788, invFun := readDigit 163150527366588, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel28 : ∀ p l, R (p28 p) (l28 l) ↔ R p l := by decide +kernel
private def p29 : Equiv.Perm (Fin 13) := { toFun := readDigit 3189160178469408, invFun := readDigit 1058114195059008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l29 : Equiv.Perm (Fin 13) := { toFun := readDigit 2854904345442588, invFun := readDigit 66148494899988, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel29 : ∀ p l, R (p29 p) (l29 l) ↔ R p l := by decide +kernel
private def p30 : Equiv.Perm (Fin 13) := { toFun := readDigit 2969349033039408, invFun := readDigit 2969349033039408, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l30 : Equiv.Perm (Fin 13) := { toFun := readDigit 2951745099797808, invFun := readDigit 2951745099797808, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel30 : ∀ p l, R (p30 p) (l30 l) ↔ R p l := by decide +kernel
private def p31 : Equiv.Perm (Fin 13) := { toFun := readDigit 2753467608625488, invFun := readDigit 3192750712915488, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l31 : Equiv.Perm (Fin 13) := { toFun := readDigit 172088353254228, invFun := readDigit 2855128685118828, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel31 : ∀ p l, R (p31 p) (l31 l) ↔ R p l := by decide +kernel
private def p32 : Equiv.Perm (Fin 13) := { toFun := readDigit 1049420070930768, invFun := readDigit 1330570501277568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l32 : Equiv.Perm (Fin 13) := { toFun := readDigit 46708144486548, invFun := readDigit 1277712342727548, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel32 : ∀ p l, R (p32 p) (l32 l) ↔ R p l := by decide +kernel
private def p33 : Equiv.Perm (Fin 13) := { toFun := readDigit 724974939293808, invFun := readDigit 2344923690151008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l33 : Equiv.Perm (Fin 13) := { toFun := readDigit 3483429831841908, invFun := readDigit 3470617502316858, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel33 : ∀ p l, R (p33 p) (l33 l) ↔ R p l := by decide +kernel
private def p34 : Equiv.Perm (Fin 13) := { toFun := readDigit 1782076810013568, invFun := readDigit 2577536252531568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l34 : Equiv.Perm (Fin 13) := { toFun := readDigit 2907354017325708, invFun := readDigit 119302711317108, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel34 : ∀ p l, R (p34 p) (l34 l) ↔ R p l := by decide +kernel
private def p35 : Equiv.Perm (Fin 13) := { toFun := readDigit 2018791004976528, invFun := readDigit 2907206574422928, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l35 : Equiv.Perm (Fin 13) := { toFun := readDigit 1245408270119568, invFun := readDigit 2977568679293568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel35 : ∀ p l, R (p35 p) (l35 l) ↔ R p l := by decide +kernel
private def p36 : Equiv.Perm (Fin 13) := { toFun := readDigit 923080371937728, invFun := readDigit 357932498404128, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l36 : Equiv.Perm (Fin 13) := { toFun := readDigit 57691705319868, invFun := readDigit 22370730029868, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel36 : ∀ p l, R (p36 p) (l36 l) ↔ R p l := by decide +kernel
private def p37 : Equiv.Perm (Fin 13) := { toFun := readDigit 330376009896768, invFun := readDigit 2910985290591168, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l37 : Equiv.Perm (Fin 13) := { toFun := readDigit 31570552050228, invFun := readDigit 2977981747172028, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel37 : ∀ p l, R (p37 p) (l37 l) ↔ R p l := by decide +kernel
private def p38 : Equiv.Perm (Fin 13) := { toFun := readDigit 745984742349888, invFun := readDigit 680978241637488, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l38 : Equiv.Perm (Fin 13) := { toFun := readDigit 3406730939607348, invFun := readDigit 3494409172685748, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel38 : ∀ p l, R (p38 p) (l38 l) ↔ R p l := by decide +kernel
private def p39 : Equiv.Perm (Fin 13) := { toFun := readDigit 2944265387845248, invFun := readDigit 2687557307888448, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l39 : Equiv.Perm (Fin 13) := { toFun := readDigit 2942959431456348, invFun := readDigit 154574566090548, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel39 : ∀ p l, R (p39 p) (l39 l) ↔ R p l := by decide +kernel
private def p40 : Equiv.Perm (Fin 13) := { toFun := readDigit 2184273136858128, invFun := readDigit 3224415651379728, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l40 : Equiv.Perm (Fin 13) := { toFun := readDigit 1333059741446928, invFun := readDigit 3013238348064528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel40 : ∀ p l, R (p40 p) (l40 l) ↔ R p l := by decide +kernel
private def p41 : Equiv.Perm (Fin 13) := { toFun := readDigit 2175064963453968, invFun := readDigit 2175064963453968, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l41 : Equiv.Perm (Fin 13) := { toFun := readDigit 1330901168187408, invFun := readDigit 1330901168187408, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel41 : ∀ p l, R (p41 p) (l41 l) ↔ R p l := by decide +kernel
private def p42 : Equiv.Perm (Fin 13) := { toFun := readDigit 2124349389050928, invFun := readDigit 2910663978653328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l42 : Equiv.Perm (Fin 13) := { toFun := readDigit 1263019173242928, invFun := readDigit 2977970126591328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel42 : ∀ p l, R (p42 p) (l42 l) ↔ R p l := by decide +kernel
private def p43 : Equiv.Perm (Fin 13) := { toFun := readDigit 2113899896444208, invFun := readDigit 1767584213506608, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l43 : Equiv.Perm (Fin 13) := { toFun := readDigit 1262686448563488, invFun := readDigit 2872374155039088, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel43 : ∀ p l, R (p43 p) (l43 l) ↔ R p l := by decide +kernel
private def p44 : Equiv.Perm (Fin 13) := { toFun := readDigit 2456844072211008, invFun := readDigit 2456844072211008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l44 : Equiv.Perm (Fin 13) := { toFun := readDigit 3529963125887508, invFun := readDigit 3529963125887508, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel44 : ∀ p l, R (p44 p) (l44 l) ↔ R p l := by decide +kernel
private def p45 : Equiv.Perm (Fin 13) := { toFun := readDigit 2687557307888448, invFun := readDigit 2944265387845248, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l45 : Equiv.Perm (Fin 13) := { toFun := readDigit 154574566090548, invFun := readDigit 2942959431456348, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel45 : ∀ p l, R (p45 p) (l45 l) ↔ R p l := by decide +kernel
private def p46 : Equiv.Perm (Fin 13) := { toFun := readDigit 3250682808456768, invFun := readDigit 3035182826341968, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l46 : Equiv.Perm (Fin 13) := { toFun := readDigit 2969469891650868, invFun := readDigit 2986804112266068, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel46 : ∀ p l, R (p46 p) (l46 l) ↔ R p l := by decide +kernel
private def p47 : Equiv.Perm (Fin 13) := { toFun := readDigit 1044850296779088, invFun := readDigit 1608053910259488, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l47 : Equiv.Perm (Fin 13) := { toFun := readDigit 46421644180308, invFun := readDigit 1172458276166508, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel47 : ∀ p l, R (p47 p) (l47 l) ↔ R p l := by decide +kernel
private def p48 : Equiv.Perm (Fin 13) := { toFun := readDigit 3150625500579408, invFun := readDigit 1627709156603808, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l48 : Equiv.Perm (Fin 13) := { toFun := readDigit 2850720497566548, invFun := readDigit 1297782452267898, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel48 : ∀ p l, R (p48 p) (l48 l) ↔ R p l := by decide +kernel
private def p49 : Equiv.Perm (Fin 13) := { toFun := readDigit 767769261472848, invFun := readDigit 767769261472848, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l49 : Equiv.Perm (Fin 13) := { toFun := readDigit 3423984222759828, invFun := readDigit 3423984222759828, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel49 : ∀ p l, R (p49 p) (l49 l) ↔ R p l := by decide +kernel
private def p50 : Equiv.Perm (Fin 13) := { toFun := readDigit 1435569259460448, invFun := readDigit 1470764872656048, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l50 : Equiv.Perm (Fin 13) := { toFun := readDigit 1214485876190058, invFun := readDigit 1161734458725258, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel50 : ∀ p l, R (p50 p) (l50 l) ↔ R p l := by decide +kernel
private def p51 : Equiv.Perm (Fin 13) := { toFun := readDigit 692402754005088, invFun := readDigit 2413920629709888, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l51 : Equiv.Perm (Fin 13) := { toFun := readDigit 3487838120187738, invFun := readDigit 3518944738171188, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel51 : ∀ p l, R (p51 p) (l51 l) ↔ R p l := by decide +kernel
private def p52 : Equiv.Perm (Fin 13) := { toFun := readDigit 2738614061966208, invFun := readDigit 2738614061966208, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l52 : Equiv.Perm (Fin 13) := { toFun := readDigit 152398648861308, invFun := readDigit 152398648861308, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel52 : ∀ p l, R (p52 p) (l52 l) ↔ R p l := by decide +kernel
private def p53 : Equiv.Perm (Fin 13) := { toFun := readDigit 1032585137670528, invFun := readDigit 1032585137670528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l53 : Equiv.Perm (Fin 13) := { toFun := readDigit 134285211482508, invFun := readDigit 134285211482508, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel53 : ∀ p l, R (p53 p) (l53 l) ↔ R p l := by decide +kernel
private def p54 : Equiv.Perm (Fin 13) := { toFun := readDigit 399961757067648, invFun := readDigit 2715936988890048, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l54 : Equiv.Perm (Fin 13) := { toFun := readDigit 99725541119628, invFun := readDigit 169742790068028, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel54 : ∀ p l, R (p54 p) (l54 l) ↔ R p l := by decide +kernel
private def p55 : Equiv.Perm (Fin 13) := { toFun := readDigit 2014534758503568, invFun := readDigit 1764831178955568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l55 : Equiv.Perm (Fin 13) := { toFun := readDigit 1245138191561088, invFun := readDigit 2872274872723488, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel55 : ∀ p l, R (p55 p) (l55 l) ↔ R p l := by decide +kernel
private def p56 : Equiv.Perm (Fin 13) := { toFun := readDigit 1524574000919568, invFun := readDigit 1524574000919568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l56 : Equiv.Perm (Fin 13) := { toFun := readDigit 1225502224032528, invFun := readDigit 1225502224032528, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel56 : ∀ p l, R (p56 p) (l56 l) ↔ R p l := by decide +kernel
private def p57 : Equiv.Perm (Fin 13) := { toFun := readDigit 2088816979707168, invFun := readDigit 2716291050258768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l57 : Equiv.Perm (Fin 13) := { toFun := readDigit 1243219238090028, invFun := readDigit 169768165081428, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel57 : ∀ p l, R (p57 p) (l57 l) ↔ R p l := by decide +kernel
private def p58 : Equiv.Perm (Fin 13) := { toFun := readDigit 1314496594560288, invFun := readDigit 1032825921618288, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l58 : Equiv.Perm (Fin 13) := { toFun := readDigit 1155070072731948, invFun := readDigit 134318750708148, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel58 : ∀ p l, R (p58 p) (l58 l) ↔ R p l := by decide +kernel
private def p59 : Equiv.Perm (Fin 13) := { toFun := readDigit 2132521620587808, invFun := readDigit 921089142727008, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l59 : Equiv.Perm (Fin 13) := { toFun := readDigit 1231969310128428, invFun := readDigit 57349010911578, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel59 : ∀ p l, R (p59 p) (l59 l) ↔ R p l := by decide +kernel
private def p60 : Equiv.Perm (Fin 13) := { toFun := readDigit 2893412449240608, invFun := readDigit 998672815575408, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l60 : Equiv.Perm (Fin 13) := { toFun := readDigit 2837258434548588, invFun := readDigit 136582399665588, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel60 : ∀ p l, R (p60 p) (l60 l) ↔ R p l := by decide +kernel
private def p61 : Equiv.Perm (Fin 13) := { toFun := readDigit 2942411314337328, invFun := readDigit 1280070751229328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l61 : Equiv.Perm (Fin 13) := { toFun := readDigit 2942411314337328, invFun := readDigit 1280070751229328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel61 : ∀ p l, R (p61 p) (l61 l) ↔ R p l := by decide +kernel
private def p62 : Equiv.Perm (Fin 13) := { toFun := readDigit 1058114195059008, invFun := readDigit 3189160178469408, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l62 : Equiv.Perm (Fin 13) := { toFun := readDigit 66148494899988, invFun := readDigit 2854904345442588, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel62 : ∀ p l, R (p62 p) (l62 l) ↔ R p l := by decide +kernel
private def p63 : Equiv.Perm (Fin 13) := { toFun := readDigit 2411627146801728, invFun := readDigit 2380151515079328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l63 : Equiv.Perm (Fin 13) := { toFun := readDigit 3518822451148308, invFun := readDigit 3505840918124058, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel63 : ∀ p l, R (p63 p) (l63 l) ↔ R p l := by decide +kernel
private def p64 : Equiv.Perm (Fin 13) := { toFun := readDigit 3432092960182848, invFun := readDigit 3470507910476448, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l64 : Equiv.Perm (Fin 13) := { toFun := readDigit 3431263709598228, invFun := readDigit 3540657330237978, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel64 : ∀ p l, R (p64 p) (l64 l) ↔ R p l := by decide +kernel
private def p65 : Equiv.Perm (Fin 13) := { toFun := readDigit 3440725709256768, invFun := readDigit 3454262739843168, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l65 : Equiv.Perm (Fin 13) := { toFun := readDigit 3431105040136068, invFun := readDigit 3435497756080218, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel65 : ∀ p l, R (p65 p) (l65 l) ↔ R p l := by decide +kernel
private def p66 : Equiv.Perm (Fin 13) := { toFun := readDigit 325814816831808, invFun := readDigit 1767096473193408, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l66 : Equiv.Perm (Fin 13) := { toFun := readDigit 31140546786948, invFun := readDigit 2872342905641148, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel66 : ∀ p l, R (p66 p) (l66 l) ↔ R p l := by decide +kernel
private def p67 : Equiv.Perm (Fin 13) := { toFun := readDigit 1752049249704768, invFun := readDigit 2015012297225568, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l67 : Equiv.Perm (Fin 13) := { toFun := readDigit 2867971309195908, invFun := readDigit 1245134795616858, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel67 : ∀ p l, R (p67 p) (l67 l) ↔ R p l := by decide +kernel
private def p68 : Equiv.Perm (Fin 13) := { toFun := readDigit 2842607525329728, invFun := readDigit 1456458718865328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l68 : Equiv.Perm (Fin 13) := { toFun := readDigit 2832983551409028, invFun := readDigit 1174902119880378, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel68 : ∀ p l, R (p68 p) (l68 l) ↔ R p l := by decide +kernel
private def p69 : Equiv.Perm (Fin 13) := { toFun := readDigit 584221478779968, invFun := readDigit 659055023598768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l69 : Equiv.Perm (Fin 13) := { toFun := readDigit 3395452859476788, invFun := readDigit 3417717868599738, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel69 : ∀ p l, R (p69 p) (l69 l) ↔ R p l := by decide +kernel
private def p70 : Equiv.Perm (Fin 13) := { toFun := readDigit 3560460700291728, invFun := readDigit 3495451793134128, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l70 : Equiv.Perm (Fin 13) := { toFun := readDigit 3547262118834528, invFun := readDigit 3442250955920928, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel70 : ∀ p l, R (p70 p) (l70 l) ↔ R p l := by decide +kernel
private def p71 : Equiv.Perm (Fin 13) := { toFun := readDigit 1627378718291088, invFun := readDigit 3174403982636688, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l71 : Equiv.Perm (Fin 13) := { toFun := readDigit 1297816465580928, invFun := readDigit 2960647484351328, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel71 : ∀ p l, R (p71 p) (l71 l) ↔ R p l := by decide +kernel
private def p72 : Equiv.Perm (Fin 13) := { toFun := readDigit 2088063493223568, invFun := readDigit 1589983127418768, left_inv := by decide +kernel, right_inv := by decide +kernel }
private def l72 : Equiv.Perm (Fin 13) := { toFun := readDigit 1243226092368768, invFun := readDigit 1295573588911968, left_inv := by decide +kernel, right_inv := by decide +kernel }
private theorem rel72 : ∀ p l, R (p72 p) (l72 l) ↔ R p l := by decide +kernel
private def point (i : Fin 73) : Equiv.Perm (Fin 13) := match i.val with
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | 8 => p8
  | 9 => p9
  | 10 => p10
  | 11 => p11
  | 12 => p12
  | 13 => p13
  | 14 => p14
  | 15 => p15
  | 16 => p16
  | 17 => p17
  | 18 => p18
  | 19 => p19
  | 20 => p20
  | 21 => p21
  | 22 => p22
  | 23 => p23
  | 24 => p24
  | 25 => p25
  | 26 => p26
  | 27 => p27
  | 28 => p28
  | 29 => p29
  | 30 => p30
  | 31 => p31
  | 32 => p32
  | 33 => p33
  | 34 => p34
  | 35 => p35
  | 36 => p36
  | 37 => p37
  | 38 => p38
  | 39 => p39
  | 40 => p40
  | 41 => p41
  | 42 => p42
  | 43 => p43
  | 44 => p44
  | 45 => p45
  | 46 => p46
  | 47 => p47
  | 48 => p48
  | 49 => p49
  | 50 => p50
  | 51 => p51
  | 52 => p52
  | 53 => p53
  | 54 => p54
  | 55 => p55
  | 56 => p56
  | 57 => p57
  | 58 => p58
  | 59 => p59
  | 60 => p60
  | 61 => p61
  | 62 => p62
  | 63 => p63
  | 64 => p64
  | 65 => p65
  | 66 => p66
  | 67 => p67
  | 68 => p68
  | 69 => p69
  | 70 => p70
  | 71 => p71
  | _ => p72
private def line (i : Fin 73) : Equiv.Perm (Fin 13) := match i.val with
  | 0 => l0
  | 1 => l1
  | 2 => l2
  | 3 => l3
  | 4 => l4
  | 5 => l5
  | 6 => l6
  | 7 => l7
  | 8 => l8
  | 9 => l9
  | 10 => l10
  | 11 => l11
  | 12 => l12
  | 13 => l13
  | 14 => l14
  | 15 => l15
  | 16 => l16
  | 17 => l17
  | 18 => l18
  | 19 => l19
  | 20 => l20
  | 21 => l21
  | 22 => l22
  | 23 => l23
  | 24 => l24
  | 25 => l25
  | 26 => l26
  | 27 => l27
  | 28 => l28
  | 29 => l29
  | 30 => l30
  | 31 => l31
  | 32 => l32
  | 33 => l33
  | 34 => l34
  | 35 => l35
  | 36 => l36
  | 37 => l37
  | 38 => l38
  | 39 => l39
  | 40 => l40
  | 41 => l41
  | 42 => l42
  | 43 => l43
  | 44 => l44
  | 45 => l45
  | 46 => l46
  | 47 => l47
  | 48 => l48
  | 49 => l49
  | 50 => l50
  | 51 => l51
  | 52 => l52
  | 53 => l53
  | 54 => l54
  | 55 => l55
  | 56 => l56
  | 57 => l57
  | 58 => l58
  | 59 => l59
  | 60 => l60
  | 61 => l61
  | 62 => l62
  | 63 => l63
  | 64 => l64
  | 65 => l65
  | 66 => l66
  | 67 => l67
  | 68 => l68
  | 69 => l69
  | 70 => l70
  | 71 => l71
  | _ => l72
set_option maxHeartbeats 16000000 in
private theorem relation (i : Fin 73) : ∀ p l, R (point i p) (line i l) ↔ R p l := by
  fin_cases i
  · exact rel0
  · exact rel1
  · exact rel2
  · exact rel3
  · exact rel4
  · exact rel5
  · exact rel6
  · exact rel7
  · exact rel8
  · exact rel9
  · exact rel10
  · exact rel11
  · exact rel12
  · exact rel13
  · exact rel14
  · exact rel15
  · exact rel16
  · exact rel17
  · exact rel18
  · exact rel19
  · exact rel20
  · exact rel21
  · exact rel22
  · exact rel23
  · exact rel24
  · exact rel25
  · exact rel26
  · exact rel27
  · exact rel28
  · exact rel29
  · exact rel30
  · exact rel31
  · exact rel32
  · exact rel33
  · exact rel34
  · exact rel35
  · exact rel36
  · exact rel37
  · exact rel38
  · exact rel39
  · exact rel40
  · exact rel41
  · exact rel42
  · exact rel43
  · exact rel44
  · exact rel45
  · exact rel46
  · exact rel47
  · exact rel48
  · exact rel49
  · exact rel50
  · exact rel51
  · exact rel52
  · exact rel53
  · exact rel54
  · exact rel55
  · exact rel56
  · exact rel57
  · exact rel58
  · exact rel59
  · exact rel60
  · exact rel61
  · exact rel62
  · exact rel63
  · exact rel64
  · exact rel65
  · exact rel66
  · exact rel67
  · exact rel68
  · exact rel69
  · exact rel70
  · exact rel71
  · exact rel72
private def choices (i : Fin 26) : Nat := match i.val with
  | 0 => 1619541770991914265972430493994948897496819189973668139302912
  | 1 => 20972141533260108428760298244310897941695170548269193606725632
  | 2 => 17972230931388824787856162995426742277638498752533364149518347
  | 3 => 16163905745960489700562681063495755157868633397633653982625802
  | 4 => 40356203028972220815023504216065466635254005494489936003079430
  | 5 => 35660290632091689340660845498056542961565469225002622701997571
  | 6 => 33796115087873371949652069866981493497674565381035917616023560
  | 7 => 38623842957568918264953696304465734742131057355266534006525193
  | 8 => 1808104619863447438154175197983883730864906041785424868868353
  | 9 => 56343364802241309381350939112919727443089687553568955580023812
  | 10 => 43688802217835474237252402057360609731131797340594993130842119
  | 11 => 3226485949372406398270182276779075259124631780816319239356930
  | 12 => 8211136131565510436640212414680399218326211970163121594899461
  | 13 => 8116392169182134853644060545717157456908827457208916674019328
  | 14 => 17689535222654197541301403008881524773784700373384860499902464
  | 15 => 30764517928814057389037027190377104986714072670271313926094851
  | 16 => 32378103074088975512959075465534132168348943237198679004952582
  | 17 => 1663507636248239585420445853685174697931339436918667360796675
  | 18 => 1657352364875775452702290384329532997939737304965867573808641
  | 19 => 49897198921218093171905802673029253002503903731828469582990596
  | 20 => 51516347697616106898901850552180023127761595907616223481505799
  | 21 => 19340316899914146661150337425400103538667631622848223970011404
  | 22 => 8135761855871040264298943568338883695991287549171100341374469
  | 23 => 3226481830766987747674869896916204256769419259825633425100290
  | 24 => 45006870018464646344088272650739175484742820772758366612032770
  | _ => 1782746416148659649346806541758577360093567062668600568122625
private def choice (a b : Fin 26) : Fin 73 := Fin.ofNat 73 (((choices a) >>> (8*b.val)) % 256)
private def act (i : Fin 73) (v : Fin 26) : Nat := if v.val < 13 then (point i (Fin.ofNat 13 v.val)).val else 13 + (line i (Fin.ofNat 13 (v.val - 13))).val
set_option maxHeartbeats 16000000 in
private theorem within (a b : Fin 26) : pairCode (act (choice a b) a) (act (choice a b) b) ∈ representatives := by
  fin_cases a <;> revert b <;> decide +kernel
end PEqualNP.Outside.L_meta_18149
open PEqualNP.Outside.L_meta_18149
theorem PEqualNP.Outside.L_meta_18149 : (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 ≠ (0 : Fin (13 : ℕ)) ∧ (x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ))); ∀ (x2 x3 : Fin (26 : ℕ)),   ∃ (x4 : Equiv.Perm (Fin (13 : ℕ))) (x5 : Equiv.Perm (Fin (13 : ℕ))),     (∀ (x6 x7 : Fin (13 : ℕ)), x1 (x4 x6) (x5 x7) ↔ x1 x6 x7) ∧       have x6 : Fin (26 : ℕ) → ℕ := fun (x6 : Fin (26 : ℕ)) => if ↑x6 < (13 : ℕ) then ↑(x4 (Fin.ofNat (13 : ℕ) ↑x6)) else (13 : ℕ) + ↑(x5 (Fin.ofNat (13 : ℕ) (↑x6 - (13 : ℕ))));       (26 : ℕ) * Min.min (x6 x2) (x6 x3) + Max.max (x6 x2) (x6 x3) ∈ [(0 : ℕ), (1 : ℕ), (13 : ℕ), (14 : ℕ), (27 : ℕ), (28 : ℕ), (29 : ℕ), (39 : ℕ), (40 : ℕ), (41 : ℕ), (43 : ℕ), (351 : ℕ), (352 : ℕ), (355 : ℕ), (378 : ℕ), (379 : ℕ)]) := by
  dsimp only
  intro a b
  exact ⟨point (choice a b), line (choice a b), relation _, within a b⟩
