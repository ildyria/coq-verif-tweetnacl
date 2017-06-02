Require Import PocklingtonRefl.


Open Local Scope positive_scope.

Lemma prime76580149463 : prime 76580149463.
Proof.
 apply (Pocklington_refl
         (Pock_certif 76580149463 5 ((2393, 1)::(2,1)::nil) 6053)
        ((Proof_certif 2393 prime2393) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012671: prime  12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012671.
apply (Pocklington_refl 

(Ell_certif
12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012671
206
((59930480103080426651084741694234687761656478484903511926160253588006814462928603452987461584902043367108261299742350588639,1)::nil)
725951084260195440770560463056578026202594606455322267710542981607787570079439667353771944419170720211139198308388754433170
9689640057172639871991863935657257906668981152847933415366856263996764137599448308029977883264632542173017885929817665606588
0
11140324108686787190294711548494522295725004466013705395992079378993006139835009153398876308220062617099334568765237224736530)
(
(Ell_certif
59930480103080426651084741694234687761656478484903511926160253588006814462928603452987461584902043367108261299742350588639
1570530735
((38159380626881158521921407475183659975719277142897500777761135955635318369552120284549450150698214687630782373829,1)::nil)
57414276893558116370794946409863393983523747075444145836350483510215460780376711638714853429166704865646141563359705118598
14756463187789876956714284082310450293022247885438835303181541696655878450033668305495350574201344136253075164995281901964
0
529129854827782151346794178999302851730578025660521040646208723696558342349287269064264336122584224407932733507460573388)
::
(Ell_certif
38159380626881158521921407475183659975719277142897500777761135955635318369552120284549450150698214687630782373829
100943406
((378027472412424428416071154515864661587892894587859466297657390325126739403099884215132629508596618721221,1)::nil)
28898946438760316111694924238282331747813038470055510346148955586092612492763802953100310487658864199873880184224
25120607095428707158122136214777174668153768639100335172610116317725461819656941516782158124833265485966433852312
0
21630315654193136488873113636377208277200692995540005050471653404185348847164755218241872945626120022257376577223)
::
(Ell_certif
378027472412424428416071154515864661587892894587859466297657390325126739403099884215132629508596618721221
3482
((108566189664682489493415035759869230783427023144129661688735876462020784644636423564131454188898656217,1)::nil)
141760302154659160656026682943449248095459835470447299861621521371922527276162456580674736065723732020459
0
189013736206212214208035577257932330793946447293929733148828695162563369701549942107566314754298309360612
283520604309318321312053365886898496190919670940894599723243042743845054552324913161349472131447464040918)
::
(Ell_certif
108566189664682489493415035759869230783427023144129661688735876462020784644636423564131454188898656217
95353909
((1138560451304439857766240456485839828374807614275469794354744545826977592881521191582268683087,1)::nil)
0
13310
11
121)
::
(Ell_certif
1138560451304439857766240456485839828374807614275469794354744545826977592881521191582268683087
3932
((289562678358199353450213747834648989922382404449714535143695998753873530067827552809557077,1)::nil)
532103789568660726250278817133300028523548832347301921709579707212171684941736175694315677056
984946349508046724326069774869722409492199973362323519311290415797810969451209837410244808729
123907945886544455569514780303211902053728110520154304496536532359869748720554640729890714435
50622519290809431655164733819579869900822093467377181627575460636043273213140820148957936800)
::
(Ell_certif
289562678358199353450213747834648989922382404449714535143695998753873530067827552809557077
354576
((816644889553154622563889681858470370026122476924948654723017361448891646954097111503,1)::nil)
268447358482123319696210536865476729380406371314203541963431353888290729811695506519413665
175988240056762662047455410873761726832349009791950501339651973485168503131593845433761667
0
137996452690759257815786716438975199457468549857633276804267164584571300015223574541701554)
::
(SPock_certif 
816644889553154622563889681858470370026122476924948654723017361448891646954097111503
2
((960300009117003669498909558326811393647413678789835272473403717105584446669117, 1)::nil))
::
(Ell_certif
960300009117003669498909558326811393647413678789835272473403717105584446669117
12285347872
((78166285490837395271676158713726278572273894626676958833971608271289,1)::nil)
960300009117003669498909558326811393647413678789835272473403717105584446525757
25690112
64
4096)
::
(Ell_certif
78166285490837395271676158713726278572273894626676958833971608271289
12496954
((6254827015514132105445547668153877122653475900923726253744581,1)::nil)
21731466879689543011811296746089403968203912962869835082497937216304
0
33299250790175646094495818486605227513492602529848931305489848495864
66598501580351292188991636973210455026985205059697862610979696991729)
::
(Ell_certif
6254827015514132105445547668153877122653475900923726253744581
608293998754
((10282572289593875951890890102834829295224458490241,1)::nil)
1116018
0
6723
558009)
::
(Ell_certif
10282572289593875951890890102834829295224458490241
685396
((15002381527750199814254658438718259406813337,1)::nil)
10368
0
288
5184)
::
(Ell_certif
15002381527750199814254658438718259406813337
90784
((165253585739229377580437110055651786309,1)::nil)
544644
0
6642
544644)
::
(Ell_certif
165253585739229377580437110055651786309
2055
((80415370189406023152041387832831331,1)::nil)
165253585739229377580437110054894202405
8234810772496
0
2869636)
::
(Ell_certif
80415370189406023152041387832831331
9992425
((8047633101014620946271243901,1)::nil)
0
66908100977904230200721935970285327
40207685094703011576020693916415681
25129803184189382235012933697759851)
::
(SPock_certif 
8047633101014620946271243901
2
((457642973190889, 1)::nil))
::
(SPock_certif 
457642973190889
2
((76580149463, 1)::nil))
:: (Proof_certif 76580149463 prime76580149463) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
