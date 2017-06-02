Require Import PocklingtonRefl.


Open Local Scope positive_scope.

Lemma prime8725915592549 : prime 8725915592549.
Proof.
 apply (Pocklington_refl
         (Pock_certif 8725915592549 3 ((1493, 1)::(7, 1)::(2,2)::nil) 48418)
        ((Proof_certif 1493 prime1493) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.

Lemma prime9012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012346103: prime  9012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012346103.
apply (Pocklington_refl 

(Ell_certif
9012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012346103
13986778
((644347517269612384488416378438909400412225119649982232019901316388005468995251584871148108053,1)::nil)
6876185946935048040751473751022855964435207604826800480584663082562294790804494778730289090926002123
1287604209866173807929447190325501394628999764593900337993219613475043207272374348910703520783514130
6516846521636749360666474081337202009939996170296211414189696691120500897237814287101042700085704070
2998572055249888636204342756351637531949479794472452565652191467026302998735989403985748205493541627)
(
(Ell_certif
644347517269612384488416378438909400412225119649982232019901316388005468995251584871148108053
1497
((430425863239554031054386358342624849974766278957837438467999123730922152371746873570509403,1)::nil)
0
16099776
660
17424)
::
(Ell_certif
430425863239554031054386358342624849974766278957837438467999123730922152371746873570509403
1293660
((332719465114136659597101524622099199151837638944376508147884923943200404443549457431,1)::nil)
289975626511744866140091265861677492458656809520477876988840499632959965536640266414272794
297185428712726663958979141683738649218638291445691368309364200908337676579577162068480917
89556275673284803859411324942479193383687199311131908539246861667374500136391048012989360
395257953085467719995030050059258928938403275170021505221014856868895404968479220279853944)
::
(Ell_certif
332719465114136659597101524622099199151837638944376508147884923943200404443549457431
397
((838084294997825339035520213153902264866089168032090424648531533231662847138518037,1)::nil)
0
3584
8
64)
::
(SPock_certif 
838084294997825339035520213153902264866089168032090424648531533231662847138518037
2
((6026435233107726716681912540296130417249756723560347633161701708744375752427, 1)::nil))
::
(Ell_certif
6026435233107726716681912540296130417249756723560347633161701708744375752427
799153074
((7541027406606367776646896236923103442102559577407705771339962284857,1)::nil)
6026435233107726716681912540296130417249756723560347633161701708744375658347
9834496
0
3136)
::
(Ell_certif
7541027406606367776646896236923103442102559577407705771339962284857
99586
((75723770475833628990489589268803847236986538662715608142908101,1)::nil)
180
0
6
36)
::
(Ell_certif
75723770475833628990489589268803847236986538662715608142908101
2626
((28836165451574116142608373674330220327400147348020509034137,1)::nil)
254898
0
2499
127449)
::
(SPock_certif 
28836165451574116142608373674330220327400147348020509034137
2
((2497935330177937988791439160978016313877351641373917969, 1)::nil))
::
(Ell_certif
2497935330177937988791439160978016313877351641373917969
15130
((165098171194840580885091814858811065991152869408649,1)::nil)
2475075068971992147402876221557265554480685179579767469
0
2219116945646725665515247979790417236813386655566029846
267388253928239402581909711477223697365631754910812929)
::
(Ell_certif
165098171194840580885091814858811065991152869408649
74515521
((2215621242114653950887518255254509324788641,1)::nil)
0
192
4
16)
::
(Ell_certif
2215621242114653950887518255254509324788641
2575
((860435433830933573161222805912158029721,1)::nil)
0
233678802879279908882667940983886400695947
553905310528663487721879563813627331197494
2077144914482488078957048364301102492100740)
::
(Ell_certif
860435433830933573161222805912158029721
126423675
((6805967583452494741774641449143,1)::nil)
0
221184
48
576)
::
(SPock_certif 
6805967583452494741774641449143
2
((87255994659647368484290274989, 1)::nil))
::
(SPock_certif 
87255994659647368484290274989
2
((3511025054709776616943919, 1)::nil))
::
(SPock_certif 
3511025054709776616943919
2
((1709359812419560183517, 1)::nil))
::
(Ell_certif
1709359812419560183517
581
((2942099505078979841,1)::nil)
1709359812419559033029
475439166
435
7569)
::
(Ell_certif
2942099505078979841
337168
((8725915592549,1)::nil)
100
0
20
100)
:: (Proof_certif 8725915592549 prime8725915592549) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.
