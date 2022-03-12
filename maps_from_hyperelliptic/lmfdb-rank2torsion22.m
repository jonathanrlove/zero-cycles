
// Elliptic curves downloaded from the LMFDB on 10 March 2022.
// Query "{'conductor': {'$gte': 1, '$lte': 50000}, 'rank': 2, 'torsion_structure': [2, 2]}" returned 383 curves.

// Below are two lists, one called labels, and one called data (in matching order).
// Each entry in the data list has the form:
//    [[a1, a2, a3, a4, a6] Weierstrass coefficients]
// defining the elliptic curve y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6.
//
// To create a list of curves, type "curves:= make_data();"

labels := [*\
"2175.b2",
"3264.c2",
"3315.a2",
"3663.a3",
"4450.d2",
"5115.b3",
"5304.b3",
"5382.b3",
"6150.a2",
"6336.o3",
"6510.a3",
"6600.a3",
"6630.a2",
"6630.e2",
"6720.a2",
"6867.a3",
"7137.d2",
"7832.b2",
"8379.e2",
"8502.b2",
"8526.a3",
"9009.b3",
"9010.b2",
"9078.e2",
"9408.h3",
"9408.h4",
"9425.a2",
"9576.c2",
"9744.c2",
"10304.s2",
"10560.b2",
"10878.o3",
"10920.a3",
"11310.c2",
"11385.c3",
"11640.d2",
"11895.b3",
"12002.b2",
"12168.e2",
"12207.b2",
"12480.y2",
"12656.d2",
"12705.b2",
"12870.b3",
"12936.d3",
"13104.k2",
"13120.n2",
"13120.t2",
"13200.b3",
"13650.b2",
"13680.a3",
"14016.bg2",
"14144.p2",
"14352.u3",
"14400.f2",
"14400.k3",
"14430.m2",
"14685.c2",
"14706.o2",
"14763.f3",
"14784.g3",
"14880.c3",
"15080.j2",
"15088.g3",
"15480.f2",
"15504.a2",
"15582.a2",
"15600.b3",
"15675.e2",
"15675.f3",
"15680.bv3",
"15680.bw2",
"15792.c3",
"15950.d3",
"16263.a3",
"16317.b2",
"16317.j3",
"16320.k2",
"16400.l2",
"16422.p2",
"16560.bc3",
"16728.c2",
"17094.c2",
"17794.i2",
"17958.i2",
"17985.e3",
"18018.d3",
"18032.l2",
"18240.bn2",
"18369.b2",
"18480.f3",
"18496.j3",
"18648.g2",
"18960.h3",
"19032.l2",
"19040.b3",
"19065.c3",
"19152.h2",
"19176.a2",
"19206.d2",
"19215.g2",
"19350.bq2",
"19488.a3",
"19525.g2",
"19536.r2",
"19680.l3",
"19734.i2",
"20160.e3",
"20160.f2",
"20235.c2",
"20400.ca2",
"20672.o2",
"20832.u3",
"21105.e2",
"21177.a3",
"21186.o2",
"21216.d3",
"21315.c2",
"21360.g2",
"21483.e2",
"21525.i2",
"21567.c3",
"21696.f2",
"21801.d2",
"21840.t2",
"21945.l3",
"22035.e2",
"22134.ba3",
"22176.e3",
"22515.e3",
"22737.a2",
"22755.b2",
"22800.s3",
"22848.e3",
"22848.bq3",
"22968.f2",
"22984.e2",
"23055.c2",
"23142.k3",
"23310.i2",
"23310.i4",
"23439.c2",
"23790.b3",
"23850.bs2",
"23925.t3",
"23925.t4",
"24024.b2",
"24200.n2",
"24310.h2",
"24336.o3",
"24336.o4",
"24360.f3",
"24695.b2",
"25200.l3",
"25330.e2",
"25520.h3",
"25575.b2",
"25857.e2",
"25872.h2",
"25925.a2",
"25935.h2",
"26040.l3",
"26208.i3",
"26520.r3",
"26600.p2",
"26775.p3",
"26775.p4",
"26928.l2",
"26928.o2",
"27075.f2",
"27075.f5",
"27075.f6",
"27342.g3",
"27360.a3",
"27360.f3",
"27456.bm2",
"27720.m2",
"27744.b3",
"27792.g2",
"27840.ch2",
"27846.h2",
"28314.h3",
"28371.e2",
"28392.d3",
"28560.b3",
"28560.e3",
"28665.o2",
"28830.a3",
"28830.a6",
"28975.c3",
"29070.k2",
"29274.z2",
"29280.c3",
"29450.h2",
"29736.b2",
"29784.j2",
"29946.n3",
"30222.a2",
"30222.b3",
"30360.m2",
"30450.b2",
"30498.m3",
"30912.f2",
"30912.k3",
"30912.bk3",
"31122.e2",
"31200.i3",
"31680.d2",
"31775.i3",
"32080.g2",
"32430.z2",
"32490.n3",
"32490.n6",
"32606.e3",
"32982.l3",
"33066.d3",
"33120.i3",
"33120.y3",
"33201.m2",
"33222.l3",
"33495.g2",
"33558.r2",
"33600.f2",
"33600.g2",
"33600.bd2",
"33702.k2",
"33840.bj2",
"33915.d3",
"34320.d2",
"34320.bd2",
"34335.e3",
"34485.e3",
"34650.a3",
"34710.a2",
"34765.b2",
"34800.a2",
"34800.by2",
"34848.i3",
"34983.f2",
"35139.a3",
"35217.b2",
"35280.p2",
"35280.di2",
"35280.di4",
"35400.d3",
"35520.bd2",
"35631.c3",
"35670.d2",
"35880.f2",
"35904.h2",
"35904.bx2",
"35970.m3",
"36080.i2",
"36192.c3",
"36225.k2",
"36465.e2",
"36630.a2",
"37107.d3",
"37296.l3",
"37296.m2",
"37440.c3",
"37440.da3",
"37440.db3",
"37758.b2",
"37995.g2",
"38064.s2",
"38130.e2",
"38130.u3",
"38190.k3",
"38216.b2",
"38304.r3",
"38318.r2",
"38430.v2",
"38454.c2",
"38640.v3",
"39160.l3",
"39270.m2",
"39270.y2",
"39330.br3",
"39360.b2",
"39360.i2",
"39360.x2",
"39480.h2",
"39585.g3",
"39585.h2",
"40075.e2",
"40128.f3",
"40128.j3",
"40222.g2",
"40278.k2",
"40600.j2",
"40656.cd3",
"40656.cd4",
"40880.n3",
"40902.k2",
"41118.k3",
"41118.l3",
"41280.cs2",
"41440.e3",
"41496.u2",
"41525.d3",
"41610.l3",
"41664.j2",
"41664.l2",
"41718.e2",
"41832.f2",
"42160.q3",
"42294.h3",
"42504.e3",
"42630.b2",
"42735.f3",
"42840.y2",
"42925.a2",
"43050.a2",
"43056.g3",
"43080.i3",
"43120.bk3",
"43230.h2",
"43290.a2",
"43290.c2",
"43290.bp2",
"43560.c2",
"43560.o2",
"43560.o4",
"43680.o3",
"43806.k2",
"43824.x2",
"43890.a2",
"43890.l2",
"43890.r3",
"44109.s2",
"44352.bc2",
"44352.bc3",
"44352.bg2",
"44370.p2",
"44400.bb3",
"44730.o2",
"44880.h2",
"44946.q2",
"45045.e3",
"45066.g2",
"45201.c3",
"45390.j2",
"45458.c3",
"45510.b2",
"45567.b3",
"45570.h2",
"45570.bo2",
"45570.bo5",
"45600.z3",
"45747.b2",
"45760.z2",
"45864.n2",
"46002.r2",
"46200.a3",
"46246.c2",
"46272.d2",
"46410.a2",
"46725.c2",
"46725.o2",
"46761.c2",
"46965.a2",
"47040.r3",
"47175.c2",
"47367.a3",
"47515.a2",
"47565.l3",
"47610.bm2",
"47691.a3",
"47880.c2",
"47880.p2",
"48048.bt2",
"48675.f2",
"48675.g2",
"48678.d2",
"48950.j2",
"48960.dl3",
"49200.w2",
"49335.h2",
"49470.e2",
"49504.h3",
"49590.bb2",
"49608.c2"*];


data := [*\
[*1, 1, 1, -813, 3906*],
[*0, -1, 0, -289, 289*],
[*1, 1, 1, -71, -196*],
[*1, -1, 1, -356, 2126*],
[*1, -1, 0, -3292, -48384*],
[*1, 1, 1, -4180, 77252*],
[*0, -1, 0, -884, 10404*],
[*1, -1, 0, -6183, 178605*],
[*1, 1, 0, -725, -6375*],
[*0, 0, 0, -1596, 23920*],
[*1, 1, 0, -273, -1323*],
[*0, -1, 0, -1108, 14212*],
[*1, 1, 0, -228, 828*],
[*1, 1, 0, -767, 1521*],
[*0, -1, 0, -281, 1881*],
[*1, -1, 1, -2291, 42666*],
[*1, -1, 1, -581, 4556*],
[*0, 0, 0, -2611, -51330*],
[*1, -1, 1, -2876, 54366*],
[*1, 0, 1, -222, -1220*],
[*1, 1, 0, -956, 10620*],
[*1, -1, 1, -2111, -34914*],
[*1, -1, 0, -115, 225*],
[*1, 1, 1, -10284, -188979*],
[*0, -1, 0, -4769, 122529*],
[*0, -1, 0, -849, -6831*],
[*1, -1, 1, -330, -328*],
[*0, 0, 0, -831, -4030*],
[*0, -1, 0, -224, -816*],
[*0, 0, 0, -556, 3120*],
[*0, -1, 0, -121, 121*],
[*1, 0, 1, -3162, 17980*],
[*0, -1, 0, -196, 196*],
[*1, 1, 0, -1852, 25216*],
[*1, -1, 1, -1058, 12552*],
[*0, 1, 0, -2536, -36736*],
[*1, 1, 1, -19825, 1066142*],
[*1, -1, 1, -2211, 35411*],
[*0, 0, 0, -67431, -4108390*],
[*1, 0, 0, -1534, 3059*],
[*0, -1, 0, -625, 625*],
[*0, 0, 0, -3211, 15930*],
[*1, 1, 1, -30071, -793132*],
[*1, -1, 0, -3915, 72625*],
[*0, -1, 0, -117224, 15131964*],
[*0, 0, 0, -1011, 4930*],
[*0, 0, 0, -1708, 10032*],
[*0, 0, 0, -2188, -39312*],
[*0, -1, 0, -2508, -7488*],
[*1, 1, 0, -675, 5625*],
[*0, 0, 0, -27363, 1741538*],
[*0, 1, 0, -7009, 223391*],
[*0, 0, 0, -316, 1680*],
[*0, 1, 0, -2984, 49476*],
[*0, 0, 0, -2100, 20000*],
[*0, 0, 0, -14700, 286000*],
[*1, 0, 1, -1979, -32398*],
[*1, 1, 1, -11075, 357392*],
[*1, -1, 1, -4451, -83869*],
[*1, 0, 0, -31464, -1542321*],
[*0, -1, 0, -329, 969*],
[*0, -1, 0, -310, 2200*],
[*0, 0, 0, -236887, 44373834*],
[*0, 0, 0, -1051, 6090*],
[*0, 0, 0, -5187, -141266*],
[*0, -1, 0, -664, -2576*],
[*1, 1, 0, -2181, 12825*],
[*0, -1, 0, -1808, 26112*],
[*1, 1, 1, -4313, 91406*],
[*1, 1, 1, -15688, 747656*],
[*0, 0, 0, -55468, 4066608*],
[*0, 0, 0, -2548, -32928*],
[*0, -1, 0, -2304, 2304*],
[*1, -1, 0, -53167, 4731741*],
[*1, -1, 1, -916286, 337652916*],
[*1, -1, 1, -9491, 84746*],
[*1, -1, 0, -114228, 14884155*],
[*0, -1, 0, -3401, 77385*],
[*0, 0, 0, -13675, 614250*],
[*1, 1, 1, -3129, 65991*],
[*0, 0, 0, -5187, -10366*],
[*0, -1, 0, -424, -836*],
[*1, 1, 0, -33281, 2216865*],
[*1, -1, 1, -1551, 22871*],
[*1, 1, 1, -582774, -171344589*],
[*1, 0, 0, -29975, 1995000*],
[*1, -1, 0, -5598, -117180*],
[*0, 0, 0, -6811, 133770*],
[*0, 1, 0, -8241, 281295*],
[*1, -1, 1, -4271, 105806*],
[*0, -1, 0, -456, 3456*],
[*0, 0, 0, -1156, 0*],
[*0, 0, 0, -3351, 56810*],
[*0, -1, 0, -6400, 6400*],
[*0, 1, 0, -7324, -113344*],
[*0, 0, 0, -73, 72*],
[*1, 1, 1, -4929930, 4196340150*],
[*0, 0, 0, -8571, 282490*],
[*0, -1, 0, -804, -8316*],
[*1, -1, 0, -1368, 10480*],
[*1, -1, 1, -32162, -2180176*],
[*1, -1, 1, -77405, 8306597*],
[*0, -1, 0, -974, -10296*],
[*1, -1, 0, -2167, -30384*],
[*0, 1, 0, -29304, 1920996*],
[*0, -1, 0, -710, 6600*],
[*1, 0, 1, -1797, 29020*],
[*0, 0, 0, -948, 7072*],
[*0, 0, 0, -468, 2592*],
[*1, 1, 1, -2480, 39800*],
[*0, 1, 0, -1808, -3612*],
[*0, 0, 0, -436, -3360*],
[*0, 1, 0, -614, 2376*],
[*1, -1, 1, -3047, -9106*],
[*1, -1, 1, -7196, 221766*],
[*1, -1, 1, -19571, -672429*],
[*0, -1, 0, -174, 504*],
[*1, 1, 1, -7155, -230448*],
[*0, -1, 0, -2400, 44352*],
[*1, -1, 1, -1391, -17314*],
[*1, 0, 0, -20313, 1087992*],
[*1, 0, 0, -31289, 2096304*],
[*0, -1, 0, -13569, 412929*],
[*1, 0, 0, -4989, -58176*],
[*0, -1, 0, -4480, 104272*],
[*1, 1, 1, -284645, -52981630*],
[*1, 1, 1, -201, 198*],
[*1, 1, 1, -48614, 4103651*],
[*0, 0, 0, -5421, 26980*],
[*1, 0, 0, -1555, -17248*],
[*1, 1, 1, -479, -4084*],
[*1, 1, 1, -590, -4678*],
[*0, -1, 0, -4008, -79488*],
[*0, -1, 0, -609, 3969*],
[*0, 1, 0, -1289, 14391*],
[*0, 0, 0, -169491, -26663650*],
[*0, 0, 0, -13351, 461370*],
[*1, 1, 1, -8510, -140110*],
[*1, 0, 1, -50292, 4331710*],
[*1, -1, 0, -345105, 78029325*],
[*1, -1, 0, -27585, 490941*],
[*1, 0, 0, -6004, -121561*],
[*1, 1, 0, -1117, 10621*],
[*1, -1, 1, -318380, 68947247*],
[*1, 1, 0, -323000, -65203125*],
[*1, 1, 0, -69875, 5925000*],
[*0, -1, 0, -404, 2244*],
[*0, 0, 0, -21175, 998250*],
[*1, -1, 0, -47695, 3924525*],
[*0, 0, 0, -37011, -2614430*],
[*0, 0, 0, -6591, 153790*],
[*0, -1, 0, -39796, 3066820*],
[*1, -1, 1, -6492, 137534*],
[*0, 0, 0, -4275, 101250*],
[*1, -1, 0, -349, 693*],
[*0, 0, 0, -427, 2346*],
[*1, 1, 1, -11688, 472656*],
[*1, -1, 1, -8651, 308026*],
[*0, -1, 0, -1584, 17424*],
[*1, -1, 0, -46042, 3776991*],
[*1, 0, 0, -956, -1905*],
[*0, -1, 0, -26040, 1626012*],
[*0, 0, 0, -381, 380*],
[*0, 1, 0, -21156, 1159200*],
[*0, 0, 0, -99175, -4371750*],
[*1, -1, 1, -336380, 66785622*],
[*1, -1, 1, -83255, -8139378*],
[*0, 0, 0, -58611, 4511410*],
[*0, 0, 0, -2451, 2450*],
[*1, 1, 1, -1218563, 516972656*],
[*1, 1, 1, -90438, 4803906*],
[*1, 1, 1, -45313, -3679594*],
[*1, -1, 0, -9123, 336545*],
[*0, 0, 0, -1533, 17732*],
[*0, 0, 0, -813, -812*],
[*0, 1, 0, -17649, 857871*],
[*0, 0, 0, -6543, 195858*],
[*0, -1, 0, -29574, 1945944*],
[*0, 0, 0, -111171, -14265790*],
[*0, 1, 0, -961, -10465*],
[*1, -1, 0, -13158, 576180*],
[*1, -1, 0, -342513, -74987555*],
[*1, 0, 0, -28764, 511839*],
[*0, -1, 0, -42644, 3388644*],
[*0, -1, 0, -8176, 285376*],
[*0, -1, 0, -1776, -23040*],
[*1, -1, 1, -65057, -5600136*],
[*1, 1, 0, -320513, 69576117*],
[*1, 1, 0, -17798, -835392*],
[*1, -1, 1, -2730, -41728*],
[*1, -1, 0, -71304, 7327628*],
[*1, 1, 1, -7769, 112871*],
[*0, -1, 0, -5086, 141040*],
[*1, -1, 0, -3667, 48741*],
[*0, 0, 0, -172191, -27422750*],
[*0, 1, 0, -22584, -975744*],
[*1, 1, 1, -664, -6199*],
[*1, -1, 0, -68238, -5816300*],
[*1, -1, 0, -1413, 16065*],
[*0, -1, 0, -1220, -7068*],
[*1, 1, 0, -8500, -162500*],
[*1, 1, 1, -921719, 340214861*],
[*0, -1, 0, -649, 6409*],
[*0, -1, 0, -5409, -86751*],
[*0, 1, 0, -5409, 86751*],
[*1, -1, 0, -17613, 615505*],
[*0, -1, 0, -1158, 12312*],
[*0, 0, 0, -10668, 323408*],
[*1, -1, 0, -214042, -37761009*],
[*0, 0, 0, -53467, 4758474*],
[*1, 0, 0, -28211, 1819041*],
[*1, -1, 0, -1083609, -433072787*],
[*1, -1, 0, -60174, 5162080*],
[*1, -1, 1, -1026, -1279*],
[*1, 0, 0, -9654, -219996*],
[*1, -1, 0, -11763, -130815*],
[*0, 0, 0, -6213, 188188*],
[*0, 0, 0, -1317, 14924*],
[*1, -1, 0, -14238, -648945*],
[*1, 1, 1, -1063154, 421421951*],
[*1, 1, 1, -1595, -4768*],
[*1, 1, 1, -22894, 1314731*],
[*0, -1, 0, -19633, -762863*],
[*0, -1, 0, -1433, 19737*],
[*0, -1, 0, -1233, -3663*],
[*1, 1, 1, -309, -1449*],
[*0, 0, 0, -5187, 83266*],
[*1, 1, 1, -1665, 22830*],
[*0, -1, 0, -1056, 0*],
[*0, 1, 0, -6456, 195300*],
[*1, -1, 1, -101453, -11497044*],
[*1, 1, 1, -46285, 3560690*],
[*1, -1, 0, -3717, 45441*],
[*1, 1, 0, -27768, -1792512*],
[*1, -1, 1, -3627, 84554*],
[*0, -1, 0, -6008, 160512*],
[*0, 1, 0, -174008, 27875988*],
[*0, 0, 0, -2541, -26620*],
[*1, -1, 1, -36536, 828546*],
[*1, 1, 1, -153114, 22539486*],
[*1, -1, 1, -1166, -1164*],
[*0, 0, 0, -165963, -25325062*],
[*0, 0, 0, -88347, 10050586*],
[*0, 0, 0, -8967, -62426*],
[*0, -1, 0, -29508, 1959012*],
[*0, -1, 0, -1425, 12177*],
[*1, -1, 1, -3146, -48904*],
[*1, 1, 0, -27952, 1768624*],
[*0, -1, 0, -1476, 13860*],
[*0, -1, 0, -1089, 1089*],
[*0, 1, 0, -114529, 14842751*],
[*1, 0, 1, -40178, 3032048*],
[*0, 0, 0, -3787, 47034*],
[*0, -1, 0, -254, 1584*],
[*1, -1, 1, -1955, -20078*],
[*1, 1, 1, -25075, 1516760*],
[*1, -1, 0, -4965, -66619*],
[*1, -1, 1, -2021, 31556*],
[*0, 0, 0, -65271, 6417430*],
[*0, 0, 0, -5871, 131150*],
[*0, 0, 0, -3108, -45632*],
[*0, 0, 0, -18732, 984656*],
[*0, 0, 0, -7812, 264384*],
[*1, 1, 0, -16781, 829725*],
[*1, 1, 0, -39477, -2916576*],
[*0, 1, 0, -1084, 12236*],
[*1, 1, 0, -418, -2912*],
[*1, 1, 1, -33895, 2387357*],
[*1, 0, 1, -7639, 256262*],
[*0, 0, 0, -27091, 1711710*],
[*0, 0, 0, -372441, 86715200*],
[*1, -1, 1, -276786, 55916081*],
[*1, -1, 0, -16569, 99225*],
[*1, 1, 0, -901, -10115*],
[*0, -1, 0, -432976, -109336640*],
[*0, 0, 0, -3007, -60606*],
[*1, 1, 0, -1337, 15729*],
[*1, 0, 1, -5594, 49592*],
[*1, -1, 1, -43007, 3161639*],
[*0, -1, 0, -6561, 6561*],
[*0, -1, 0, -2481, 47025*],
[*0, -1, 0, -20505, 1136025*],
[*0, -1, 0, -30756, -1215900*],
[*1, 1, 1, -4400, 110360*],
[*1, 0, 0, -22631, -691680*],
[*1, -1, 1, -29355, 1913522*],
[*0, -1, 0, -569, 5049*],
[*0, -1, 0, -1529, 15609*],
[*1, -1, 0, -6538, -100320*],
[*1, 1, 1, -17984, 906401*],
[*0, 0, 0, -6775, -213750*],
[*0, 1, 0, -201384, 12243636*],
[*0, 1, 0, -162664, 25176116*],
[*0, 0, 0, -1963, 32538*],
[*1, 1, 1, -3214, -71029*],
[*1, 1, 1, -9274, 322871*],
[*1, 1, 1, -5916229, 5535812171*],
[*0, 1, 0, -67265, -5916225*],
[*0, 0, 0, -433, -3432*],
[*0, 1, 0, -38344, -2700544*],
[*1, -1, 0, -14167, 602616*],
[*1, 0, 1, -5854, -58948*],
[*0, -1, 0, -3969, 3969*],
[*0, -1, 0, -1169, 15249*],
[*1, 1, 1, -2669, -23389*],
[*0, 0, 0, -16131, -443410*],
[*0, 0, 0, -31147, 2042586*],
[*1, 0, 1, -857, 7400*],
[*0, -1, 0, -484, 484*],
[*1, 1, 0, -31728, 1965132*],
[*1, 1, 1, -4486, 54914*],
[*0, 0, 0, -21423, 1206322*],
[*1, -1, 1, -4605, 109772*],
[*1, 1, 0, -4375, -42875*],
[*0, 0, 0, -129171, 17867410*],
[*0, 1, 0, -43080, 3427200*],
[*0, 0, 0, -3283, 43218*],
[*1, 1, 0, -5594462, -5028432396*],
[*1, -1, 0, -43290, 3477600*],
[*1, -1, 0, -32580, 260176*],
[*1, -1, 1, -20012, 1088799*],
[*0, 0, 0, -719103, -234311902*],
[*0, 0, 0, -218163, -39000962*],
[*0, 0, 0, -22143, 242242*],
[*0, -1, 0, -190, -800*],
[*1, 1, 0, -19919, 991845*],
[*0, 1, 0, -2824, 50996*],
[*1, 1, 0, -478, 3232*],
[*1, 1, 0, -13442, 503844*],
[*1, 1, 0, -20807, 1085889*],
[*1, -1, 0, -20058, 199655*],
[*0, 0, 0, -163596, -24958960*],
[*0, 0, 0, -22476, 724880*],
[*0, 0, 0, -1116, -6480*],
[*1, -1, 0, -3534, 77588*],
[*0, -1, 0, -25808, 434112*],
[*1, -1, 0, -61314, -4855852*],
[*0, -1, 0, -10216, -362384*],
[*1, -1, 1, -7286, -50619*],
[*1, -1, 1, -20498, 1130456*],
[*1, 1, 0, -1246, -16160*],
[*1, 0, 0, -16094, -582981*],
[*1, 1, 1, -69291, 5170713*],
[*1, -1, 1, -18531, -833629*],
[*1, 1, 0, -1763, 10317*],
[*1, -1, 1, -2939, -15262*],
[*1, 1, 0, -12912, -419796*],
[*1, 1, 1, -941781, 351387819*],
[*1, 1, 1, -59781, 5291019*],
[*0, 1, 0, -2858, 57288*],
[*1, -1, 1, -15386, -708744*],
[*0, 0, 0, -30748, 1502928*],
[*0, 0, 0, -19551, 641410*],
[*1, 0, 0, -2506799, 1349701689*],
[*0, -1, 0, -25508, -1352988*],
[*1, -1, 1, -30831, -2075929*],
[*0, -1, 0, -78089, -8371191*],
[*1, 1, 0, -10493, 364413*],
[*1, 1, 1, -3824688, 438301656*],
[*1, 1, 0, -5000, 121875*],
[*1, 0, 0, -38564, -2840481*],
[*1, 1, 1, -5220, -147180*],
[*0, -1, 0, -46321, 3688945*],
[*1, 1, 1, -2838, -14094*],
[*1, -1, 1, -15926, 755196*],
[*1, -1, 1, -442308, 104873606*],
[*1, -1, 0, -1087695, 436840096*],
[*1, -1, 1, -4396883, 329348531*],
[*1, -1, 1, -111416, 14282826*],
[*0, 0, 0, -89823, 10342978*],
[*0, 0, 0, -13683, -455618*],
[*0, 1, 0, -11144, 441396*],
[*1, 1, 1, -1033313, -390508594*],
[*1, 1, 1, -1538, 19406*],
[*1, 0, 1, -2887, 19850*],
[*1, -1, 0, -6142, 134016*],
[*0, 0, 0, -11172, -324736*],
[*0, -1, 0, -12508, 512512*],
[*1, 0, 0, -5601, 120456*],
[*1, 1, 1, -36916, -2696587*],
[*0, 0, 0, -33361, -2156880*],
[*1, -1, 1, -13838, 605981*],
[*0, 0, 0, -8271, 289170*]*];


function make_data()
    return [EllipticCurve([a:a in ai]):ai in data];
end function;