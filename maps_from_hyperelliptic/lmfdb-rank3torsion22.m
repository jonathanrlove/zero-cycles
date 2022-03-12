
// Elliptic curves downloaded from the LMFDB on 10 March 2022.
// Query "{'conductor': {'$gte': 1, '$lte': 100000000}, 'rank': 3, 'torsion_structure': [2, 2]}" returned 20 curves.

// Below are two lists, one called labels, and one called data (in matching order).
// Each entry in the data list has the form:
//    [[a1, a2, a3, a4, a6] Weierstrass coefficients]
// defining the elliptic curve y^2 + a1xy + a3y = x^3 + a2x^2 + a4x + a6.
//
// To create a list of curves, type "curves:= make_data();"

labels := [*\
"174915.b3",
"185562.d3",
"199728.b2",
"217328.c3",
"279616.i2",
"305040.s3",
"326975.c2",
"344850.c3",
"344955.b2",
"349398.c3",
"375150.b2",
"404430.a2",
"447168.f2",
"449072.l3",
"457025.a2",
"458345.a2",
"484160.v2",
"486291.b2",
"494361.e2",
"498675.d2"*];


data := [*\
[*1, -1, 1, -54788, 369542*],
[*1, -1, 0, -123993, 16705885*],
[*0, 0, 0, -13251, 474370*],
[*0, 0, 0, -317611, -49080870*],
[*0, 0, 0, -100396, 11684400*],
[*0, -1, 0, -49520, 4165632*],
[*1, -1, 1, -19230, -943228*],
[*1, 1, 0, -204250, 22562500*],
[*1, 1, 1, -60320, 5539520*],
[*1, -1, 0, -7848, 222700*],
[*1, 1, 0, -60750, 5062500*],
[*1, 1, 0, -19023, 866133*],
[*0, -1, 0, -28289, 1766529*],
[*0, 0, 0, -45451, 2296890*],
[*1, -1, 1, -12855, 115022*],
[*1, -1, 1, -243207, 43368806*],
[*0, 0, 0, -10108, 388368*],
[*1, 0, 0, -3809, 56784*],
[*1, -1, 1, -207941, 18540596*],
[*1, 1, 1, -4663, 23156*]*];


function make_data()
    return [EllipticCurve([a:a in ai]):ai in data];
end function;