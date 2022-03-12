load "maps_from_hyperelliptic/methods.m";
load "maps_from_hyperelliptic/lmfdb-rank1torsion22.m";
rank1curves := make_data();
load "maps_from_hyperelliptic/lmfdb-rank2torsion22.m";
rank2curves := make_data();
load "maps_from_hyperelliptic/lmfdb-rank3torsion22.m";
rank3curves := make_data();

shortrank1pairs := &cat[[<rank1curves[i], rank1curves[j]> : j in [1..i]] : i in [1..10]];
rank1pairs := &cat[[<rank1curves[i], rank1curves[j]> : j in [1..i]] : i in [1..100]];
rank1rank2 := &cat[[<rank1curves[i], rank2curves[j]> : j in [1..100]] : i in [1..100]]; 
rank1rank3 := &cat[[<rank1curves[i], rank3curves[j]> : j in [1..20]] : i in [1..500]]; 
rank2distinctpairs := &cat[[<rank2curves[i], rank2curves[j]> : j in [1..i-1]] : i in [1..100]]; 
rank2diagonal := [<rank2curves[i], rank2curves[i]> : i in [1..100]]; 
rank2rank3 := &cat[[<rank2curves[i], rank3curves[j]> : j in [1..20]] : i in [1..500]]; 
shortrank2rank3 := &cat[[<rank2curves[i], rank3curves[j]> : j in [1..10]] : i in [1..10]]; 
rank3pairs := &cat[[<rank3curves[i], rank3curves[j]> : j in [1..i]] : i in [1..20]]; 

/* ~~~~~~~~~~ INSTRUCTIONS ~~~~~~~~~~

Set pairlist to be any list of pairs of elliptic curves over the rationals 
    with fully rational 2-torsion. A selection of some options for pairlist 
    is given above.

search_bound is a height bound used to find points on certain genus 2 hyperelliptic
    curves. Larger values may produce more successes, but may take longer.

constantrank should be set to true only if there are constants r1, r2 such that 
    rank(C1)=r1 and rank(C2)=r2 for all <C1,C2> in the list of curve pairs. 
    (This holds for all the lists of pairs given above.)
    This saves the need to compute the rank for every curve separately, but yields 
    incorrect results if the assumption does not hold.

The code will print "n / [length of list]" when processing the nth pair, where n
    is a multiple of progress_markers.

max_curves must be an integer from 1 to 6, inclusive. This determines the maximum number
    of covers H->C1 and H->C2 to use. Lower values will run faster but produce 
    fewer successes.

genlist determines how comprehensive the returned information is; see below.
*/

pairlist := shortrank1pairs;
successes, alldata := FindGoodPairs(pairlist : search_bound := 1000, constantrank := true, 
                                               progress_markers := 100, max_curves := 6, genlist := false);
print #successes, " out of ", #pairlist;


/* ~~~~~~~~~~ OUTPUT INTERPRETATION ~~~~~~~~~~ 

successes is a list of indices. If i in successes, and <C1,C2> = pairlist[i], then
    F^2(C1xC2)_comp is torsion. If i is not in successes, the test is inconclusive.

alldata is a list of the same length as pairlist.

if genlist:=true, then for each i, alldata[i] is a list of tuples <P,f1,f2>, where
    P is on a curve C, and f1:C->C1 and f2:C->C2 are maps (here <C1,C2>=pairlist[i]). 
    As the tuple varies over alldata[i], f1(P) \otimes f2(P) will produce an
    independent set of elements of C1(\Q)\otimes C2(\Q), all of which map to torsion
    in F^2(C1xC2). If the length of the list of tuples equals rank(C1)*rank(C2)
    then F^2(C1xC2)_comp is finite.

if genlist:=false, alldata[i] as above is replaced with its length.

Sample outputs:
if pairlist := shortrank1pairs, "29 out of 55"
if pairlist := rank1pairs, "1169 out of 5050"
if pairlist := rank1rank2, "545 out of 10000"
if pairlist := rank1rank3, "56 out of 10000"
if pairlist := rank2distinctpairs, "69 out of 4950"
if pairlist := rank2diagonal, "4 out of 100"
if pairlist := rank2rank3, "30 out of 10000"
if pairlist := rank3pairs, "0 out of 210"
*/