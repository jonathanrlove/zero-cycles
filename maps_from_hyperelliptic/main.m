load "pointfinding.m";
load "lmfdb-rank1torsion22.m";
r1t22curves := make_data();
load "lmfdb-rank2torsion22.m";
r2t22curves := make_data();
load "lmfdb-rank3torsion22.m";
r3t22curves := make_data();

// POSSIBLE PAIRLISTS
shortrank1pairs := &cat[[<r1t22curves[i], r1t22curves[j]> : j in [1..i-1]] : i in [1..10]];
rank1nonisopairs := &cat[[<r1t22curves[i], r1t22curves[j]> : j in [1..i-1]] : i in [1..100]];
rank2nonisopairs := &cat[[<r2t22curves[i], r2t22curves[j]> : j in [1..i-1]] : i in [1..100]]; 
rank2diagonal := [<r2t22curves[i], r2t22curves[i]> : i in [1..100]]; 
rank3nonisopairs := &cat[[<r3t22curves[i], r3t22curves[j]> : j in [1..i-1]] : i in [1..20]]; 
rank3diagonal := [<r3t22curves[i], r3t22curves[i]> : i in [1..20]]; 
rank1rank2 := &cat[[<r1t22curves[i], r2t22curves[j]> : j in [1..100]] : i in [1..100]]; 
rank1rank3 := &cat[[<r1t22curves[i], r3t22curves[j]> : j in [1..20]] : i in [1..500]]; 
rank2rank3 := &cat[[<r2t22curves[i], r3t22curves[j]> : j in [1..20]] : i in [1..500]];


procedure test(pairlist, filename : search_bound := 1000, constantrank := true, scholten := true, section_bound := 3)
	data := FindGoodPairs(pairlist : search_bound := search_bound, constantrank := constantrank, 
                                                   scholten := scholten, section_bound := section_bound, filename := filename);
    for q in Setseq(Seqset([i[2] : i in data])) do
        fprintf filename, "%o\n", <q, #[i : i in data | i[2] eq q]>;
    end for;
end procedure; 

/* ~~~~~~~~~~ INSTRUCTIONS ~~~~~~~~~~

After loading this file, run

test(pairlist, filename);

with pairlist set to be any list of pairs of elliptic curves over the rationals 
    with fully rational 2-torsion (a selection of some options for pairlist is 
    given in the section labelled "POSSIBLE PAIRLISTS" above), and filename
    is a string ending with .txt. For example:

test(shortrank1pairs, "data.txt");

OPTIONS:

search_bound is a height bound used to find points on certain hyperelliptic
    curves. Larger values may produce more successes, but may take longer.

constantrank should be set to true only if there are constants r1, r2 such that 
    rank(C1)=r1 and rank(C2)=r2 for all <C1,C2> in the list of curve pairs. 
    (This holds for all the lists of pairs in "POSSIBLE PAIRLISTS" above.)
    This saves the need to compute the rank for every curve separately, but yields 
    incorrect results if this assumption does not hold.

scholten is a Boolean value that determines whether relations arising from the
    six Scholten curves should be counted separately.

section_bound is a natural number that determines the number of curves to check
    from each fibration.

OUTPUT:

For each pair <C1, C2> in pairlist, the code will print a line 

i / n: [a1, a2, a3, a4, a5], [b1, b2, b3, b4]

where
- n is the total number of pairs in pairlist;
- i is the index of the pair <C1, C2>;
- a1+...+a5 is the number of independent relations found using hyperelliptic points on C1xC2, with
    - a1 counting relations arising from isogenies C1 -> C2;
    - a2 counting additional relations arising from Scholten curves (if scholten := true) 
    - a3 counting additional relations arising from fibration
    - a4 counting additional relations arising from modifying C1,C2 by isogenies first and then using Scholten curves
    - a5 counting additional relations arising from modifying C1,C2 by isogenies first and then using fibration
- b1+...+b4 is a running total of pairs for which rank(C1)*rank(C2) independent relations have been found:
    - b1 is the number of pairs for which isogenies were sufficient
    - b2 is the number of pairs for which Scholten curves (in addition) were sufficient;
    - b3 is the number of pairs for which fibration sections (in addition) were sufficient;
    - b4 is the number of pairs for which modifying by isogenies (in addition) was sufficient

After all pairs have been processed, each possible quintuple [a1,a2,a3,a4,a5] is printed 
    together with the number of pairs <C1,C2> attaining that quintuple.
*/
