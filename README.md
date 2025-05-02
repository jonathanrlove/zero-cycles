# Rational Equivalences of Zero-cycles

This repository contains Magma code used to compute rational equivalences of zero-cycles on algebraic varieties.

## Main code

The folder "maps_from_hyperelliptic" contains code associated to the paper "Hyperelliptic curves mapping to abelian varieties and applications to Beilinson's conjecture for zero-cycles" by Evangelia Gazaki and Jonathan Love. Main code is available in maps_from_hyperelliptic_2025/main.m.

### Instructions 
After loading main.m, run

test(pairlist, filename);

with pairlist set to be any list of pairs of elliptic curves over the rationals with fully rational 2-torsion, and filename is a string ending with .txt. For example:

test(shortrank1pairs, "data.txt");

The following options for pairlist come precomputed. Each reference to "the first n" is according to the ordering given by the LMFDB (ordered by conductor).

shortrank1pairs: Distinct C1, C2 in the first 10 elliptic curves over Q with rank 1 and (Z/2)^2 torsion. (45 pairs)
rank1nonisopairs: Distinct C1, C2 in the first 100 elliptic curves over Q with rank 1 and (Z/2)^2 torsion. (4950 pairs)
rank2nonisopairs: Distinct C1, C2 in the first 100 elliptic curves over Q with rank 2 and (Z/2)^2 torsion. (4950 pairs)
rank2diagonal: C1=C2 in the first 100 elliptic curves over Q with rank 2 and (Z/2)^2 torsion. (100 pairs)
rank3nonisopairs: Distinct C1, C2 in the first 20 elliptic curves over Q with rank 3 and (Z/2)^2 torsion. (190 pairs)
rank3diagonal: C1=C2 in the first 100 elliptic curves over Q with rank 3 and (Z/2)^2 torsion. (20 pairs)
rank1rank2: First 100 C1 of rank 1 and first 100 C2 of rank 2, both with (Z/2)^2 torsion. (10000 pairs)
rank1rank3: First 500 C1 of rank 1 and first 20 C2 of rank 3, both with (Z/2)^2 torsion. (10000 pairs)
rank2rank3: First 500 C1 of rank 2 and first 20 C2 of rank 3, both with (Z/2)^2 torsion. (10000 pairs)

### Output

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

After all pairs have been processed, each possible quintuple [a1,a2,a3,a4,a5] is printed  together with the number of pairs <C1,C2> attaining that quintuple.

Output files for each of the pairlists listed above are available in the "data" folder.


## Deprecated code

The folder "maps_from_hyperelliptic_2024" contains code associated to the paper "Torsion phenomena for zero-cycles on a product of curves over a number field" by Evangelia Gazaki and Jonathan Love: Research in Number Theory, Vol. 10, No. 35 (2024), 19 pgs. Main code is available in maps_from_hyperelliptic_2024/main.m. This code is superseded by the code in "maps_from_hyperelliptic", and is included for preservation purposes only.
