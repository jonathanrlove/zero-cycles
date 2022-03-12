TranslatedRoots := function(curve : perm:=1)
    /* Given an elliptic curve, return two values a and b such that
    curve is isomorphic to y^2=x(x-a)(x-b). Return an error if no rational a,b exist.

    Up to scaling, there are 6 possiblities for [a,b], determined by permuting the roots.
    Parameter perm is an integer in [1..6] that designates the choice of permutation. */

    E := WeierstrassModel(curve);
    if #DivisionPoints(E!0, 2) ne 4 then
        error curve, " does not have fully rational 2-torsion";
    end if;

    x := [P[1] : P in DivisionPoints(E!0, 2) | P ne E!0]; 

    pi := [[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]];
    a := x[pi[perm][1]] - x[pi[perm][3]];
    b := x[pi[perm][2]] - x[pi[perm][3]];
    return a,b;
end function;

HyperWithMaps := function(C1, C2 : option:=1)
    /* Given elliptic curves C1 and C2, return a genus 2 curve H and maps f1:H->C1 and f2:H->C2,
    as in Scholten ia.cr/2018/1137.  
    Return false if the construction fails to produce a valid hyperelliptic curve. 
    
    In general, there are six non-isomorphic curves H that can be constructed using this technique; 
    parameter option is an integer in [1..6] that designates the choice of curve.*/
    
    Pol<X> := PolynomialRing(Rationals());

    a,b := TranslatedRoots(C1);
    E1 := EllipticCurve(X*(X-a)*(X-b));
    f1 := Isomorphism(E1,C1);

    c,d := TranslatedRoots(C2 : perm:=option);
    E2 := EllipticCurve(X*(X-c)*(X-d));
    f2 := Isomorphism(E2,C2);

    if a*d-b*c eq 0 then
        // construction does not yield a valid curve for the given inputs.
        return false, _, _, _;
    end if;

    // see ia.cr/2018/1137 Theorem 1
    PP<x,y,z> := ProjectiveSpace(Rationals(), [1,3,1]);
    Hp := Curve(PP, y^2 - (a*d-b*c)*((a-b)*x^2-(c-d)*z^2)*(a*x^2-c*z^2)*(b*x^2-d*z^2));
    g1 := map<Hp -> E1 | [(a*b*(a-b))/(a*d - b*c) * (x^2 - z^2*(c - d)/(a - b))*z, 
                            (a*b*(a - b))/(a*d - b*c)^2*y, z^3]>;
    g2 := map<Hp -> E2 | [(c*d*(c-d))/(-a*d + b*c) * (z^2 - x^2*(a - b)/(c - d))*x, 
                            (c*d*(c - d))/(-a*d + b*c)^2*y, x^3]>;

    // Replace Hp with an integral model h:H->Hp to allow for point-finding
    tf, Htemp, f := IsHyperelliptic(Hp);
    assert tf;
    H, g := IntegralModel(Htemp);
    h := Inverse(f*g);

    return true, H, h*g1*f1, h*g2*f2;
end function;

GetCoeffs := function(basis, P)
    /* basis: a linearly independent list of points Q_1,...,Q_n on an ellitic curve E.
    P: a point on E.
    
    Return a list of integers [a_1,...,a_k] and a linearly independent 
    list of points [Q_1,...,Q_k] (with either k=n, or k=n+1 and Q_{n+1}=P) 
    such that a_1*P_1 + ... + a_k*P_k is a multiple of P. */

    newptlist := Append(basis,P);
    isindep, v := IsLinearlyIndependent(newptlist);
    if isindep then
        coeffs := Append([0 : i in [1..#basis]], 1);
        return coeffs, newptlist;
    else
        assert v[#newptlist] ne 0;
        coeffs := [v[i] : i in [1..#basis]];
        return coeffs, basis;
    end if;
end function;

TensorProd := function(pair, n1, n2)
    /* Input non-negative integers n1 and n2, and a pair <v1, v2> of lists 
    of integers with the lengths of v1 and v2 at most n1 and n2, respectively. 

    Pad v1 and v2 on the right with 0s to make them length n1 and n2,
    then return their tensor product, a vector of length n1*n2. */
    
    coeffs1 := pair[1] cat [0 : i in [1..n1 - #pair[1]]];
    coeffs2 := pair[2] cat [0 : i in [1..n2 - #pair[2]]];
    return Vector(KroneckerProduct(Matrix([coeffs1]), Matrix([coeffs2])));
end function;

GrowBasis := procedure(P1, P2, ~C1basis, ~C2basis, ~prod_basis, ~prod_vect_basis)
    /* If linearly independent, add Pi to Cibasis (i=1,2).
    If linearly independent, add P1 \otimes P2 to prod_basis 
    (expressed as coefficients in C1basis and C2basis).

    prod_vect_basis can be recovered as [TensorProd(pair, n1, n2) : pair in prod_basis], but 
    is passed as an argument to prevent recreating it more often than needed.*/
    
    n1 := #C1basis;
    n2 := #C2basis;

    coeffs1, C1basis := GetCoeffs(C1basis, P1);
    coeffs2, C2basis := GetCoeffs(C2basis, P2);

    if #C1basis gt n1 or #C2basis gt n2 then
        //prod_vect_basis must be redefined using the larger bases
        n1 := #C1basis;
        n2 := #C2basis;
        prod_vect_basis := [TensorProd(pair, n1, n2) : pair in prod_basis];
    end if;

    //if P1 \otimes P2 is indepedent of prod_basis, add it.
    if n1*n2 gt 0 then
        newvect := TensorProd(<coeffs1, coeffs2>, n1, n2);
        if IsIndependent(Append(prod_vect_basis, newvect)) then
            Append(~prod_basis, <coeffs1, coeffs2>);
            Append(~prod_vect_basis, newvect);
        end if;
    end if;
end procedure;

ProcessPair := function(C1, C2 : search_bound:=1000, max_rank := 10^10, max_curves := 6)
    /* C1 and C2 are elliptic curves with fully rational 2-torsion.
    Return non-negative integers "#prod_basis" and "total_orbits."

    This method produces up to 6 hyperelliptic curves H with maps fi:H->Ci (i=1,2).
    For each such H that contains a Weierstrass point, let Hpts denote the set of 
    all points on H that do not map to 2-torsion points on C1 or C2. (By construction
    of fi, Hpts has no Weierstrass points). There is a group action on each 
    curve H, and Hpts partitions into orbits of size 4.

    For non-isogenous C1,C2, "generators" is the sum of #Hpts / 4 (i.e. the total 
    number of orbits) as H varies over curves with a rational Weierstrass point.
    If C1,C2 are isogenous, then Rank(C1) is added to generators.

    Let G be the subgroup of the tensor product C1(\Q)\otimes C2(\Q) generated by 
    f1(P) \otimes f2(P), where P ranges over Hpts and H varies over all curves
    with a Weierstrass point; if an isogeny phi:C1->C2 exists, also include in the
    generating set R\otimes phi(R), for a set of generators R of C1(\Q)/C1(\Q)_tors.
    The subgroup produced by a point P in Hpts depends only on the orbit of P, so 
    the number of generators of G is given by "generators." Every element of G maps 
    to torsion in F^2(C1xC2).

    "#prod_basis" is the rank of G. In particular, if 
    #prod_basis = rank(C1) * rank(C2), then F^2(C1xC2)_comp is finite. 
    
    Parameters:
    
    "search_bound": a height bound used for finding rational points on H.
    "max_rank": stop finding new generators once #prod_basis >= max_rank. 
    Note that #prod_basis will be the same for any max_rank >= rank(C1)*rank(C2).
    "max_curves": stop finding new generators once this many curves H have
    been processed. Must be an integer from 1 to 6.
    */

    generators := 0;

    C1basis := []; // linearly independent set [P_1,...,P_k] in C1(\Q)
    C2basis := []; // linearly independent set [Q_1,...,Q_l] in C2(\Q)
    prod_basis := []; // linearly independent set in C1(\Q) \otimes C2(\Q), 
    // each element of the form <[a_1,..,a_r], [b_1,..,b_s]> (r <= k, s <= l)
    // representing (a_1 P_1 + ... + a_r P_r) \otimes (b_1 Q_1 + ... + b_s Q_s).

    //Isogenous curves get automatic contributions
    IsIsog, psi := IsIsogenous(C1, C2);
    if IsIsog then
        C1basis := ReducedBasis(Generators(C1));
        C2basis := [psi(P) : P in C1basis];
        prod_basis := [<[i eq j select 1 else 0 : i in [1..#C1basis]], 
                        [i eq j select 1 else 0 : i in [1..#C1basis]]> : j in [1..#C1basis]];
        generators +:= #C1basis;
    end if;

    // A modification of prod_basis, used for testing linear independence
    prod_vect_basis := [TensorProd(pair, #C1basis, #C2basis) : pair in prod_basis];

    curvenum := 1; // there are 6 curves H to consider
    while #prod_basis lt max_rank and curvenum le max_curves do
        //Define a hyperelliptic curve with maps to C1 and C2
        Hexists, H, f1, f2 := HyperWithMaps(C1, C2 : option:=curvenum);

        if Hexists then
            //Find points on H
            pts := RationalPoints(H: Bound:=search_bound);
            Wpts := [P:P in pts | -P eq P];
            Hpts := [P:P in pts | 2*f1(P) ne C1 ! 0 and 2*f2(P) ne C2 ! 0];
            assert #Hpts mod 4 eq 0;
            
            if #Wpts ne 0 and #Hpts ne 0 then 
                generators +:= #Hpts / 4;       
                for P in Hpts do
                    // Add f1(P), f2(P), and f1(P)\otimes f2(P) to C1basis, C2basis, 
                    // and prod_basis, respectively (unless already in the span up to torsion)
                    GrowBasis(f1(P), f2(P), ~C1basis, ~C2basis, ~prod_basis, ~prod_vect_basis);
                end for;
            end if;
        end if;
        curvenum +:= 1;
    end while;
    print prod_vect_basis;
    assert generators ge #prod_basis;
    return #prod_basis, generators;
end function;


FindGoodPairs := function(pairlist : search_bound := 1000, constantrank := false, progress_markers := 100, max_curves := 6);
                            
    /* every element of pairlist is a pair <C1,C2>, where C1,C2 are elliptic 
    curves with fully rational 2-torsion.
    Return a list "successes" of integers, and a list "alldata" of pairs of integers.

    "successes" contains a collection of indices i such that if <C1,C2> = pairlist[i], 
    then F^2(C1xC2)_comp is provably finite.

    "alldata" is a list of the same length as pairlist: if <C1,C2> = pairlist[i], 
    alldata[i] is the output of 
    ProcessPair(C1, C2 : search_bound:=search_bound, max_rank := Rank(C1)*Rank(C2), max_curves := max_curves).

    Parameters:

    "search_bound", "max_curves" : parameters passed to ProcessPair (see explanation there).
    "constantrank" : if false, the ranks of every curve in pairlist will be computed, which is 
    potentially time-intensive. Setting constantrank:=true will compute r1:=Rank(C1) and
    r2:=Rank(C2) of the first pair <C1,C2>, then assume r1=Rank(C1) and r2=Rank(C2) for all
    following pairs <C1,C2>.
    "progress_markers": print "n / total" after n steps if n is a multiple of progress_markers. */

    successes := [];
    alldata := [];
    curveranks := AssociativeArray();
    
    for i in [1..#pairlist] do
        if i mod progress_markers eq 0 then print i,"/",#pairlist; end if;
        C1 := pairlist[i][1];
        C2 := pairlist[i][2];
        if not constantrank or i eq 1 then
            r1 := IsDefined(curveranks, C1) select curveranks[C1] else Rank(C1);
            curveranks[C1] := r1;
            r2 := IsDefined(curveranks, C2) select curveranks[C2] else Rank(C2);
            curveranks[C2] := r2;
        end if;
        
        tensorrank, generators := ProcessPair(C1, C2 : search_bound:=search_bound, max_rank := r1*r2, max_curves := max_curves);
        Append(~alldata, <tensorrank, generators>);
        if tensorrank eq r1*r2 then Append(~successes, i); end if;
    end for;
    
    return successes, alldata;
end function;