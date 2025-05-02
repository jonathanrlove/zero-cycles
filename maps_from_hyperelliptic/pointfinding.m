load "hyperswithmaps.m";

/* Section 1: Some methods for handling subgroups of rational points on elliptic curves. */

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

GrowBasis := procedure(P, f1, f2, ~C1basis, ~C2basis, ~generators, ~prod_basis, ~prod_vect_basis)
    /* If linearly independent, add Pi = fi(P) to Cibasis (i=1,2).
    If linearly independent, add P1 \otimes P2 to prod_basis 
    (expressed as coefficients in C1basis and C2basis).

    prod_vect_basis can be recovered as [TensorProd(pair, n1, n2) : pair in prod_basis], but 
    is passed as an argument to prevent recreating it more often than needed.*/
    
    n1 := #C1basis;
    n2 := #C2basis;

    coeffs1, C1basis := GetCoeffs(C1basis, f1(P));
    coeffs2, C2basis := GetCoeffs(C2basis, f2(P));

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
            Append(~generators, <P, f1, f2>);
            Append(~prod_basis, <coeffs1, coeffs2>);
            Append(~prod_vect_basis, newvect);
        end if;
    end if;
end procedure;

/* Section 2: Generating rational equivalences form hyperelliptics. */

Boundedpqrs := function(bound)
    /* return all quadruples [p,q,r,s] such that nval(p,q,r,s) <= bound.*/

    all := [];
    // p^2+pq+q^2-p-q <= n implies |p-1/3|, |q-1/3| <= sqrt((4/3)(n+1/3)).
    sqrt := Sqrt((4/3) * (bound + 1/3));
    for pqrs in CartesianPower([Floor(1/3-sqrt)..Ceiling(1/3+sqrt)], 4) do
        if nval(pqrs) le bound then
            Append(~all, pqrs);
        end if;
    end for;
    return all;
end function;

HasFullTwoTorsion := function(E)
    return #DivisionPoints(Identity(E), 2) eq 4;
end function;

HyperGenerators := function(C1, C2 :
                        scholten := true, fibration := true, isogeny := true,
                        section_bound := 2)
    /* Generates a list of tuples of the form <i, d, f1, f2>, where
        - i is either 1 or 2;
        - d is either an integer from 1 to 6 (if i=1) or a quadruple of 
          integers [p,q,r,s] with nval(p,q,r,s) <= section_bound (if i=2);
        - fi is an isogeny from an elliptic curve to Ci.
    
    These tuples will be used the function HyperWithMaps.
    */

    hypertypes := [* *];
    if scholten then 
        hypertypes := [* <1, i> : i in [1..6] *];
    end if;
    if fibration then 
        hypertypes cat:= [* <2, pqrs> : pqrs in Boundedpqrs(section_bound) *];
    end if;

    allgens :=  [* <a[1], a[2], Isomorphism(C1, C1), Isomorphism(C2, C2)> : a in hypertypes *];
    if isogeny then
        for D1 in [E : E in IsogenousCurves(C1) | HasFullTwoTorsion(E)] do
            _, phi1 := IsIsogenous(D1, C1);
            for D2 in [E : E in IsogenousCurves(C2) | HasFullTwoTorsion(E)] do
                _, phi2 := IsIsogenous(D2, C2);
                if not (IsIsomorphic(C1,D1) and IsIsomorphic(C2,D2)) then
                    allgens cat:= [* <a[1], a[2], phi1, phi2> : a in hypertypes *];
                end if;
            end for;
        end for;
    end if;

    return allgens;
end function;

ProcessPair := function(C1, C2 : search_bound:=1000, max_rank := 10^10, max_curves := 10^10,
                        scholten := true, fibration := true, isogeny := true,
                        section_bound := 2)
    /* C1 and C2 are elliptic curves with fully rational 2-torsion.
    
    Return "generators," a list of tuples <P,f1,f2>, where P is on a curve C, and 
    f1:C->C1 and f2:C->C2 are maps. As the tuple varies over generators, 
    f1(P) \otimes f2(P) will produce an independent set of elements of 
    C1(\Q)\otimes C2(\Q), all of which map to torsion in F^2(C1xC2). If the length 
    of the list of tuples equals rank(C1)*rank(C2) then F^2(C1xC2)_comp is finite.
    
    Parameters:
    
    "search_bound": a height bound used for finding rational points on H.

    "max_rank": stop finding new generators once #generators >= max_rank. 
    Note that #generators will never exceed Rank(C1)*Rank(C2).

    "max_curves": Limits the number of hyperelliptics to produce.

    "scholten": Use Scholten curves to find generators.

    "fibration": use elliptic fibration to find generators.

    "isogeny": use pairs of isogenous curves to find generators.

    "section_bound": bound on the lattice norm n(p,q,r,s) (as in Lemma 3.9).
    The genus of the corresponding hyperelliptic curves will all be at most 4n-2.
    Only relevant if fibration:=true or isogenyfibrations:=true.  
    */

    generators := [* *];
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
        generators cat:= SequenceToList([<P, IdentityIsogeny(C1), psi> : P in C1basis]);
    end if;

    // A modification of prod_basis, used for testing linear independence
    prod_vect_basis := [TensorProd(pair, #C1basis, #C2basis) : pair in prod_basis];

    // Compile a list of all ways to generate hyperelliptics
    curvegens := HyperGenerators(C1, C2 : scholten := scholten, fibration := fibration, 
                             isogeny := isogeny, section_bound := section_bound);
    

    numgens := #generators;
    genspermethod := [numgens, 0, 0, 0, 0]; //isogenouscurves; Scholten; beyond Scholten; isogenies+beyond Scholten

    curvenum := 1;
    //print #curvegens;
    while #prod_basis lt max_rank and curvenum le Min(max_curves, #curvegens) do
        //Define a hyperelliptic curve with maps to C1 and C2
        
        method, param, phi1, phi2 := Explode(curvegens[curvenum]);
        D1 := Domain(phi1); D2 := Domain(phi2);
        if method eq 1 then 
            Hexists, Htuple := ScholtenHypers(D1, D2, param);
        else
            Hexists, Htuple := FibrationHypers(D1, D2, param);
        end if;

        if Hexists then
            //printf "%o", curvenum;
            H, g1, g2 := Explode(Htuple);
            f1 := g1*phi1;
            f2 := g2*phi2;

            //Find points on H
            pts := RationalPoints(H: Bound:=search_bound);
            Hpts := [P:P in pts | 2*f1(P) ne C1 ! 0 and 2*f2(P) ne C2 ! 0];
            assert #Hpts mod 4 eq 0;
            
            for P in Hpts do 
                // Add f1(P), f2(P), and f1(P)\otimes f2(P) to C1basis, C2basis, 
                // and prod_basis, respectively (unless already in the span up to torsion)
                GrowBasis(P, f1, f2, ~C1basis, ~C2basis, ~generators, ~prod_basis, ~prod_vect_basis);

                if #generators gt numgens then
                    methodindex := 2;
                    if method eq 2 then methodindex +:= 1; end if;
                    if not (IsIsomorphic(D1,C1) and IsIsomorphic(D2,C2)) then methodindex +:= 2; end if;
                    genspermethod[methodindex] +:= 1;
                end if;
                numgens := #generators;
            end for;
        end if;
        curvenum +:= 1;
    end while;
    assert #generators eq #prod_basis and #prod_basis eq #prod_vect_basis and #generators eq &+genspermethod;
    return generators, genspermethod;
end function;


FindGoodPairs := function(pairlist : search_bound := 1000, constantrank := false, max_curves := 10^10,
                                     scholten := true, fibration := true, isogeny := true, section_bound := 2, filename := "goodpairs.txt");
                            
    /* every element of pairlist is a pair <C1,C2>, where C1,C2 are elliptic 
    curves with fully rational 2-torsion.

    For each pair <C1, C2> in pairlist, the code will print a line to filename

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

    Output: a list consisting of <i, [a1,a2,a3,a4,a5]> for each pair in pairlist.

    Parameters:

    "search_bound", "max_curves", "scholten", "fibration", "isogeny", "section_bound" : 
        parameters passed to ProcessPair (see explanation there).
    "constantrank" : if false, the ranks of every curve in pairlist will be computed, which is 
        potentially time-intensive. Setting constantrank:=true will compute r1:=Rank(C1) and
        r2:=Rank(C2) of the first pair <C1,C2>, then assume r1=Rank(C1) and r2=Rank(C2) for all
        following pairs <C1,C2>.
    "genlist" : determines the output, see above.
    */

    alldata := [];
    curveranks := AssociativeArray();

    justisogenous := 0;
    scholtencount := 0;
    beyondscholten := 0;
    isogenyneeded := 0;
    
    for i in [1..#pairlist] do
        C1 := pairlist[i][1];
        C2 := pairlist[i][2];
        if not constantrank or i eq 1 then
            r1 := IsDefined(curveranks, C1) select curveranks[C1] else Rank(C1);
            curveranks[C1] := r1;
            r2 := IsDefined(curveranks, C2) select curveranks[C2] else Rank(C2);
            curveranks[C2] := r2;
        end if;
        
        generators, genspermethod := 
            ProcessPair(C1, C2 : search_bound:=search_bound, max_rank := r1*r2, max_curves := max_curves, 
                                 scholten := scholten, fibration := fibration, isogeny := isogeny,
                                 section_bound := section_bound);
        Append(~alldata, <i, genspermethod>);
        if #generators eq r1*r2 then 
            if genspermethod[4]+genspermethod[5] gt 0 then isogenyneeded +:= 1; 
            elif genspermethod[3] gt 0 then beyondscholten +:= 1;
            elif genspermethod[2] gt 0 then scholtencount +:= 1;
            else justisogenous +:= 1; end if;
        end if;


        fprintf filename, "%o / %o: %o, %o\n", i, #pairlist, genspermethod,
            [justisogenous, scholtencount, beyondscholten, isogenyneeded];
    end for;
    
    return alldata;
end function;
                        

GenCoeffs := function(genlist)
    /* genlist : a list of tuples <P, f1, f2>, where P is a point on some curve C
    (C does _not_ need to be the same for all tuples), and f1:C->C1
    and f2:C->C2 are maps (C1 and C2 _must_ be the same for all tuples).
    For instance, one can set genlist := alldata[i] for any i, if alldata
    is the second output of FindGoodPairs (with parameter genlist:=true).
    
    Return sequences coeff_list, [R_1,...,R_k], [S_1,...,S_l],
    where
    - R_1, ..., R_k generates C1(\Q) modulo torsion; 
    - S_1, ..., S_l generates C2(\Q) modulo torsion;
    - coeff_list is a list of pairs of the same length as genlist. If
    genlist[i] = <P, f1, f2>, then 
    coeff_list[i] = <[a_1,...,a_k], [b_1,...,b_l]>,
    where a_1 R_1 + ... + a_k R_k is a multiple of f1(P),
    and   b_1 S_1 + ... + b_l S_l is a multiple of f2(P).
    */

    if #genlist eq 0 then return []; end if;

    C1 := Codomain(genlist[1][2]);
    C2 := Codomain(genlist[1][3]);
    C1basis := ReducedBasis(Generators(C1));
    C2basis := ReducedBasis(Generators(C2));
    n1 := #C1basis;
    n2 := #C2basis;

    coeff_list := [];
    for gen in genlist do
        P := gen[1];
        f1 := gen[2];
        f2 := gen[3];

        coeffs1 := GetCoeffs(C1basis, f1(P));
        coeffs2 := GetCoeffs(C2basis, f2(P));
        Append(~coeff_list, <coeffs1, coeffs2>);
    end for;

    return coeff_list, C1basis, C2basis;
end function;



FindGenusDrop := procedure(pairlist, filename : section_bound := 3);
    
    tuples := [pqrs : pqrs in Boundedpqrs(section_bound) | nval(pqrs) gt 0];
    for i in [1..#pairlist] do
        C1 := pairlist[i][1];
        C2 := pairlist[i][2];
        if not jInvariant(C1) eq jInvariant(C2) then
        
    	    badcurves := [* *];
            for pqrs in tuples do
                Hexists, Htuple := FibrationHypers(C1, C2, pqrs);
        
                if not Hexists then
                    Append(~badcurves, <pqrs, Htuple>);
                end if;
            end for;
            fprintf filename, "%o/%o, %o, %o\n", i, #pairlist, #badcurves, badcurves;
        end if;
    end for;
end procedure;

