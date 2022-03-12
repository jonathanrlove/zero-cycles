TranslatedRoots := function(curve : perm:=1)
    /* given an elliptic curve, return two values a and b such that
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
    /* Given elliptic curves C1 and C2, return a genus 2 curve H with maps f1:H->C1 and f2:H->C2. 
    Return false if the construction fails to produce a valid curve. 
    
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
        return false, _, _, _;
    end if;

    PP<x,y,z> := ProjectiveSpace(Rationals(), [1,3,1]);
    Hp := Curve(PP, y^2 - (a*d-b*c)*((a-b)*x^2-(c-d)*z^2)*(a*x^2-c*z^2)*(b*x^2-d*z^2));
    g1 := map<Hp -> E1 | [(a*b*(a-b))/(a*d - b*c) * (x^2 - z^2*(c - d)/(a - b))*z, 
                            (a*b*(a - b))/(a*d - b*c)^2*y, z^3]>;
    g2 := map<Hp -> E2 | [(c*d*(c-d))/(-a*d + b*c) * (z^2 - x^2*(a - b)/(c - d))*x, 
                            (c*d*(c - d))/(-a*d + b*c)^2*y, x^3]>;

    tf, Htemp, f := IsHyperelliptic(Hp);
    assert tf;
    H, g := IntegralModel(Htemp);
    h := Inverse(f*g); // map from H to Hp

    return true, H, h*g1*f1, h*g2*f2;
end function;

GetCoeffs := function(basis, P)
    /* basis: a linearly independent set of points on an ellitic curve E.
    P: a point on E.
    
    If P is in the span of basis (up to torsion), return a list of corresponding coefficients, and basis.
    Otherwise, return [0,0,...,0,1] (length = #basis+1) and a new basis with P added. */

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
    /* Given a pair of vectors with lengths <=n1 and <=n2, 
    first pad them on the right with 0s to make them length n1 and n2,
    then return the tensor product, a vector of length n1*n2. */
    
    coeffs1 := pair[1] cat [0 : i in [1..n1 - #pair[1]]];
    coeffs2 := pair[2] cat [0 : i in [1..n2 - #pair[2]]];
    return Vector(KroneckerProduct(Matrix([coeffs1]), Matrix([coeffs2])));
end function;

GrowBasis := procedure(P1, P2, P, ~C1basis, ~C2basis, ~Hpts, ~prod_basis, ~prod_vect_basis)
    /* Add P1 to C1basis (unless it is already in the span up to torsion);
    Add P2 to C2basis (unless it is already in the span up to torsion);
    Add the tensor of P1 and P2 to prod_basis (unless it is already in the span up to torsion).

    prod_vect_basis can be recovered as [TensorProd(pair, n1, n2) : pair in prod_basis], but 
    is passed as an argument to prevent redundantly recreating it many times.*/
    
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

    //see if we have found an independent element of the tensor product
    if n1*n2 gt 0 then
        newvect := TensorProd(<coeffs1, coeffs2>, n1, n2);
        if IsIndependent(Append(prod_vect_basis, newvect)) then
            Append(~Hpts, P);
            Append(~prod_basis, <coeffs1, coeffs2>);
            Append(~prod_vect_basis, newvect);
        end if;
    end if;
end procedure;

ProcessPair := function(C1, C2 : search_bound:=1000, rank1:=-1, rank2:=-1)
    /* Attempt to prove F^2(C1xC2)_comp is torsion. */

    success := false;
    attempt := 1;
    C1basis := [];
    C2basis := [];
    prod_basis := [];
    Hpts := [];
    total_orbits := 0;

    // compute ranks of C1 and C2 if not already given
    if rank1 eq -1 then rank1 := Rank(C1); end if;
    if rank2 eq -1 then rank2 := Rank(C2); end if;

    //Isogenous curves get some automatic contributions
    IsIsog, psi := IsIsogenous(C1, C2);
    if false then //IsIsog then
        C1basis := ReducedBasis(Generators(C1));
        C2basis := [psi(P) : P in C1basis];
        prod_basis := [<[i eq j select 1 else 0 : i in [1..#C1basis]], [i eq j select 1 else 0 : i in [1..#C1basis]]> : j in [1..#C1basis]];
    end if;

    prod_vect_basis := [TensorProd(pair, #C1basis, #C2basis) : pair in prod_basis];

    while not success and attempt le 1 do
        //Define a hyperelliptic curve with maps to C1 and C2
        Hexists, H, f1, f2 := HyperWithMaps(C1, C2 : option:=attempt);

        if Hexists then
            //Find points on H
            pts := RationalPoints(H: Bound:=search_bound);
            Wpts := [P:P in pts | -P eq P];
            nonWpts := [P:P in pts | -P ne P and f1(P) ne C1 ! 0 and f2(P) ne C2 ! 0];
            // The points mapping to the identity under f1 or f2 will not help us;
            // also, these are the only non-Weierstrass points that are fixed by x -> -x or y -> -y.
            assert #nonWpts mod 4 eq 0;
            
            if #Wpts ne 0 and #nonWpts ne 0 then 
                total_orbits +:= #nonWpts / 4;       
                // Find the images of P-W on E1 and E2 for non-Weierstrass P and Weierstrass W.
                W := Wpts[1]; // other choices of W will differ by 2-torsion
                old_num := #prod_basis;
                for P in nonWpts do
                    GrowBasis(f1(P)-f1(W), f2(P)-f2(W), P, ~C1basis, ~C2basis, ~Hpts, ~prod_basis, ~prod_vect_basis);
                end for;

                if #prod_basis eq rank1 * rank2 then
                    return true, [total_orbits, #prod_basis];
                end if;
            end if;
        end if;
        attempt +:= 1;
    end while;
    return #prod_basis eq rank1 * rank2, [total_orbits, #prod_basis];
end function;


FindGoodPairs := function(pairlist : search_bound := 1000, constantrank := false, progress_markers := 100); //progress_markers:=10^10
                            
    /* Returns a list of pairs of curves (one from list1, one from list2) 
    with some property I'll describe later */

    successes := [];
    alldata := [];

    if constantrank then 
        rank1 := Rank(pairlist[1][1]);
        rank2 := Rank(pairlist[1][2]);
    else 
        rank1 := -1; 
        rank2 := -1;
    end if;
    
    for i in [1..#pairlist] do
        if i mod progress_markers eq 0 then print i,"/",#pairlist; end if;
        C1 := pairlist[i][1];
        C2 := pairlist[i][2];
        
        goodpair, data := ProcessPair(C1, C2 : search_bound:=search_bound, rank1:=rank1, rank2:=rank2);
        Append(~alldata, data);
        if goodpair then Append(~successes, i); 
        end if;
    end for;
    
    return successes, alldata;
end function;

//OVER QUADRATIC EXTENSIONS (SET x COORDINATE xval arbitrarily)
/*
total := 0;
successes := 0;
for i in [1..10] do
    a := xcoords[i][1]-xcoords[i][3];
    b := xcoords[i][2]-xcoords[i][3];
    for j in [1..i-1] do
        total +:= 1;
        c := xcoords[j][1]-xcoords[j][3];
        d := xcoords[j][2]-xcoords[j][3];
        
        for height in [1..20] do
            for q in [1..height] do
                p := height-q;
                if GCD(p,q) eq 1 and p/q ne 4/3 then
                    xval := p/q;
                    if IsIrreducible(Evaluate(DefiningPolynomial(H),[xval,X,1])) then
                        K<r> := NumberField(Evaluate(DefiningPolynomial(H),[xval,X,1]));
                        HK := BaseChange(H,K);
                        tf, HH, f := IsHyperelliptic(HK);
                        
                        E1 := EllipticCurve(X*(X-a)*(X-b));
                        E1K := BaseChange(E1, K);
                        f1 := map<HK -> E1K | [(a*b*(a-b))/(a*d - b*c) * (x^2 - z^2*(c - d)/(a - b))*z, (a*b*(a - b))/(a*d - b*c)^2*y, z^3]>;
                        E2 := EllipticCurve(X*(X-c)*(X-d));
                        E2K := BaseChange(E2, K);
                        f2 := map<HK -> E2K | [(c*d*(c-d))/(-a*d + b*c) * (z^2 - x^2*(a - b)/(c - d))*x, (c*d*(c - d))/(-a*d + b*c)^2*y, x^3]>;

                        P1:= E1K ! Generators(E1)[3];
                        Q1:= f1(HK![xval,r,1]);
                        if not IsLinearlyIndependent(P1,Q1) then
                            print <xval,i,j,P1,Q1>;
                        end if;
                        P2:= E2K ! Generators(E2)[3];
                        Q2:= f2(HK![xval,r,1]);
                        if not IsLinearlyIndependent(P2,Q2) then
                            print <xval,i,j,P2,Q2>;
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end for;
end for;



h := Inverse(f);
pts := RationalPoints(HH:Bound:=100);
Wpts := [P:P in pts | -P eq P];
nonWpts := [P:P in pts | -P ne P];

E1a := BaseChange(WeierstrassModel(curves[i]),K);
E1 := BaseChange(EllipticCurve(X*(X-a)*(X-b)),K);
g1 := Isomorphism(E1,E1a);
f1 := map<H -> E1 | [(a*b*(a-b))/(a*d - b*c) * (x^2 - z^2*(c - d)/(a - b))*z, (a*b*(a - b))/(a*d - b*c)^2*y, z^3]>;
E2a := BaseChange(WeierstrassModel(curves[j]),K);
E2 := BaseChange(EllipticCurve(X*(X-c)*(X-d)),K);
g2 := Isomorphism(E2,E2a);
f2 := map<H -> E2 | [(c*d*(c-d))/(-a*d + b*c) * (z^2 - x^2*(a - b)/(c - d))*x, (c*d*(c - d))/(-a*d + b*c)^2*y, x^3]>;

S1:=[];
S2:=[];
for Wpt in Wpts do
    for nonWpt in nonWpts do
        if Order(g1(f1(h(Wpt))) - g1(f1(h(nonWpt)))) eq 0 and Order(g2(f2(h(Wpt))) - g2(f2(h(nonWpt)))) eq 0 then
            Append(~S1, g1(f1(h(Wpt))) - g1(f1(h(nonWpt))));
            Append(~S2, g2(f2(h(Wpt))) - g2(f2(h(nonWpt))));
        end if;
    end for;
end for;
ReducedBasis(S);


// ONE RANK 1 and ONE RANK 2

load "rank1torsion22.m";
curves1 := make_data();
load "rank3torsion22.m";
curves2 := make_data();

xcoords1 := [];
for C in curves1 do
    E := WeierstrassModel(C);
    Append(~xcoords1, [P[1] : P in DivisionPoints(E!0, 2) | P ne E!0]);   
end for;
xcoords2 := [];
for C in curves2 do
    E := WeierstrassModel(C);
    Append(~xcoords2, [P[1] : P in DivisionPoints(E!0, 2) | P ne E!0]);   
end for;

PP<x,y,z> := ProjectiveSpace(Rationals(), [1,3,1]);
Pol<X> := PolynomialRing(Rationals());

total := 0;
successes := 0;
numpts := [];
for i in [1..500] do
    print i,successes;
    a := xcoords1[i][1]-xcoords1[i][3];
    b := xcoords1[i][2]-xcoords1[i][3];
    for j in [1..20] do
        total +:= 1;
        c := xcoords2[j][1]-xcoords2[j][3];
        d := xcoords2[j][2]-xcoords2[j][3];
        H := Curve(PP, y^2 - (a*d-b*c)*((a-b)*x^2-(c-d)*z^2)*(a*x^2-c*z^2)*(b*x^2-d*z^2));
        tf, HH, f := IsHyperelliptic(H);
        if tf then
            HH, g := IntegralModel(HH);
            h := Inverse(f*g);
            pts := RationalPoints(HH:Bound:=1000);
            Wpts := [P:P in pts | -P eq P];
            nonWpts := [P:P in pts | -P ne P];
                    
            if #Wpts ne 0 and #nonWpts ne 0 then
                Append(~numpts, #nonWpts);
                E1a := WeierstrassModel(curves1[i]);
                E1 := EllipticCurve(X*(X-a)*(X-b));
                g1 := Isomorphism(E1,E1a);
                f1 := map<H -> E1 | [(a*b*(a-b))/(a*d - b*c) * (x^2 - z^2*(c - d)/(a - b))*z, (a*b*(a - b))/(a*d - b*c)^2*y, z^3]>;
                E2a := WeierstrassModel(curves2[j]);
                E2 := EllipticCurve(X*(X-c)*(X-d));
                g2 := Isomorphism(E2,E2a);
                f2 := map<H -> E2 | [(c*d*(c-d))/(-a*d + b*c) * (z^2 - x^2*(a - b)/(c - d))*x, (c*d*(c - d))/(-a*d + b*c)^2*y, x^3]>;
                E1pts := [];
                E2pts := [];
                for nonWpt in nonWpts do
                    if Order(g1(f1(h(Wpts[1]))) - g1(f1(h(nonWpt)))) eq 0 then
                        Append(~E1pts, g1(f1(h(Wpts[1]))) - g1(f1(h(nonWpt))));
                        Append(~E2pts, g2(f2(h(Wpts[1]))) - g2(f2(h(nonWpt))));
                    end if;
                end for;
                if #ReducedBasis(E1pts) ge 1 and #ReducedBasis(E2pts) ge 3 then
                    successes+:=1;
                end if;      
            end if;
        end if;
    end for;
end for;
*/