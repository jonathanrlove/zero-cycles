/* SETUP: get 2-torsion coordinates */

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

NormalizeCurves := function(C1, C2 : option:=option)
    Pol<X> := PolynomialRing(Rationals());

    a,b := TranslatedRoots(C1);
    E1 := EllipticCurve(X*(X-a)*(X-b));
    f1 := Isomorphism(E1,C1);

    c,d := TranslatedRoots(C2 : perm:=option);
    E2 := EllipticCurve(X*(X-c)*(X-d));
    f2 := Isomorphism(E2,C2);

    return a, b, c, d, E1, f1, E2, f2;
end function;

nval := function(pqrs)
    p := pqrs[1]; q := pqrs[2]; r := pqrs[3]; s := pqrs[4]; 
    return p*(p-1)+q*(q-1)+r*(r-1)+s*(s-1)+p*q+r*s, p, q, r, s;
end function;

/* METHOD 1: six Scholten curves */

ScholtenHypers := function(C1, C2, option)
    /* Given elliptic curves C1 and C2, return a genus 2 curve H and maps f1:H->C1 and f2:H->C2,
    as in Scholten ia.cr/2018/1137.  
    Return false if the construction fails to produce a valid hyperelliptic curve. 
    
    In general, there are six non-isomorphic curves H that can be constructed using this technique; 
    parameter option is an integer in [1..6] that designates the choice of curve.*/
    
    a, b, c, d, E1, f1, E2, f2 := NormalizeCurves(C1, C2 : option:=option);

    if a*d-b*c eq 0 then
        return false, _;
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

    return true, <H, h*g1*f1, h*g2*f2>;
end function;

/* METHOD 2: sections of elliptic fibration */

FibrationHypers := function(C1, C2, pqrs)
    /* Given elliptic curves C1 and C2, return a hyperelliptic curve H with maps 
    to C1 and C2. Each curve H is a pullback of a section of the elliptic fibration of
    the Kummer surface, associated to a quadruple pqrs.

    Return false if the construction fails to produce a valid hyperelliptic curve. 
    */
    
    a, b, c, d, E1, f1, E2, f2 := NormalizeCurves(C1, C2 : option:=1);

    // construct the Kummer surface as an elliptic fibration, and Mordell-Weil generators
    F<t> := FunctionField(Rationals());
    P2<x1,x2,z1> := ProjectiveSpace(F, 2);
    C := Curve(P2, x1*(x1-a*z1)*(x1-b*z1)*t^2 - x2*(x2-c*z1)*(x2-d*z1));
    E, fE := EllipticCurve(C, C![0,0,1]);
    A22 := fE(C![a,c,1]);
    A33 := fE(C![b,d,1]);
    A23 := fE(C![a,d,1]);
    A32 := fE(C![b,c,1]);

    // Produce a section from pqrs and get its coordinate rational functions
    n, p, q, r, s := nval(pqrs);
    P := p * A22 + q * A33 + r * A23 + s * A32;

    Pol<X> := PolynomialRing(Rationals());
    sect := Inverse(fE)(P);
    assert sect[3] eq 1;
    h1n := Pol ! Numerator(sect[1]);
    h1d := Pol ! Denominator(sect[1]);
    h2n := Pol ! Numerator(sect[2]);
    h2d := Pol ! Denominator(sect[2]);

    Hpoly := h1n*h1d*(h1n-a*h1d)*(h1n-b*h1d);
    // Ignore degenerate cases: Hpoly is 0, not squarefree, or the wrong degree
    if Hpoly eq 0 then
        return false, <4*n-2, -1>;
    end if;
    if &*[c[2] : c in Factorization(Hpoly)] ne 1 or Degree(Hpoly) ne 8*n-2 then
    	newHpoly := &*[c[1] : c in Factorization(Hpoly) | c[2] mod 2 eq 1];
    	Htemp := HyperellipticCurve(newHpoly);
    	return false, <4*n-2, Genus(Htemp)>;
    end if;
    
    Htemp<x,y,z> := HyperellipticCurve(h1n*h1d*(h1n-a*h1d)*(h1n-b*h1d));
    H, g := IntegralModel(Htemp);
    ginv := Inverse(g);

    // Projectivize h1, h2 in order to define maps to E1, E2
    g1n := Numerator(Evaluate(h1n,x/z)/Evaluate(h1d,x/z));
    g1d := Denominator(Evaluate(h1n,x/z)/Evaluate(h1d,x/z));
    g2n := Numerator(Evaluate(h2n,x/z)/Evaluate(h2d,x/z));
    g2d := Denominator(Evaluate(h2n,x/z)/Evaluate(h2d,x/z));
    g1 := map<Htemp -> E1 | [g1n*g1d, y*z, g1d^2]>;
    g2 := map<Htemp -> E2 | [g2n*g2d, y*x, g2d^2]>;

    return true, <H, ginv*g1*f1, ginv*g2*f2>;
end function;
