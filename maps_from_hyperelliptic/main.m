//load "maps_from_hyperelliptic/main.m";
load "maps_from_hyperelliptic/methods.m";
load "maps_from_hyperelliptic/lmfdb-rank1torsion22.m";
rank1curves := make_data();
load "maps_from_hyperelliptic/lmfdb-rank2torsion22.m";
rank2curves := make_data();
load "maps_from_hyperelliptic/lmfdb-rank3torsion22.m";
rank3curves := make_data();

// parameter "constantrank" should be set to true only if all first components have the same rank, 
// and all second components have the same rank.

rank1pairs := &cat[[<rank1curves[i], rank1curves[j]> : j in [1..i-1]] : i in [1..100]];
rank1rank2 := &cat[[<rank1curves[i], rank2curves[j]> : j in [1..100]] : i in [1..100]];
rank1rank3 := &cat[[<rank1curves[i], rank3curves[j]> : j in [1..20]] : i in [1..500]];
rank2pairs := &cat[[<rank2curves[i], rank2curves[j]> : j in [1..i]] : i in [1..100]];
rank2diagonal := [<rank2curves[i], rank2curves[i]> : i in [1..100]];

//successes, alldata := FindGoodPairs(rank1pairs : search_bound:=1000, constantrank:=true, progress_markers := 100);
//successes, alldata := FindGoodPairs(rank1rank2 : search_bound:=1000, constantrank:=true, progress_markers := 100);
//successes, alldata := FindGoodPairs(rank1rank3 : search_bound:=1000, constantrank:=true, progress_markers := 100);
//successes, alldata := FindGoodPairs(rank2pairs : search_bound:=1000, constantrank:=true, progress_markers := 100);
//successes, alldata := FindGoodPairs(rank2diagonal : search_bound:=1000, constantrank:=true, progress_markers := 100);

/*
aa,cc := FindGoodPairs(rank1pairs : constantrank:=true);
aa,cc := FindGoodPairs(rank1curves[1..100] : secondlist:=rank2curves[1..100]);
aa,cc := FindGoodPairs(rank1curves[1..500] : secondlist:=rank3curves);

#aa;
#cc;
#[cc[n] : n in Keys(cc) | #cc[n][1] ge 1];
*/