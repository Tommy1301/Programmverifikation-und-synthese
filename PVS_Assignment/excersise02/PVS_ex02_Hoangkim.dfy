//Problem 2
//excercise 1.8
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y:int)
requires s>=m && m>=0
ensures s == x + y 
ensures (m == x || m == y) && x <= m && y <= m

//test passed
method Test_ReconstructFromMaxSum()
{
    var s,m := *,*;
    assume s == 15; 
    assume m == 10;
    var x,y := ReconstructFromMaxSum(s,m);
    assert x == 10 ∨ y==10;
    assert (x == 10 && y == 5) ∨ (x == 5 && y == 10);
}

//test not passed
//for example max = -10 and sum = 10 but here after reconstruct max = 10 
method Test_ReconstructFromMaxSum2()
{
    var s,m := *,*;
    assume s == 10; 
    assume m == -10;
    var x,y := ReconstructFromMaxSum(s,m);
    assert x == 10 ∨ y == 10;
    assert (x == 10 && y == -20) ∨ (x == -20 && y == 10);
}



//Problem 3
//Exercise 2.6
//a)
method ht3_1(){
    var x:int := *;
    assume -128 ≤ x < 0; 
        x:= x-1;
    assert -129 ≤ x < -1;
}


method ht3_2(){
    var x,y:int := *,*;
    assume 0 ≤ x ≤ y < 100;
    y := y-x;
    assert (0 ≤ y < 100-x) && (y <= 100); //why y equal 100 still correct?
}

method ht3_3(){
    var x,y:int := *,*;
    assume (x % 2) == 0  && y < 100;
        x,y := y,x;
    assert y % 2 == 0 && x < 100;
}


//Problem 4
//Excercise 2.8
method ht4_1(){
    var x,y:int := *,*;
    var b:bool := *;
    assume x <= y  ;
        b := y < 10;
    assert b ==> (x <= y);
} 

method ht4_2(){
    var x,y:int := *,*;
    assume   (0 <= x <= 50) && y <= 0;
        x,y := 2*x , x+y;
    assert 0 <= x <= 100 && y <= x;
} 


method ht4_3(){
    var x,y:int := *,*;

    assume y >= 5 && 2*y <= y;
        x := 2*y;
    assert 10 <= x <= y;
}