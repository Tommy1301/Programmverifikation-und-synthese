
//Problem 2,
//Excercise 1.6
method Min(x: int, y:int) returns (m:int)
//requires x >= 0 && y >= 0
ensures m <= x && m <= y && (m == x || m == y)
{
      m := if x < y then x else y; //keyword if then else
}


//Problem 3
//Excercise 1.7
//a)
method MaxSum(x:int, y:int) returns (s:int,m:int)
//requires x >= 0 && y >= 0
ensures s == x+y
ensures m >= x && m >= y && ( m == x || m == y )

//b)
method TestMaxSum() 
{
    var a,b := *,*;
    assume a == 1928; 
    assume b == 1;
    var s,m := MaxSum(a,b);
    assert s == a+b && m == a; 

}

//Problem 4
method Ex_01_4a()
{
    var x:int, y:int := *,*;

    assume x ≤ y;
        x := 2*x+1;
    assert  x ≤ 2*y+1 ;
        y := x+y;
    assert y >= (x-1)/2+x;

}


method Ex_01_4b()
{
    var x:int, y:int := *,*;

    assume y ≥ x && x ≥ 0;
        x := 2*x+1;
    assert y ≥ 0 ;
        y := x+y;
    assert x ≤ y ;

}

method Ex_01_4c(){
    var x:int, y:int := *,*;

    assume x == (3/2 - y/4);
        x := 2*x+1;
    assume y == 8 - 2*x ;
        y := x+y;
    assert x + y == 8 ;
}


