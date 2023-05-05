// Problem 1 //# 3
//Problem 2,  //# 0
//Excercise 1.6 //# It seems you misunderstood the question.
method Min(x: int, y:int) returns (m:int)
//requires x >= 0 && y >= 0
ensures m <= x && m <= y && (m == x || m == y)
{
      m := if x < y then x else y; //keyword if then else
}


//Problem 3  //# 2
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
//# Better: 
method BetterTestMaxSum() 
{
    var a,b := 1928,1;
    var s,m := MaxSum(1928,1);
    assert s == 1929 && m == 1928; 
}


//Problem 4
method Ex_01_4a()  //# 2
{
    var x:int, y:int := *,*;

    assume x ≤ y;
        x := 2*x+1;
    assert  x ≤ 2*y+1 ;
        y := x+y;
    assert y >= (x-1)/2+x;

}


method Ex_01_4b()     //# 2
{
    var x:int, y:int := *,*;

    assume y ≥ x && x ≥ 0;
        x := 2*x+1;
    assert y ≥ 0 ;
        y := x+y;
    assert x ≤ y ;

}

method Ex_01_4c(){      //# 0
    var x:int, y:int := *,*;

    assume x == (3/2 - y/4);
        x := 2*x+1;
    assume y == 8 - 2*x ;    //# this should be "assert" and then you would see that it doesn't work. 
        y := x+y;
    assert x + y == 8 ;
}

//# 9 pts