// Solutions to Exercise sheet #01

// Problem 1 (there was nothing to hand in) 

// Problem 2
// has many, many solutions ...
// An example is: 

method Min(x:int,y:int) returns (m:int)
ensures m <= x && m <= y
{
  m := -(x*x + y*y);
}

// Problem 3 
//---------------------------------------

// Problem 3_a 

// only the specification, no implementation required:

method MaxSum(x:int,y:int) returns (s:int,m:int)
ensures s == x+y && m <= x && m <= y && (m==x || x==y)  

// Problem 3_b 
// multiple assignment in Dafny is :  x,y := t1, t2;
//                         and NOT : (x,y) := (t1,t2);

method TestMaxSum()   
{
  var a,b := MaxSum(1928,1);     // this is the call  
  assert a == 1929 && b == 1928;
}

// Problem 4

// Some of you replaced "assert" by "assume" 
// This is NOT ok, since "assert" and "assume" have 
// very different semantics

// Problem 4_a, 4_b, 4_c  have many different solutions
// We give here the "best" solutions in a certain sense
// which we shall discuss in class. 

// Problem 4_a
// ----------------------------------

method Ex_01_4_a() 
{   var x:int,y:int := *,*;

    assume x ≤ y; 
      x := 2*x+1;
    assert x <= 2*y + 1       && x%2==1;    // this, or
    assert 3*x <= 2*(x+y) + 1 && x%2==1;    // this, or both
      y := x+y;
    assert 3*x <= 2*y +1;   
}    

// Problem 4_b
// ----------------------------------
method Ex_01_4_b() 
{   var x:int, y:int := *,*;

    assume 0 <= y; 
      x := 2*x+1;
    assert x <= x+y && x%2==1;  
      y := x+y;
    assert x <= y   && x%2==1;  
}    

// Problem 4_c
// ----------------------------------
method Ex_01_4_c() 
{   var x:int,y:int := *,*;

    assume 4*x+y == 6; 
      x := 2*x+1;
    assert 2*x+y == 8;  
      y := x+y;
    assert x+y == 8;  
}    
