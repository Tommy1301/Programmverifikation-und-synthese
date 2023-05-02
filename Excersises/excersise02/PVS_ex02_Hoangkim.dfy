//Excercise 1.7 (Excercise 01)
//a)
method MaxSum(x:int, y:int) returns (s:int,m:int)
ensures s == x+y && s >= m
ensures m >= x && m >= y && ( m == x || m == y )


//Problem 2
//excercise 1.8
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y:int)
//requires s>=m && m>=0
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


/*
{
     if (s <= m){
        x := s;
        y := m - s;
    }else{
        x := m;
        y := s - m;
    }
    
}
*/