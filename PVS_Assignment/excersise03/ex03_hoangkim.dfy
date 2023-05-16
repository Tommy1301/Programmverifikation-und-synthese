method Gauss(n:int) returns(sum:int)
requires n >= 0
ensures sum == n*(n+1)/2
{
    sum := 0;
    var i := 0;
    assert sum == 0 && i == 0;
    while i < n
    invariant sum == i*(i+1)/2 && i <= n
    {
        i := i+1;
        sum := sum + i;
    }
    assert sum == n*(n+1)/2;

}


//Problem01
//b)
method ht1_1(){
    var x,y:int := *,*;
    assume x <= 49.5;
    x :=  2*x + 1;
    assert x <= 100;
}

method ht1_2(){
    var x,y:int := *,*;
    var b:bool := *;
    assume (2*x >= y && y>= 0) ∨ (2*x<=y && y<=0)  ;
        y:=2*x+y;
    assert 2*x*y <= y*y;
} 

method ht1_3(){
    var x,y:int := *,*;
    var b:bool := *;
    assume 0<=x<=1  ;
        y:= x+ 1;
    assert x*x <= y <= (x+1)*(x+1);
} 

//Problem02
method ht2_1(){
    var x,y:int := *,*;
    assume x <= y;
        x := 2*x+1; 
    assert x <= 2*y+1; 
}

method ht2_2(){
    var x,y:int := *,*;
    assume 0 < x < 100;
        x := 2*x - 1; 
    assert -1 < x < 199 ; 

}

method ht2_3(){
    var x,y:int := *,*;
    assume x < y;
        y := x-1; 
    assert y < x ; 

}

//Problem 03
method ht3_1(){
    var x,y:int := *,*;
    assume y+1 == x-1;
        y := y+1;
    assert x == y+1 ; 

}

method ht3_1_2(){
    var x,y:int := *,*;
    assume y == x-1;
        x := x+1;
    assert y+1 == x-1;
}

method ht3_2(){
    var x,y:int := *,*;

    assume (x+1 == y+1) && (x < y);
        x := x + 1; 
    assert x == y+1;
}


//problem04
method ht4_1(){
    var x,y:int := *,*;

    assume -3 <= x <= 3;
    //assert 0 <= x*x <= 9;
        x := x*x + 1; 
    assert x*x <= 100;
}

method ht4_2(){
    var x,y:int := *,*;

    assume -3 <= x <= 3;
        x := x*x + 1; 
    assert x*x <= 100;
}
