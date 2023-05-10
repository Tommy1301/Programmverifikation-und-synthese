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