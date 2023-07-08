//problem 01
//problem 02

//# There is no specification !! 
/*
method rotateLeft<T>(a: array<T>)
  modifies a


{
  var len := a.Length;   //# could be ghost
  var i := 0;

  while (i < len)
    invariant 0 <= i <= len
    invariant forall j :: i < j < len ==> a[j] == old(a[(j + 1) % len])
  {
    var temp := a[(i + 1) % len];
    a[(i + 1) % len] := a[i];
    a[i] := temp;
    i := i + 1;
  }

  //assert forall j :: i < j < len ==> a[j] == old(a[(j + 1) % len]);
}
// invariant is too weak.
//# 2 pt
*/

//Problem03
// Ghost predicate to represent a sorted sequence
ghost predicate sorted(a: seq<int>)
{
  // For all indices i and j such that 0 ≤ i < j < |a|, the elements are in non-decreasing order
  ∀ i, j | 0 ≤ i < j < |a| :: a[i] ≤ a[j]
}

method InsertionSort(a: array<int>)
  modifies a
  requires a.Length ≥ 2
  ensures sorted(a[..])
  //ensures multiset(a[..]) == multiset(old(a[..]))
{
  var x := 1;
  while x < a.Length
    invariant 1 ≤ x ≤ a.Length;
    invariant sorted(a[..x]);
    //invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var i := x;   //# comments, please !!
    var d := x;   //# comments, please !!

    x := x + 1;

    var temp := a[i];  // Save the value of the element to be inserted

    while d >= 1 && a[d - 1] > temp
      invariant 0 ≤ d ≤ i + 1;
      invariant sorted(a[..i+1]);  // Elements before position i are sorted
      invariant forall j | 0 ≤ j < d - 1 :: a[j] ≤ a[j + 1];  // Elements outside position d are in non-decreasing order
      //nvariant a[..d] == a[..d] - a[d - 1] + a[d];  // The element a[d-1] is temporarily removed from the sequence
      //invariant multiset(a[..]) == multiset(old(a[..]))
    {
      a[d] := a[d - 1];  // Copy the next element into place
      d := d - 1;
    }

    a[d] := temp;  // Write the saved value into place
  }
}

//# There is no operation "-" defined on sequences. 
//# 3 pt


//# 4+2+3 = 9  pts

method InsertionSort2(a: array<int>)
  modifies a
  requires a.Length ≥ 2
  ensures sorted(a[..])
  //ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := 1;
  while i < a.Length
    invariant 1 ≤ i ≤ a.Length;
    invariant sorted(a[..i]);
    //invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if(a[i]<a[i-1]){
      var temp := a[j];







    }
    var i := x;   //# comments, please !!
    var d := x;   //# comments, please !!

    x := x + 1;

    var temp := a[i];  // Save the value of the element to be inserted

    while d >= 1 && a[d - 1] > temp
      invariant 0 ≤ d ≤ i + 1;
      invariant sorted(a[..i+1]);  // Elements before position i are sorted
      invariant forall j | 0 ≤ j < d - 1 :: a[j] ≤ a[j + 1];  // Elements outside position d are in non-decreasing order
      //nvariant a[..d] == a[..d] - a[d - 1] + a[d];  // The element a[d-1] is temporarily removed from the sequence
      //invariant multiset(a[..]) == multiset(old(a[..]))
    {
      a[d] := a[d - 1];  // Copy the next element into place
      d := d - 1;
    }

    a[d] := temp;  // Write the saved value into place
  }
}

