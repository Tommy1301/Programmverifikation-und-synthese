//problem 01
//problem 02

method rotateLeft<T>(a: array<T>)
  modifies a
  requires a.Length > 0
{
  var len := a.Length;
  var i := 0;

  while (i < len)
    invariant 0 <= i <= len
    invariant  multiset(a[..]) == multiset(old(a[..]))
  {
    var temp := a[(i + 1) % len];
    a[(i + 1) % len] := a[i];
    a[i] := temp;
    i := i + 1;
  }
}


//Problem03
// Ghost predicate to represent a sorted sequence
ghost predicate sorted(a:seq<int>)
{∀ i,j | 0 ≤  i < j  < |a| :: a[i] ≤ a[j] }

method InsertionSort(a:array<int>)
  modifies a
  requires a.Length ≥ 2
  ensures sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var x := 1;
  while x < a.Length
    invariant 1 ≤ x ≤ a.Length;
    invariant sorted(a[..x]);
    invariant multiset(a[..]) == multiset(old(a[..]))
  {


    var i := x;
    var d := x;

    x := x + 1;

    var temp := a[i];  // Save the value of the element to be inserted

    while d >= 1 && a[d - 1] > temp
      invariant 0 ≤ d ≤ i + 1;
      invariant forall i, j | 0 ≤ i < j < d :: a[i] ≤ a[j];  // Elements before position d are sorted
    {
      a[d] := a[d - 1];  // Copy the next element into place
      d := d - 1;
    }
    a[d] := temp;  // Write the saved value into place
  
  }
}







