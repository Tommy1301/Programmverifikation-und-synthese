// ****************************************************************************************
//                              DafnyIntro.dfy
// ****************************************************************************************
// Here we use methods to simulate Hoare triples

// Note that a Hoare triple 
//     {P} Cmd {Q}
// is meaning that 
// if we start the command Cmd in a state where the precondition P is satisfied
// and if then Cmd terminates, then at the end the postcondition Q will be true 

// For the time being you should ignore the first two lines in the following 
// examples. Just concentrate on the lines beginning with 
// assume and ending with assert. We shall discuss that in detail, later.
// Thus in the following examples 
//      assume P
//         Cmd
//      assert Q
// simulates our Hoare triples.

method swapVars(A:int,B:int)			//swapping integer variables 
{ var x,y := *,*;

  assume x == A && y == B;     //pre

	  var temp := x;		   // Body of program
	         x := y;
	         y := temp;

  assert x == B && y == A;    //post

}

// The same with variables of arbitrary (generic) type T:

method swapTVars<T>(A:T,B:T)		
{ var x:T, y:T := A,B;

  assume x == A && y == B;     //pre

	  var temp := x;		   // Deklaration of variable temp is part of Cmd	
	         x := y;
	         y := temp;

  assert x == B && y == A;    //post
}

// For integer variables there are some cute tricks for 
// exchanging the content of variables x and y without 
// requiring an extra variable such as temp above:

method swapIntVars1(A:int,B:int)
{	var   x,y:=*,*;		   // for arbitrary x,y:int 

	assume x == A && y == B;							

	y := x + y;			
	x := y - x;
	y := y - x;

	assert x == B && y == A;
}

// or like so:

method swapIntVars2(A:int,B:int)
{	var   x,y:=*,*;		   // for all x,y:int  

	assume x == A && y == B;
	
	x := x - y;
	y := x + y;
	x := y - x;

	assert x == B && y == A;
}

// the following does not work
// we interchanged the 1st and 3rd line	

method swapIntVars3(A:int,B:int)
{	var   x,y:=*,*;		   // for all x,y:int    
	
	assume x == A && y == B; 	// pre						

	x := y - x;					
	y := x + y;			
	x := x - y;

//	assert x == B && y == A;	    // uncomment to see that this does not work !!!	
	assert x == -B && y == 2*B-A;	// rather Dafny says that this is true
	                                // can you prove this by hand ???	
}

// Swapping bitvectors is even easier 
// we only need to use the xor-Operation "^" three times:

method swapBitVecs(A:bv8,B:bv8)
{   var x,y := *,*;           

	assume x == A &&  y == B;							

	x  := x ^ y;		// exclusive or 
	y  := x ^ y;		//  on bitvectors
	x  := x ^ y;		//
	
	assert x == B && y == A;
}

// Dafny has simultaneous assignment, so swapping 
// could in fact be done very trivially: 

method swapTrivial(A:int,B:int)
{	var   x,y:=*,*;		   // for all x,y:int  

	assume x == A && y == B;							
	  x,y  := y, x;
	assert x == B && y == A;
}

// ---------------------------------------------
//          Swapping Array Entries 
// ---------------------------------------------
// Swapping array entries is quite different ...

// Here everything still looks normal 

method swapX(a:array<int>,i:int,j:int)
modifies a;                 // ignore this for now
requires 0 <= i < a.Length; // i must be valid index
requires 0 <= j < a.Length; // j must be valid index

ensures a[i] == old(a[j]) && a[j] == old(a[i])
{
  var temp := a[j];
      a[j] := a[i];
      a[i] := temp;
}

// But in order to apply the previous tricks 
// Dafny reminds us of the extra condition i≠j

method swapY(a:array<int>,i:int,j:int)
modifies a;

requires 0 <=  i < a.Length;
requires 0 <= j < a.Length;
requires i ≠ j;                    // this is needed !! Why ??

// a[i]  und a[j]  are switched:

ensures (a[i] == old(a[j]) ∧ a[j] == old(a[i]))

// alle anderen Einträge bleiben gleich:   
ensures forall k :: 0 <= k < a.Length &&  k != i && k != j  ==>  a[k] == old(a[k]) 
{
   a[j] := a[i] + a[j];
   a[i] := a[j] - a[i];
   a[j] := a[j] - a[i];
} 

// The following specification is stronger
// It not only states that a[i] and a[j]  are switched,  
// but also that all other entries are preserved 

method swapZ(a:array<int>,i:int,j:int)
modifies a;

// The following precondition combines stating that
// i and j are valid idices and i != j:
requires 0 <= i < j < a.Length || 0 <= j < i < a.Length

//The postcondition states that a[i] and a[j] are swapped:
ensures a[i] == old(a[j]) && a[j] == old(a[i])

// and all other entries remain unchanged:
ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k]) 

{
  a[i] := a[i] - a[j];
  a[j] := a[i] + a[j];
  a[i] := a[j] - a[i];
}
