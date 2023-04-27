// ****************************************************************************************
//                              DafnyIntro.dfy
// ****************************************************************************************
//
//  Method calls in Dafny
//

// In a method definition:

// preconditions are assumed / may be used
// postconditions must be proved 

method max(x:int,y:int) returns (m:int)
  ensures m ≥ x && m ≥ y
  ensures m == x || m == y

// without a body the above max is only a specification.
// Before we compile the program, the body must be supplied

// We can already use max to implement and verify functions
// using it. The caller (here: min) of a method (here:max) 
// will only rely on the specification of the called function
// anyway: 

// In a method call, the preconditions of the called method (here: max) 
// must be verified, the postconditions of the called method may be used.

method min(x:int,y:int) returns (m:int)
ensures m ≤ x && m ≤ y
ensures m == x || m == y
{
  m :=  max(-x,-y);       // method call always assigns to variable
  m := -m;
}

// Notice that we cannot simply write : 
//       m := -max(-x,-y);
// This is because a method call in Dafny can only be written
// as an assignment to a variable, here: m := max(-x,-y);
// Then we can do whatever we want with this variable.  


// By the way - here is a possible implementation for a maximum method: 

method maximum(x:int,y:int) returns (m:int)					// if-then-else
  ensures m >= x && m >= y
	ensures m == x || m == y
{
	  if (x > y) { m := x; }	
	  else       { m := y; }	
}

