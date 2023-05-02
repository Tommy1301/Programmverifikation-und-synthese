// ****************************************************************************************
//                              DafnyIntro.dfy
// ****************************************************************************************

/* 
 A *method specification* typically consists of
    + a header consisting of
      - the keyword "method"
      - a method name
      - a list of typed variables (the parameter list)
      - optionally: the keyword "returns" with
        a list of typed result variables (the result list) 
	  + preconditions
      - typically involving the parameter variables
	  + postconditions
      - typically involving parameters and output variables 
  
  Nothing needs to be proved !!
*/
// Example: 

  method sumMax(x:int,y:nat) returns (s:int,m:nat)
  requires x >= 0 && y > 0
  ensures s == x+y;
  ensures m >= x && m >= y && (m == x || m == y)

/* A *method definition* typically consists of:
	+ a method specification AND 
  + an implication 

  It is assumed that by the end of execution of the body
  + the method's result has been assigned to the result variables.

  + It must!! be proved that, 
   - assuming the preconditions, 
   - the method's body guarantes the postcondition 
*/

method SumMax'(x:int,y:nat) returns (s:int,m:nat)
requires x >= 0 && y > 0
ensures s == x+y;
ensures m >= x && m >= y && (m == x || m == y)
{
  s := x+y;
  m := if x < y then y else x;  //if-else-expression
}

/* In the above and in following example, 
   the proof that the implementation 
   is correct will be done by Dafny. 
   No further user intervention is required.
   + The green line at the left margin  
     signals that the proof was successful.
*/

method maximum(x:int,y:int) returns (m:int)
  //requires x > 0 && y > 0        // actually superfluous    
  ensures m ≥ x && m ≥ y         // important 
  ensures m == x || m == y       // important
{   
  if x < y { m := y; }           // implementation 
  else     { m := x; }

} 

/* A *method call* requires
  +  a list of variables matching the method's output variables  
  +  the call itself with formal parameters replaced by 
     expressions of matching type
  +  an assignment of the method call to the receiving variables      
*/


/*   In a *method call* (of "maximum")
   preconditions of the called method must be verified
   postconditions of the called methode may be use
   Of the called method only its specification (Pre/Post) is known,
   not its implementation

*/

method MaxSumMax() returns (msm:int)
{
  var u:int,v:nat;
      u,v := SumMax'(3,17);
      msm := maximum(u,v);
} 

method minimum(x:int,y:int) returns (m:int)
requires x < 0 && y < 0     // necessary, due to the precondition in "maximum"
ensures m ≤ x && m ≤ y
ensures m == x || m == y
{                            // here u is the receiving variable  
  var u :=  maximum(-x,-y);  // called method assigned to receiving variable
  m := -u;                   // method's output variable receives result 
}

method calcAbs(x:int) returns (a:nat) // calculate absolute value
ensures a ≥ 0;
ensures a == x || a == -x
{
  if x < 0 { a := -x; } else { a := x; }
}
