// ****************************************************************************************
//                              DafnyIntro.dfy
// ****************************************************************************************


/* Methods are imperative programming features
   They work by modifying the "state" given by 
   the current content of the variables.
   The following method calculates the absolute 
   value of an integer and assigns the valu to output variable a
 */

method calcAbs(x:int) returns (a:nat) // calculate absolute value
ensures a ≥ 0;
ensures a == x || a == -x
{
  if x < 0 { a := -x; } else { a := x; }
}


/* Functions serve to aid specification but are also compiled
   Functions have their own syntax:

     function (parameters):type 
       preconditions  - optional
       postconditions - optional
      { Expr }        - one single expression - optional!!
*/

/* The following function also calculates the absolute value. 
   It works be directly calculating an expression representing the
   desired value using an if-then-else expression.
   Note the difference between the if-else-statement from calcAbs 
   and the if-then-else expression in abs below.  
    
   Also note that in Functions no assignments, semicola
   are neither needed nor allowed.
*/  

function abs(x:int):int 
ensures abs(x) >= 0
{ if x < 0 then -x else x }

function square(x:int):int
ensures abs(square(x))  == square(x)
{ x*x }

/* Functions are useful to abbreviate pre- and postconditions */

method squareIt(x:int) returns (s:int)
ensures s == square(x-1)+2*x-1
{
   s := (x-1)*x + x;
} 

/* If they are only needed for expressing pre- and post- conditions
   and not for the actual programs, then they may be declared as "ghost"
*/

// -----------------------------------------------------------------
//               Predicates
// -----------------------------------------------------------------

/* Predicates are boolean functions

// Let us try to specify and detect the/an integer-midpoint between two integers.
*/

ghost predicate between(x:int,m:int,y:int)
{  
  x ≤ m ≤ y || y ≤ m ≤ x      // this is the body 
}     // note that you may use chains of (in-)equalities

/* the following method uses the prediate 'between' in its specification:
*/

method FindMidpoint(x:int,y:int) returns (m:int)
ensures between(x,m,y)
ensures 0 ≤ abs(abs(m-x) - abs(m-y)) ≤ 1 
{
   m := (x+y)/2;
}

// Exercise 1:: Find a better *specification* of Midpoint and prove it correct 

predicate halfway(x:int,m:int,y:int)
{ 0 ≤ abs(abs(m-x)-abs(m-y)) ≤ 1  }

method max(x:int,y:int) returns (mx:int) 
ensures x ≤ mx && y ≤ mx
ensures mx == x || mx == y
{
  if (x ≤ y) { mx := y; } else { mx := x; }
}

method min(x:int,y:int) returns (mn:int) 
{
  if (x ≤ y) { mn:=x; }  else { mn := y; }
}

