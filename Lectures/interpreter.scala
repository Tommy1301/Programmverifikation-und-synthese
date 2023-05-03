/* --------------------------------------------------------------

  Semantics and evaluation of simple IMP programs
  as discussed in my lectures on program verification

  H.Peter Gumm (g...@mathematik.uni-marburg.de) 

------------------------------------------------------------------

  This is a Scala-Program which can be evaluated and changed
  without needing to install Scala. Simply go to
  	   https://scastie.scala-lang.org
  Copy the contents of this file into the editor and press "Run"
  Scastie should be set into "Worksheet mode" (see the menu on top
  of the Scastie page)

===========================================================
                  S Y N T A X   of IMP
===========================================================

We begin by representing Terms, Boolean expressions, and Programs

The Scala keywords "case class" generate a class which allows 
pattern matching on its objects. To see why this is really helpful,
scroll down to the definitions of "eval" or "execute" where the 
"match" - statement works by pattern matching.
*/

// -----------------------------------------------
//   Arithmetical Terms
// -----------------------------------------------

sealed abstract class Term

case class Const(c: Int) extends Term
case class Var(name: String) extends Term
case class Neg(t: Term) extends Term
case class Sum(t1: Term, t2: Term) extends Term
case class Diff(t1: Term, t2: Term) extends Term
case class Prod(t1: Term, t2: Term) extends Term
case class Div(t1: Term, t2: Term) extends Term
case class Mod(t1: Term, t2: Term) extends Term

// -----------------------------------------------
// Boolean Expressions
// -----------------------------------------------

sealed abstract class BExpr

// Boolean Constants
case object T extends BExpr  // constant T (true)
case object F extends BExpr  // constant F (false)

// Atomic formulae
case class Eq(t1: Term, t2: Term) extends BExpr
case class Lt(t1: Term, t2: Term) extends BExpr
case class Leq(t1: Term, t2: Term) extends BExpr
case class Gt(t1: Term, t2: Term) extends BExpr
case class Geq(t1: Term, t2: Term) extends BExpr

// Boolean combinations
case class Not(b: BExpr) extends BExpr
case class Dis(b1: BExpr, b2: BExpr) extends BExpr
case class Con(b1: BExpr, b2: BExpr) extends BExpr
case class Imp(b1: BExpr, b2: BExpr) extends BExpr
case class Iff(b1: BExpr, b2: BExpr) extends BExpr


// -----------------------------------------------
// Commands (  same as "Programs" )
// -----------------------------------------------

sealed abstract class Cmd

case class Ass(name: String, t: Term) extends Cmd
case object Skip extends Cmd
case class Then(c1: Cmd, c2: Cmd) extends Cmd
case class Ite(cond: BExpr, c1: Cmd, c2: Cmd) extends Cmd
case class While(cond: BExpr, c: Cmd) extends Cmd

/* 
   This concludes the representation of Terms, Boolean expressions, 
   and Programs. We next turn to semantics = meaning

 ===========================================================
               S E M A N T I C S   of IMP
 ===========================================================

   For this we need the concept of "state"

   A state is an correspondence of variables to values.
   Here we consider only Programs working on integers.
   In particular, every variable has implicitly type Integer,
   so a state is a map associating a variable names with
   integer values.

   ( In functional programming states are known as "environments".
     There they typically are never changed. )

   In Scala we can use the data type "Map"

 */

type State = Map[String, Int]

// Here is an example of a map:
val s0: State = Map("x" -> 17, "y" -> 9)

// s1 updates s0 by overriding the value of y and adding a value for z.
val s1: State = s0 + ("y" -> 42, "z" -> 3)

/*

   Calculating the value of a syntactical object is often called "evaluation".
   The value of a term or a Boolean expression depends on the current state.
   For instance:
      x+y has value 26 in state s0
      x+y has value 59 in state s1

// ------------------------------------------
// Evaluation of terms
// ------------------------------------------
*/

def eval(t: Term, e: State): Int = 
t match   													// try matching t to one of the follow. patterns
  case Const(c)     => c
  case Var(name)    => e(name) 			// here we lookup name in state e
  case Neg(t1)      => -eval(t1, e)
  case Sum(t1, t2)  => eval(t1, e) + eval(t2, e)
  case Diff(t1, t2) => eval(t1, e) - eval(t2, e)
  case Prod(t1, t2) => eval(t1, e) * eval(t2, e)
  case Div(t1, t2)  => eval(t1, e) / eval(t2, e)
  case Mod(t1, t2)  => eval(t1, e) % eval(t2, e)

// ------------------------------------------
// Evaluation of Boolean expressions
// ------------------------------------------

def eval(b: BExpr, e: State): Boolean = 
b match
  case T => true
  case F => false

  case Eq(t1, t2)  => (eval(t1, e) == eval(t2, e))
  case Lt(t1, t2)  => (eval(t1, e) < eval(t2, e))
  case Leq(t1, t2) => eval(t1, e) <= eval(t2, e)
  case Gt(t1, t2)  => eval(t1, e) > eval(t2, e)
  case Geq(t1, t2) => eval(t1, e) >= eval(t2, e)

  case Not(b)      => !eval(b, e)
  case Dis(b1, b2) => eval(b1, e) || eval(b2, e)
  case Con(b1, b2) => eval(b1, e) && eval(b2, e)
  case Imp(b1, b2) => !eval(b1, e) || eval(b2, e)
  case Iff(b1, b2) => eval(b1, e) || eval(b2, e)

// -------------------------------------------------
//         Examples
// -------------------------------------------------

val s2: State = Map("x" -> 17, "y" -> 42, "sum" -> 99, "n" -> 10)

// t := 3*x+y :

val t: Term = Sum(Prod(Const(3), Var("x")), Var("y"))

// b := (3*x+y < sum)  && n = 10 :

val b: BExpr = Con(
  Lt(t, Var("sum")),
  Eq(Var("n"), Const(10))
)

println(
  " The value of term 3*x+1, represented as "
    + t
    + "\n in state "
    + s2
    + "\n is "
    + eval(t, s2)
    + "\n"
);

println(
  " The value of Boolean expression  (3*x+y < sum)  && n = 10, \n represented as "
    + b
    + "\n in state "
    + s2
    + "\n is "
    + eval(b, s2)
    + "\n"
);

// -----------  end of example ------

/*
// ------------------------------------------
// Execution of programs
// ------------------------------------------

	IMPerative Programs change states. 
  Here we implement them functionally, so they input an starting state 
  and return a final state.

  To "execute" a program (=command) c,  we start it in a state e
  and obtain a new/final state, assuming that the program terminates.
  Notice that the "While" case is recursive so it allows nonterminating programs
 */

def execute(c: Cmd, e: State): State = 
c match
  case Skip                   => e
  case Ass(name, t)           => e + (name -> eval(t, e))
  case Then(c1: Cmd, c2: Cmd) => execute(c2, execute(c1, e))
  case Ite(cond, c1, c2) =>
    if (eval(cond, e)) execute(c1, e) else execute(c2, e)
  case While(cond, c) =>
    if (eval(cond, e)) execute(While(cond, c), execute(c, e)) else e

// ---------- Example ---------------------------

// We start in the following state s3:

val s3: State = Map("x" -> 17, "y" -> 42, "z" -> 99)


// and execute program    { y := x + 5 ; y := x+y; x := x+1}

// which is represented by  :

val prog = Then(
  Ass("y", Sum(Var("x"), Const(5))),
  Then(
    Ass("y", Sum(Var("x"), Var("y"))),
    Ass("x", Sum(Var("x"), Const(1)))
  )
)

println(" Starting state : " + s3)
println(" Program        :  { y := x + 5 ; y := x+y; x := x+1}")
println(" represented as : " + prog)
println(" Ending State   : " + execute(prog, s0) + "\n")
