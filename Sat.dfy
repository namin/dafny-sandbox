// A Very Small SAT Solver in Dafny
// https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html
// translated from the original Haskell mostly by ChatGPT
// for ideas on what to prove, see this old port to Coq here: https://github.com/acorrenson/SATurne
// see also my older DPLL work based on Adam's Chlipala textbook exercise: https://github.com/namin/coq-sandbox/blob/master/Dpll.v

// translatio from Haskell
type Literal = int
type Clause = seq<Literal>
type Problem = seq<Clause>
type Assignment = seq<Literal>

datatype SolveResult =
  | Result(assignments: seq<Assignment>)
  | FuelExhausted

/*
-- propagating the choice of the value of a literal to the rest of the problem, reducing the problem to a simpler one
propagate :: Literal -> Problem -> Problem
propagate l p = [ filter (/= negate l) c | c <- p, l `notElem` c ]
*/
function propagate(l: Literal, p: Problem): Problem
{
  if p == [] then [] // Base case: empty problem remains empty
  else
    var c := p[0];
    var rest := p[1..];
    
    if l in c then propagate(l, rest)
    else [remove(c, -l)] + propagate(l, rest)
}
function remove(c: Clause, l: Literal): Clause
{
  if c == [] then []
  else
    var x := c[0];
    var rest := c[1..];
    if x == l then remove(rest, l)
    else [x] + remove(rest, l)
}

/*
-- a simple backtracking search where we propagate the choice of the literal to the rest of the problem and check the smaller problem
solve :: Problem -> [Assignment]
solve []    = [[]]
solve (c:p) = do
  (l:c) <- [c]
  ([l:as | as <- solve (propagate l p)] ++ [negate l:as | as <- solve (propagate (negate l) (c:p))])
*/
// Solver with fuel parameter
function solve(fuel: nat, p: Problem): SolveResult
{
  if p == [] then Result([ [] ]) // Base case: return an empty assignment
  else
    var c := p[0];
    var rest := p[1..];

    if c == [] then Result([]) // If there's an empty clause, no solution
    else
      if fuel == 0 then FuelExhausted
      else
        var l := c[0];

        match (solve(fuel - 1, propagate(l, rest)), solve(fuel - 1, propagate(-l, p)))
        {
          case (FuelExhausted, _) => FuelExhausted
          case (_, FuelExhausted) => FuelExhausted
          case (Result(posSolve), Result(negSolve)) =>
            Result(appendAssignments(l, posSolve) + appendAssignments(-l, negSolve))
        }
}
// Helper function to append a literal to each assignment
function appendAssignments(l: Literal, assignments: seq<Assignment>): seq<Assignment>
{
  if assignments == [] then []
  else
    var first := assignments[0];
    var rest := assignments[1..];

    [[l] + first] + appendAssignments(l, rest)
}

// end-to-end solve
method Main()
{
  var problem1 := [[1, -2], [-1, 2], [2, 3], [-3]];
  var result1 := solve(10, problem1); // Use sufficient fuel

  match result1
  {
    case FuelExhausted => print "Fuel exhausted\n";
    case Result(assignments) =>
      print "Solutions: ", assignments, "\n";
  }

  var problem2 := [[1], [-1]]; // UNSAT (contradiction)
  var result2 := solve(10, problem2);

  match result2
  {
    case FuelExhausted => print "Fuel exhausted\n";
    case Result(assignments) =>
      print "No solutions found: ", assignments, "\n";
  }
}

// properties to verify, suggested by ChatGPT

// proved by Claude, with some hints from me
lemma solveTerminatesHelper(p: Problem, fuel: nat)
  requires fuel >= problemSize(p) * 2
  ensures solve(fuel, p).Result?
  decreases problemSize(p)
{
  if p == [] {
    assert solve(fuel, p) == Result([[]]);
  } else if p[0] == [] {
    assert solve(fuel, p) == Result([]);
  } else {
    var l := p[0][0];
    var rest := p[1..];
    
    propagateReduces(l, rest);
    propagateReduces(-l, p);

    assert problemSize(propagate(l, rest)) <= problemSize(rest);
    assert problemSize(propagate(l, rest)) < problemSize(p);

    assert problemSize(propagate(-l, p)) <= problemSize(p);
    restReduces(p);
    assert problemSize(rest) < problemSize(p);
    assert problemSize(propagate(-l, p)) < problemSize(p);

    var newFuel := fuel - 1;
    assert newFuel >= problemSize(propagate(l, rest)) * 2;
    assert newFuel >= problemSize(propagate(-l, p)) * 2;

    solveTerminatesHelper(propagate(l, rest), newFuel);
    solveTerminatesHelper(propagate(-l, p), newFuel);
  }
}
function problemSize(p: Problem): nat
{
  if p == [] then 0
  else |p[0]| + problemSize(p[1..])
}
lemma removeReduces(c: Clause, l: Literal)
  ensures |remove(c, l)| <= |c|
  ensures l in c ==> |remove(c, l)| < |c|
{
  if c != [] {
    var rest := c[1..];
    if c[0] == l {
      removeReduces(rest, l);
      assert |remove(c, l)| == |remove(rest, l)|;
      assert |remove(c, l)| < |c|;
    } else {
      removeReduces(rest, l);
      assert |remove(c, l)| == 1 + |remove(rest, l)|;
    }
  }
}
lemma restReduces(p: Problem)
  requires p != [] && p[0] != []
  ensures problemSize(p[1..]) < problemSize(p)
{
  assert problemSize(p) == |p[0]| + problemSize(p[1..]);
  assert |p[0]| > 0;  // since p[0] != []
}
lemma propagateReduces(l: Literal, p: Problem)
  ensures problemSize(propagate(l, p)) <= problemSize(p)
  ensures p != [] && l in p[0] ==> problemSize(propagate(l, p)) < problemSize(p)
  ensures p != [] && -l in p[0] ==> problemSize(propagate(l, p)) < problemSize(p)
{
  if p != [] {
    var c := p[0];
    var rest := p[1..];
    
    if l in c {
      propagateReduces(l, rest);
      assert problemSize(propagate(l, p)) == problemSize(propagate(l, rest));
      assert problemSize(propagate(l, rest)) <= problemSize(rest);
      assert problemSize(p) == |c| + problemSize(rest);
      assert |c| > 0;  // since it contains l
      assert problemSize(propagate(l, p)) < problemSize(p);
    } else {
      removeReduces(c, -l);
      propagateReduces(l, rest);
      assert |remove(c, -l)| <= |c|;
      if -l in c {
        assert |remove(c, -l)| < |c|;
        assert problemSize(propagate(l, p)) < problemSize(p);
      }
    }
  }
}

/*
lemma solveSound(fuel: nat, p: Problem, asg: Assignment)
  requires match solve(fuel, p)
           case Result(assignments) => asg in assignments
           case FuelExhausted => false
  ensures satisfies(p, asg)
{
}
*/
function satisfies(p: Problem, asg: Assignment): bool
{
  forall c: Clause :: c in p ==> exists l: Literal :: l in asg && l in c
}
// Helper lemma 1: If an assignment satisfies a propagated problem and contains the propagated literal,
// then it satisfies the original problem
lemma propagateSoundness(l: Literal, p: Problem, asg: Assignment)
  requires l in asg  // assignment contains the literal we propagated
  requires satisfies(propagate(l, p), asg)
  ensures satisfies(p, asg)
{
  forall c | c in p 
  ensures exists lit :: lit in c && lit in asg
  {
    if l !in c {
      propagateContains(l, p, c);
      var lit :| lit in remove(c, -l) && lit in asg;
      removeContains(c, -l, lit);
    }
  }
}
lemma removeContains(c: Clause, l: Literal, x: Literal)
  requires x in remove(c, l)
  ensures x in c && x != l
{
  if c != [] {
    var rest := c[1..];
    if c[0] == l {
      removeContains(rest, l, x);
    } else {
      if x == c[0] {
        assert x in c;
        assert x != l;  // since c[0] != l
      } else {
        removeContains(rest, l, x);
      }
    }
  }
}
lemma propagateContains(l: Literal, p: Problem, c: Clause)
  requires c in p
  requires l !in c
  ensures remove(c, -l) in propagate(l, p)
  decreases p
{
  if p != [] {
    if c == p[0] {
      // Base case: c is the first clause
      assert remove(c, -l) == propagate(l, p)[0];
    } else {
      // Recursive case: c is in the rest of p
      propagateContains(l, p[1..], c);
    }
  }
}

/*
// Helper lemma 2: Appending a literal preserves soundness for a specific assignment
lemma appendAssignmentsSoundness(l: Literal, asg: Assignment, p: Problem) 
  requires satisfies(p, asg)
  ensures satisfies(p, [l] + asg)
*/

/*
lemma solveComplete(p: Problem)
  requires exists asg: Assignment :: satisfies(p, asg)
  ensures match solve(10, p)
          case Result(assignments) => exists asg: Assignment :: asg in assignments && satisfies(p, asg)
          case FuelExhausted => true
{
  // TODO: Proof
}
*/


