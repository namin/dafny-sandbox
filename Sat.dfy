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
  if fuel == 0 then FuelExhausted
  else if p == [] then Result([ [] ]) // Base case: return an empty assignment
  else
    var c := p[0];
    var rest := p[1..];

    if c == [] then Result([]) // If there's an empty clause, no solution
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

lemma solveSound(p: Problem)
  ensures match solve(10, p)
          case Result(assignments) => forall asg: Assignment :: asg in assignments ==> satisfies(p, asg)
          case FuelExhausted => true
{
  // TODO: Proof
}
function satisfies(p: Problem, asg: Assignment): bool
{
  forall c: Clause :: c in p ==> exists l: Literal :: l in asg && l in c
}

lemma solveComplete(p: Problem)
  requires exists asg: Assignment :: satisfies(p, asg)
  ensures match solve(10, p)
          case Result(assignments) => exists asg: Assignment :: asg in assignments && satisfies(p, asg)
          case FuelExhausted => true
{
  // TODO: Proof
}

lemma solveTerminates(p: Problem)
  ensures exists fuel: nat :: solve(fuel, p) != FuelExhausted
{
  // TODO: Proof
}