// A Very Small SAT Solver in Dafny
// https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html
// translated from the original Haskell
// for ideas on what to prove, see this old port to Coq here: https://github.com/acorrenson/SATurne
// see also my older DPLL work based on Adam's Chlipala textbook exercise: https://github.com/namin/coq-sandbox/blob/master/Dpll.v
//
// used LLMs inculding ChatGPT 4o, (Cursor) Claude Sonnet 3.5 and more recently Claude Code (Opus)
// for initial translation, for stating high-level properties, and for the decomposition into lemmas and their proofs

// translation from Haskell
datatype Literal = Pos(n: nat) | Neg(n: nat)
function negate(l: Literal): Literal {
  match l {
    case Pos(n) => Neg(n)
    case Neg(n) => Pos(n)
  }
}
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
    else [remove(c, negate(l))] + propagate(l, rest)
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

        match (solve(fuel - 1, propagate(l, rest)), solve(fuel - 1, propagate(negate(l), p)))
        {
          case (FuelExhausted, _) => FuelExhausted
          case (_, FuelExhausted) => FuelExhausted
          case (Result(posSolve), Result(negSolve)) =>
            Result(appendAssignments(l, posSolve) + appendAssignments(negate(l), negSolve))
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
method MainExamples()
{
  var problem1 := [[Pos(1), Neg(2)], [Neg(1), Pos(2)], [Pos(2), Pos(3)], [Neg(3)]];
  var result1 := solve(10, problem1); // Use sufficient fuel

  match result1
  {
    case FuelExhausted => print "Fuel exhausted\n";
    case Result(assignments) =>
      print "Solutions: ", assignments, "\n";
  }

  var problem2 := [[Pos(1)], [Neg(1)]]; // UNSAT (contradiction)
  var result2 := solve(10, problem2);

  match result2
  {
    case FuelExhausted => print "Fuel exhausted\n";
    case Result(assignments) =>
      print "No solutions found: ", assignments, "\n";
  }
}

lemma solveTerminates(p: Problem)
  ensures solve(problemSize(p) * 2, p).Result?
{
  solveTerminatesHelper(p, problemSize(p) * 2);
}
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
    propagateReduces(negate(l), p);

    assert problemSize(propagate(l, rest)) <= problemSize(rest);
    assert problemSize(propagate(l, rest)) < problemSize(p);

    assert problemSize(propagate(negate(l), p)) <= problemSize(p);
    restReduces(p);
    assert problemSize(rest) < problemSize(p);
    assert problemSize(propagate(negate(l), p)) < problemSize(p);

    var newFuel := fuel - 1;
    assert newFuel >= problemSize(propagate(l, rest)) * 2;
    assert newFuel >= problemSize(propagate(negate(l), p)) * 2;

    solveTerminatesHelper(propagate(l, rest), newFuel);
    solveTerminatesHelper(propagate(negate(l), p), newFuel);
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
  ensures p != [] && negate(l) in p[0] ==> problemSize(propagate(l, p)) < problemSize(p)
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
      removeReduces(c, negate(l));
      propagateReduces(l, rest);
      assert |remove(c, negate(l))| <= |c|;
      if negate(l) in c {
        assert |remove(c, negate(l))| < |c|;
        assert problemSize(propagate(l, p)) < problemSize(p);
      }
    }
  }
}

// ## Consistent
/*
lemma solveConsistent(fuel: nat, p: Problem, asg: Assignment)
  requires match solve(fuel, p)
           case Result(assignments) => asg in assignments
           case FuelExhausted => false
  ensures isConsistent(asg)
*/
predicate isConsistent(asg: Assignment)
{
  forall l :: l in asg ==> negate(l) !in asg
}

// ## Sound
lemma solveSound(fuel: nat, p: Problem, asg: Assignment)
  requires match solve(fuel, p)
           case Result(assignments) => asg in assignments
           case FuelExhausted => false
  ensures satisfies(p, asg)
  decreases fuel
{
  if p == [] {
    assert solve(fuel, p) == Result([[]]);
    assert asg == [];
  } else if p[0] == [] {
    assert solve(fuel, p) == Result([]);
    assert false; // from requires since no assignments
  } else if fuel == 0 {
    assert solve(fuel, p) == FuelExhausted;
    assert false; // from requires
  } else {
    var l := p[0][0];
    var rest := p[1..];
    
    var pos_result := solve(fuel - 1, propagate(l, rest));
    var neg_result := solve(fuel - 1, propagate(negate(l), p));
    match pos_result {
      case Result(pos_solns) => {
        match neg_result {
          case Result(neg_solns) => {
            var all_solns := appendAssignments(l, pos_solns) + appendAssignments(negate(l), neg_solns);
            assert asg in all_solns;  // from requires
            
            if asg in appendAssignments(l, pos_solns) {
              // Case 1: asg came from positive branch
              appendAssignmentsContains(l, pos_solns, asg);
              var pos_asg :| asg == [l] + pos_asg && pos_asg in pos_solns;
              
              // Use recursive soundness on pos_asg
              solveSound(fuel-1, propagate(l, rest), pos_asg);
              assert satisfies(propagate(l, rest), pos_asg);
              
              // Show l in asg using prependInSequence
              prependInSequence(l, pos_asg);
              assert l in asg;  // since asg == [l] + pos_asg
              
              // Use propagateSoundness with asg (not pos_asg)
              propagateSoundness(l, rest, asg);
              assert satisfies(rest, asg);
              
              // Now show that asg satisfies p
              forall c | c in p 
              ensures exists lit :: lit in c && lit in asg {
                if c == p[0] {
                  // First clause - l satisfies it since l in asg
                  assert l in c;  // since l == c[0]
                  assert l in asg;
                } else {
                  // Other clauses - use satisfies(rest, asg)
                  assert c in rest;
                  var lit :| lit in c && lit in asg;
                }
              }
            } else {
              // Case 2: asg came from negative branch
              appendAssignmentsContains(negate(l), neg_solns, asg);
              var neg_asg :| asg == [negate(l)] + neg_asg && neg_asg in neg_solns;
              
              // Use recursive soundness on neg_asg
              solveSound(fuel-1, propagate(negate(l), p), neg_asg);
              assert satisfies(propagate(negate(l), p), neg_asg);
              
              // Show -l in asg using prependInSequence
              prependInSequence(negate(l), neg_asg);
              assert negate(l) in asg;  // since asg == [negate(l)] + neg_asg
              
              // Use propagateSoundness with asg (not neg_asg)
              propagateSoundness(negate(l), p, asg);
              assert satisfies(p, asg);
            }
          }
          case FuelExhausted => { assert false; }
        }
      }
      case FuelExhausted => { assert false; }
    }
  }
}
function satisfies(p: Problem, asg: Assignment): bool
{
  forall c: Clause :: c in p ==> exists l: Literal :: l in asg && l in c
}

// ## Complete
// Helper: checks if an assignment assigns all variables in a problem
predicate coversAllVariables(p: Problem, asg: Assignment)
{
  forall c, lit | c in p && lit in c :: 
    lit in asg || negate(lit) in asg
}

// Lemma: propagation preserves variable coverage
lemma propagatePreservesCoverage(l: Literal, p: Problem, asg: Assignment)
  requires coversAllVariables(p, asg)
  ensures coversAllVariables(propagate(l, p), asg)
{
  forall c, lit | c in propagate(l, p) && lit in c
  ensures lit in asg || negate(lit) in asg
  {
    propagateHasOriginal(l, p, c);
    var orig_c :| orig_c in p && l !in orig_c && c == remove(orig_c, negate(l));
    removePreservesOthers(orig_c, negate(l), lit);
    if lit != negate(l) {
      assert lit in orig_c;
      assert orig_c in p;
      assert lit in asg || negate(lit) in asg;
    } else {
      // lit == negate(l) means negate(l) is in the propagated clause
      removeContains(orig_c, negate(l), lit);
      assert lit in orig_c;
      assert orig_c in p;
      assert negate(l) in asg || l in asg;
    }
  }
}

lemma solveComplete(p: Problem, sat_asg: Assignment)
  requires satisfies(p, sat_asg)
  requires isConsistent(sat_asg)
  requires coversAllVariables(p, sat_asg)  // Added requirement
  ensures match solve(problemSize(p) * 2, p)
          case Result(assignments) => (
            exists asg :: asg in assignments && satisfies(p, asg) &&
                   forall l :: l in asg ==> (l in sat_asg || negate(l) in sat_asg)
          )
          case FuelExhausted => false
  decreases problemSize(p), 1
{
  solveTerminatesHelper(p, problemSize(p) * 2);
  assert solve(problemSize(p) * 2, p).Result?;

  if p == [] {
    // Base case: empty problem
    var empty_asg: Assignment := [];
    assert empty_asg in [[]];  // from solve(p) == Result([[]])
    assert satisfies(p, empty_asg);  // vacuously true
    // Invariant holds since empty_asg is empty
  } else if p[0] == [] {
    // Impossible case - contradicts requires since empty clause can't be satisfied
    assert p[0] in p;
    assert exists l :: l in sat_asg && l in p[0];  // from satisfies(p, sat_asg)
    assert p[0] == [];  // from if condition
    assert false;  // contradiction: no literal can be in empty clause
  } else {
    var l := p[0][0];
    var rest := p[1..];

    if l in sat_asg {
      // Use helper lemma for positive branch
      solvePropagatedBranch(p, l, rest, sat_asg);
      
      // Get solution from recursive call
      var pos_result := solve(problemSize(p) * 2 - 1, propagate(l, rest));
      match pos_result {
        case Result(pos_solns) => {
          // Get solution that satisfies propagate(l, rest)
          var pos_asg :| pos_asg in pos_solns && satisfies(propagate(l, rest), pos_asg) &&
                        forall m :: m in pos_asg ==> (m in sat_asg || negate(m) in sat_asg);
          
          // Show [l] + pos_asg works
          appendAssignmentsIncludes(l, pos_solns, pos_asg);
          prependInSequence(l, pos_asg);
          assert satisfies(propagate(l, rest), pos_asg);
          propagateSoundnessWithPrefix(l, p, rest, pos_asg);

          // Show all literals come from sat_asg using forall
          forall m | m in [l] + pos_asg
          ensures m in sat_asg || negate(m) in sat_asg
          {
            if m == l {
              assert m in sat_asg;  // from if condition
            } else {
              assert m in pos_asg;  // since m in [l] + pos_asg and m != l
              assert m in sat_asg || negate(m) in sat_asg;  // from pos_asg's property
            }
          }

          // Show solution is in final result
          var neg_result := solve(problemSize(p) * 2 - 1, propagate(negate(l), p));
          match neg_result {
            case Result(neg_solns) =>
              solveReturnsResult(p, l, pos_solns, neg_solns, [l] + pos_asg);
            case FuelExhausted => assert false;
          }
        }
      }
    } else {
      // Since sat_asg satisfies p[0], get satisfying literal
      assert p[0] in p;
      var lit :| lit in sat_asg && lit in p[0];
      assert lit != l;  // since l !in sat_asg
      
      // Show we have enough fuel
      propagateReduces(negate(l), p);
      assert problemSize(propagate(negate(l), p)) < problemSize(p);
      
      // First prove sat_asg satisfies propagate(negate(l), p)
      assert l !in sat_asg;  // from else branch
      propagateSatisfactionLemma(negate(l), p, sat_asg);
      
      // Use recursive call
      propagatePreservesCoverage(negate(l), p, sat_asg);
      solveComplete(propagate(negate(l), p), sat_asg);
      
      // Connect recursive result to neg_result
      assert solve(problemSize(propagate(negate(l), p)) * 2, propagate(negate(l), p)).Result?;
      var rec_result := solve(problemSize(propagate(negate(l), p)) * 2, propagate(negate(l), p));
      assert exists asg :: asg in rec_result.assignments && 
                    satisfies(propagate(negate(l), p), asg) &&
                    forall m :: m in asg ==> (m in sat_asg || negate(m) in sat_asg);
      
      // Show we have enough fuel
      solveFuelMonotonic(propagate(negate(l), p), 
                        problemSize(propagate(negate(l), p)) * 2,
                        problemSize(p) * 2 - 1);
      
      // Get solution from recursive call
      var neg_result := solve(problemSize(p) * 2 - 1, propagate(negate(l), p));
      match neg_result {
        case Result(neg_solns) => {
          // Get solution from recursive call
          var neg_asg :| neg_asg in neg_solns && satisfies(propagate(negate(l), p), neg_asg) &&
                        forall m :: m in neg_asg ==> (m in sat_asg || negate(m) in sat_asg);
          
          // Show [negate(l)] + neg_asg works
          appendAssignmentsIncludes(negate(l), neg_solns, neg_asg);
          prependInSequence(negate(l), neg_asg);
          prependPreservesSatisfaction(negate(l), propagate(negate(l), p), neg_asg);
          propagateSoundness(negate(l), p, [negate(l)] + neg_asg);
          
          // Show all literals come from sat_asg using forall
          forall m | m in [negate(l)] + neg_asg
          ensures m in sat_asg || negate(m) in sat_asg
          {
            if m == negate(l) {
              // By coversAllVariables, since l is in p[0], either l or negate(l) is in sat_asg
              assert p[0] in p;
              assert l in p[0];  // since l == p[0][0]
              assert coversAllVariables(p, sat_asg);
              assert l in sat_asg || negate(l) in sat_asg;
              assert l !in sat_asg;  // from branch condition
              assert negate(l) in sat_asg;
              assert m == negate(l);
              assert m in sat_asg;
            } else {
              assert m in neg_asg;  // since m in [negate(l)] + neg_asg and m != negate(l)
              assert m in sat_asg || negate(m) in sat_asg;  // from neg_asg's property
            }
          }

          // Get positive branch solution
          var pos_result := solve(problemSize(p) * 2 - 1, propagate(l, rest));
          match pos_result {
            case Result(pos_solns) =>
              solveReturnsResult(p, l, pos_solns, neg_solns, [negate(l)] + neg_asg);
            case FuelExhausted => assert false;
          }
        }
        case FuelExhausted => assert false;
      }
    }
  }
}

// ## Helper Lemmas

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
      var lit :| lit in remove(c, negate(l)) && lit in asg;
      removeContains(c, negate(l), lit);
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
  ensures remove(c, negate(l)) in propagate(l, p)
  decreases p
{
  if p != [] {
    if c == p[0] {
      // Base case: c is the first clause
      assert remove(c, negate(l)) == propagate(l, p)[0];
    } else {
      // Recursive case: c is in the rest of p
      propagateContains(l, p[1..], c);
    }
  }
}

// Helper lemma 2: Appending a literal preserves soundness for a specific assignment
lemma appendAssignmentsSoundness(l: Literal, asg: Assignment, p: Problem) 
  requires satisfies(p, asg)
  ensures satisfies(p, [l] + asg)
{
  forall c | c in p 
  ensures exists lit :: lit in c && lit in ([l] + asg)
  {
    var lit :| lit in c && lit in asg;  // from requires
    assert lit in [l] + asg;  // since asg is a suffix of [l] + asg
  }
}

lemma appendAssignmentsContains(l: Literal, assignments: seq<Assignment>, asg: Assignment)
  requires asg in appendAssignments(l, assignments)
  ensures exists orig :: asg == [l] + orig && orig in assignments
{
  if assignments != [] {
    var first := assignments[0];
    var rest := assignments[1..];
    if asg == [l] + first {
      // Found it in first element
      assert first in assignments;  // since first == assignments[0]
      assert asg == [l] + first;   // from if condition
    } else {
      // Must be in rest
      assert asg in appendAssignments(l, rest);  // from definition of appendAssignments
      appendAssignmentsContains(l, rest, asg);
      var orig :| asg == [l] + orig && orig in rest;
      assert orig in assignments;  // since rest is a subsequence of assignments
    }
  }
}

lemma prependInSequence<T>(x: T, s: seq<T>)
  ensures x in [x] + s
{
  assert ([x] + s)[0] == x;
}

// Helper function to find the original clause
function findOriginalClause(l: Literal, p: Problem, c: Clause): Clause
  requires c in propagate(l, p)
  ensures var orig_c := findOriginalClause(l, p, c);
         orig_c in p && l !in orig_c && c == remove(orig_c, negate(l))
  decreases p
{
  propagateHasOriginal(l, p, c);  // proves such a clause exists
  if p == [] then (
    assert propagate(l, p) == [];
    assert false;  // contradiction: c in propagate(l, []) == []
    []
  ) else if l in p[0] then (
    assert propagate(l, p) == propagate(l, p[1..]);
    findOriginalClause(l, p[1..], c)
  ) else if c == remove(p[0], negate(l)) then (
    assert p[0] in p;
    assert l !in p[0];  // since we're in else branch
    p[0]
  ) else (
    propagateContainsRest(l, p, c);  // proves c in propagate(l, p[1..])
    findOriginalClause(l, p[1..], c)
  )
}

// Helper lemma: if c is in propagate(l, p), then there exists an original clause in p
lemma propagateHasOriginal(l: Literal, p: Problem, c: Clause)
  requires c in propagate(l, p)
  ensures exists orig_c :: orig_c in p && l !in orig_c && c == remove(orig_c, negate(l))
  decreases p
{
  if p == [] {
    // Contradiction: c in propagate(l, []) == []
    assert propagate(l, p) == [];
    assert false;
  } else {
    if l in p[0] {
      // c must come from propagate(l, rest)
      assert propagate(l, p) == propagate(l, p[1..]);
      propagateHasOriginal(l, p[1..], c);
      var orig_c :| orig_c in p[1..] && l !in orig_c && c == remove(orig_c, negate(l));
      assert orig_c in p;  // since p[1..] is a subsequence of p
    } else if c == remove(p[0], negate(l)) {
      // Found it - it's p[0]
      assert p[0] in p;
      assert l !in p[0];  // since we're in else branch
      assert c == remove(p[0], negate(l));
      // Witness is p[0]
    } else {
      // c must come from propagate(l, rest)
      assert c in propagate(l, p[1..]);  // from definition of propagate
      propagateHasOriginal(l, p[1..], c);
      var orig_c :| orig_c in p[1..] && l !in orig_c && c == remove(orig_c, negate(l));
      assert orig_c in p;  // since p[1..] is a subsequence of p
    }
  }
}

lemma propagateContainsRest(l: Literal, p: Problem, c: Clause)
  requires p != []
  requires c in propagate(l, p)
  requires l !in p[0]
  requires c != remove(p[0], negate(l))
  ensures c in propagate(l, p[1..])
{
  assert propagate(l, p) == [remove(p[0], negate(l))] + propagate(l, p[1..]);
  // Since c is in propagate(l, p) but isn't remove(p[0], negate(l)),
  // it must be in propagate(l, p[1..])
}

lemma solveCombinesResults(p: Problem, l: Literal, pos_solns: seq<Assignment>, neg_solns: seq<Assignment>)
  requires p != [] && p[0] != [] && l == p[0][0]
  requires solve(problemSize(p) * 2 - 1, propagate(l, p[1..])) == Result(pos_solns)
  requires solve(problemSize(p) * 2 - 1, propagate(negate(l), p)) == Result(neg_solns)
  ensures solve(problemSize(p) * 2, p) == 
    Result(appendAssignments(l, pos_solns) + appendAssignments(negate(l), neg_solns))
{
  assert solve(problemSize(p) * 2, p) == 
    Result(appendAssignments(l, pos_solns) + appendAssignments(negate(l), neg_solns));
}

lemma removePreservesOthers(c: Clause, l: Literal, x: Literal)
  requires x in remove(c, l)
  ensures x in c && x != l
{
  if c != [] {
    var rest := c[1..];
    if c[0] == l {
      removePreservesOthers(rest, l, x);
    } else {
      if x == c[0] {
        assert x in c;
        assert x != l;  // since c[0] != l
      } else {
        removePreservesOthers(rest, l, x);
      }
    }
  }
}

lemma removePreservesNonMatch(c: Clause, l: Literal, x: Literal)
  requires x in c && x != l
  ensures x in remove(c, l)
{
  if c != [] {
    var rest := c[1..];
    if c[0] == l {
      removePreservesNonMatch(rest, l, x);
    } else if x == c[0] {
      // x survives since it's not l
    } else {
      removePreservesNonMatch(rest, l, x);
    }
  }
}

// Helper lemma to show that solve returns a satisfying assignment
lemma solveReturnsResult(p: Problem, l: Literal, pos_solns: seq<Assignment>, neg_solns: seq<Assignment>, asg: Assignment)
  requires p != [] && p[0] != [] && l == p[0][0]
  requires solve(problemSize(p) * 2 - 1, propagate(l, p[1..])) == Result(pos_solns)
  requires solve(problemSize(p) * 2 - 1, propagate(negate(l), p)) == Result(neg_solns)
  requires asg in appendAssignments(l, pos_solns) || asg in appendAssignments(negate(l), neg_solns)
  requires satisfies(p, asg)
  ensures match solve(problemSize(p) * 2, p)
          case Result(assignments) => asg in assignments
          case FuelExhausted => false
{
  // Show step by step how final result is constructed
  solveCombinesResults(p, l, pos_solns, neg_solns);
  
  // From solveCombinesResults we know:
  assert solve(problemSize(p) * 2, p) == 
    Result(appendAssignments(l, pos_solns) + appendAssignments(negate(l), neg_solns));
  
  // From requires we know asg is in one of the branches
  if asg in appendAssignments(l, pos_solns) {
    // Show asg is in the concatenated result
    assert asg in appendAssignments(l, pos_solns) + appendAssignments(negate(l), neg_solns);
  } else {
    assert asg in appendAssignments(negate(l), neg_solns);
    assert asg in appendAssignments(l, pos_solns) + appendAssignments(negate(l), neg_solns);
  }
  
  // Therefore asg is in the final result
  assert asg in solve(problemSize(p) * 2, p).assignments;
}

// Helper lemma for second ensures clause
lemma propagatePreservesSatisfaction(p: Problem, asg: Assignment, assignments: seq<Assignment>)
  requires asg in assignments
  requires isConsistent(asg)
  ensures forall l :: satisfies(p, asg) && l in asg ==> satisfies(propagate(l, p), asg)
{
  forall l | satisfies(p, asg) && l in asg 
  ensures satisfies(propagate(l, p), asg)
  {
    forall c | c in propagate(l, p)
    ensures exists lit :: lit in c && lit in asg
    {
      // Find original clause
      propagateHasOriginal(l, p, c);
      var orig_c :| orig_c in p && l !in orig_c && c == remove(orig_c, negate(l));
      
      // Since asg satisfies orig_c, find satisfying literal
      assert orig_c in p;  // from propagateHasOriginal
      assert exists lit :: lit in orig_c && lit in asg;  // since asg satisfies p
      var lit :| lit in orig_c && lit in asg;
      
      if lit != negate(l) {
        // If lit != negate(l), it survives removal
        removePreservesNonMatch(orig_c, negate(l), lit);
        assert lit in c && lit in asg;
      } else {
        // If lit == negate(l), we need to find another literal
        assert l == negate(lit);  // from if condition
        
        // Since asg is consistent and lit is in asg,
        // negate(lit) can't be in asg
        assert lit in asg;  // from above
        assert isConsistent(asg);  // from requires
        assert negate(lit) !in asg;  // from isConsistent
        
        // Therefore there must be another literal in orig_c that's in asg
        assert exists other :: other in orig_c && other in asg && other != negate(l);
        var other :| other in orig_c && other in asg && other != negate(l);
        
        removePreservesNonMatch(orig_c, negate(l), other);
        assert other in c && other in asg;
      }
    }
  }
}

lemma propagateSatisfactionLemma(l: Literal, p: Problem, sat_asg: Assignment)
  requires satisfies(p, sat_asg)
  requires negate(l) !in sat_asg
  ensures satisfies(propagate(l, p), sat_asg)
{
  forall c | c in propagate(l, p)
  ensures exists lit :: lit in c && lit in sat_asg
  {
    propagateHasOriginal(l, p, c);
    var orig_c :| orig_c in p && l !in orig_c && c == remove(orig_c, negate(l));
    
    assert orig_c in p;
    assert exists lit :: lit in orig_c && lit in sat_asg;
    var lit :| lit in orig_c && lit in sat_asg;
    
    if lit != negate(l) {
      removePreservesNonMatch(orig_c, negate(l), lit);
      assert lit in c && lit in sat_asg;
    } else {
      assert lit in sat_asg;
      assert lit == negate(l);
      assert false;  // contradicts requires
    }
  }
}

// Add this lemma for fuel monotonicity
lemma solveFuelMonotonic(p: Problem, fuel1: nat, fuel2: nat)
  requires fuel1 <= fuel2
  requires solve(fuel1, p).Result?
  ensures solve(fuel2, p).Result?
  ensures solve(fuel1, p).assignments == solve(fuel2, p).assignments
  decreases problemSize(p)
{
  if p == [] {
    assert solve(fuel1, p) == Result([[]]);
    assert solve(fuel2, p) == Result([[]]);
  } else if p[0] == [] {
    assert solve(fuel1, p) == Result([]);
    assert solve(fuel2, p) == Result([]);
  } else if fuel1 == 0 {
    assert false;  // contradicts requires since solve(0, p) == FuelExhausted
  } else {
    var l := p[0][0];
    var rest := p[1..];
    
    propagateReduces(l, rest);
    propagateReduces(negate(l), p);
    
    var pos_result1 := solve(fuel1 - 1, propagate(l, rest));
    var neg_result1 := solve(fuel1 - 1, propagate(negate(l), p));
    var pos_result2 := solve(fuel2 - 1, propagate(l, rest));
    var neg_result2 := solve(fuel2 - 1, propagate(negate(l), p));
    
    solveFuelMonotonic(propagate(l, rest), fuel1 - 1, fuel2 - 1);
    solveFuelMonotonic(propagate(negate(l), p), fuel1 - 1, fuel2 - 1);
  }
}

// Add this helper lemma
lemma removePreservesConsistency(asg: Assignment, l: Literal)
  requires isConsistent(asg)
  ensures isConsistent(remove(asg, l))
{
  forall x | x in remove(asg, l)
  ensures negate(x) !in remove(asg, l)
  {
    removeContains(asg, l, x);
    assert x in asg && x != l;
    if negate(x) in remove(asg, l) {
      removeContains(asg, l, negate(x));
      assert negate(x) in asg;
      assert false;  // contradicts isConsistent(asg)
    }
  }
}

lemma appendAssignmentsIncludes(l: Literal, assignments: seq<Assignment>, asg: Assignment)
  requires asg in assignments
  ensures [l] + asg in appendAssignments(l, assignments)
{
  if assignments != [] {
    var first := assignments[0];
    var rest := assignments[1..];
    if asg == first {
      assert [l] + asg == [[l] + first][0];
      assert [[l] + first][0] in appendAssignments(l, assignments);
    } else {
      appendAssignmentsIncludes(l, rest, asg);
      assert [l] + asg in appendAssignments(l, rest);
      assert appendAssignments(l, assignments) == [[l] + first] + appendAssignments(l, rest);
    }
  }
}

lemma satisfiesSubsequence(p: Problem, asg: Assignment, start: nat)
  requires satisfies(p, asg)
  requires start <= |p|
  ensures satisfies(p[start..], asg)
{
  // Simple proof - if asg satisfies each clause in p,
  // it must satisfy each clause in any subsequence of p
  forall c | c in p[start..]
  ensures exists l :: l in c && l in asg
  {
    assert c in p;  // since c in p[start..]
    // Rest follows from satisfies(p, asg)
  }
}

lemma prependPreservesSatisfaction(l: Literal, p: Problem, asg: Assignment)
  requires satisfies(p, asg)
  ensures satisfies(p, [l] + asg)
{
  forall c | c in p
  ensures exists lit :: lit in c && lit in ([l] + asg)
  {
    var lit :| lit in c && lit in asg;
    assert lit in [l] + asg;  // since asg is suffix of [l] + asg
  }
}

lemma solvePropagatedBranch(p: Problem, l: Literal, rest: Problem, sat_asg: Assignment)
  requires p != [] && p[0] != []
  requires l == p[0][0]
  requires rest == p[1..]
  requires satisfies(p, sat_asg)
  requires isConsistent(sat_asg)
  requires l in sat_asg
  requires coversAllVariables(p, sat_asg)
  ensures match solve(problemSize(p) * 2 - 1, propagate(l, rest))
          case Result(assignments) => 
            exists asg :: asg in assignments && satisfies(propagate(l, rest), asg) &&
                   forall m :: m in asg ==> (m in sat_asg || negate(m) in sat_asg)
          case FuelExhausted => false
  decreases problemSize(p), 0
{
  // Show problem size decreases
  propagateReduces(l, rest);
  assert problemSize(propagate(l, rest)) < problemSize(p);
  
  // Show sat_asg satisfies propagate(l, rest)
  satisfiesSubsequence(p, sat_asg, 1);
  assert negate(l) !in sat_asg;  // from isConsistent(sat_asg) and l in sat_asg
  propagateSatisfactionLemma(l, rest, sat_asg);
  
  // Use recursive call
  // First show that coversAllVariables is preserved for rest
  forall c, lit | c in rest && lit in c
  ensures lit in sat_asg || negate(lit) in sat_asg
  {
    assert rest == p[1..];
    assert c in p;  // since c in rest and rest is suffix of p
    assert coversAllVariables(p, sat_asg);
    assert lit in sat_asg || negate(lit) in sat_asg;
  }
  assert coversAllVariables(rest, sat_asg);
  propagatePreservesCoverage(l, rest, sat_asg);
  solveComplete(propagate(l, rest), sat_asg);
  
  // Connect recursive result to our ensures
  assert solve(problemSize(propagate(l, rest)) * 2, propagate(l, rest)).Result?;
  var rec_result := solve(problemSize(propagate(l, rest)) * 2, propagate(l, rest));
  
  // Show we have enough fuel
  solveFuelMonotonic(propagate(l, rest), 
                    problemSize(propagate(l, rest)) * 2,
                    problemSize(p) * 2 - 1);
}

lemma prependPreservesPropagatedSatisfaction(l: Literal, p: Problem, asg: Assignment)
  requires satisfies(propagate(l, p), asg)
  ensures satisfies(propagate(l, p), [l] + asg)
{
  forall c | c in propagate(l, p)
  ensures exists lit :: lit in c && lit in ([l] + asg)
  {
    // Since asg satisfies propagate(l, p), find satisfying literal
    var lit :| lit in c && lit in asg;
    // That literal is still in [l] + asg
    assert lit in [l] + asg;  // since asg is suffix of [l] + asg
  }
}

lemma propagateSoundnessWithPrefix(l: Literal, p: Problem, rest: Problem, asg: Assignment)
  requires p != [] && p[0] != []
  requires l == p[0][0]
  requires rest == p[1..]
  requires satisfies(propagate(l, rest), asg)  // what we have from pos_asg
  ensures satisfies(p, [l] + asg)  // what solveReturnsResult needs
{
  // Need to show every clause in p is satisfied by [l] + asg
  forall c | c in p
  ensures exists lit :: lit in c && lit in ([l] + asg)
  {
    if c == p[0] {
      // First clause contains l
      assert l in c;  // since l == p[0][0]
      assert l in [l] + asg;  // by definition of [l] + asg
    } else {
      // c is in rest, so either:
      // 1. l is in c (satisfied by [l] + asg)
      // 2. l is not in c, so c is in propagate(l, rest)
      if l in c {
        assert l in [l] + asg;
      } else {
        // c must be in propagate(l, rest)
        assert c in rest;  // since c != p[0]
        propagateContains(l, rest, c);
        // Find literal in asg that satisfies c
        var lit :| lit in remove(c, negate(l)) && lit in asg;
        removeContains(c, negate(l), lit);
        assert lit in c && lit != negate(l);
        assert lit in [l] + asg;  // since asg is suffix of [l] + asg
      }
    }
  }
}