// A Very Small SAT Solver in Dafny
// https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html
// translated from the original Haskell mostly by ChatGPT 4o
// for ideas on what to prove, see this old port to Coq here: https://github.com/acorrenson/SATurne
// see also my older DPLL work based on Adam's Chlipala textbook exercise: https://github.com/namin/coq-sandbox/blob/master/Dpll.v
// the high-level properties to verify were initially suggested by ChatGPT 4o
// the proofs of those properties were done by (Cursor) Claude Sonnet 3.5
// including the decomposition into lemmas and the suggestion of the termination upper bound

// translatio from Haskell
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
method Main()
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
lemma solveComplete(p: Problem, sat_asg: Assignment)
  requires satisfies(p, sat_asg)
  requires isConsistent(sat_asg)
  ensures match solve(problemSize(p) * 2, p)
          case Result(assignments) => exists asg :: asg in assignments && satisfies(p, asg)
          case FuelExhausted => false
  ensures forall asg, l :: satisfies(p, asg) && l in asg ==> satisfies(propagate(l, p), asg)
  decreases problemSize(p)
{
  solveTerminatesHelper(p, problemSize(p) * 2);
  
  if p == [] {
    var empty_asg: Assignment := [];
    assert solve(problemSize(p) * 2, p) == Result([empty_asg]);
    assert empty_asg in [empty_asg];
    assert satisfies(p, empty_asg);
    // For second ensures: empty problem case is trivial
    assert forall asg, l :: satisfies([], asg) && l in asg ==> satisfies(propagate(l, []), asg);
  } else if p[0] == [] {
    // Impossible case - contradicts requires since empty clause can't be satisfied
    assert p[0] in p;  // first clause is in p
    assert exists l :: l in sat_asg && l in p[0];  // from satisfies(p, sat_asg)
    assert p[0] == [];  // from if condition
    assert false;  // contradiction: no literal can be in both sat_asg and empty clause
  } else {
    var l := p[0][0];
    var rest := p[1..];
    
    // Show problem size decreases
    propagateReduces(l, rest);
    propagateReduces(negate(l), p);
    
    if l in sat_asg {
      // First, prove sat_asg satisfies propagate(l, rest)
      forall c | c in propagate(l, rest)
      ensures exists lit :: lit in c && lit in sat_asg
      {
        // Find original clause
        propagateHasOriginal(l, rest, c);
        var orig_c :| orig_c in rest && l !in orig_c && c == remove(orig_c, negate(l));
        
        // Since sat_asg satisfies orig_c (it's in rest), find satisfying literal
        assert orig_c in p[1..];  // since orig_c in rest
        assert exists lit :: lit in orig_c && lit in sat_asg;
        var lit :| lit in orig_c && lit in sat_asg;
        
        // If lit != negate(l), it survives remove
        if lit != negate(l) {
          removePreservesNonMatch(orig_c, negate(l), lit);
          assert lit in c && lit in sat_asg;
        } else {
          // If lit == negate(l), we need to find another literal
          assert l == negate(lit);  // from if condition
          
          // Since sat_asg satisfies orig_c and l is in sat_asg,
          // there must be another literal in orig_c that's in sat_asg
          // (because negate(l) can't be in sat_asg when l is)
          assert l in sat_asg;  // from if condition
          assert negate(l) !in sat_asg;  // since l in sat_asg
          assert exists other :: other in orig_c && other in sat_asg && other != negate(l);
          var other :| other in orig_c && other in sat_asg && other != negate(l);
          
          removePreservesNonMatch(orig_c, negate(l), other);
          assert other in c && other in sat_asg;
        }
      }
      assert satisfies(propagate(l, rest), sat_asg);
      
      // Now use recursive call
      solveComplete(propagate(l, rest), sat_asg);
      
      // Get solution from recursive call
      var pos_result := solve(problemSize(p) * 2 - 1, propagate(l, rest));
      match pos_result {
        case Result(pos_solns) => {
          var pos_asg :| pos_asg in pos_solns && satisfies(propagate(l, rest), pos_asg);
          assert [l] + pos_asg in appendAssignments(l, pos_solns);
          propagateSoundness(l, rest, [l] + pos_asg);
          assert satisfies(p, [l] + pos_asg);
          
          // Use helper lemma to show solution is in final result
          var neg_result := solve(problemSize(p) * 2 - 1, propagate(negate(l), p));
          match neg_result {
            case Result(neg_solns) => {
              solveReturnsResult(p, l, pos_solns, neg_solns, [l] + pos_asg);
              propagatePreservesSatisfaction(p, sat_asg, neg_solns);
            }
            case FuelExhausted => assert false;
          }
        }
        case FuelExhausted => assert false;
      }
    } else {
      // First, prove sat_asg satisfies propagate(negate(l), p)
      forall c | c in propagate(negate(l), p)
      ensures exists lit :: lit in c && lit in sat_asg
      {
        // Find original clause
        propagateHasOriginal(negate(l), p, c);
        var orig_c :| orig_c in p && negate(l) !in orig_c && c == remove(orig_c, l);
        
        // Since sat_asg satisfies orig_c, find satisfying literal
        assert orig_c in p;  // from propagateHasOriginal
        assert exists lit :: lit in orig_c && lit in sat_asg;  // since satisfies(p, sat_asg)
        var lit :| lit in orig_c && lit in sat_asg;
        
        // If lit != l, it survives remove
        if lit != l {
          removePreservesNonMatch(orig_c, l, lit);
          assert lit in c && lit in sat_asg;
        } else {
          // If lit == l, we need to find another literal
          // But this case is impossible since l !in sat_asg
          assert lit in sat_asg;  // from above
          assert lit == l;  // from if condition
          assert l !in sat_asg;  // from branch condition
          assert false;  // contradiction
        }
      }
      assert satisfies(propagate(negate(l), p), sat_asg);
      
      // Now use recursive call
      solveComplete(propagate(negate(l), p), sat_asg);
      
      // Get solution from recursive call
      var neg_result := solve(problemSize(p) * 2 - 1, propagate(negate(l), p));
      match neg_result {
        case Result(neg_solns) => {
          var neg_asg :| neg_asg in neg_solns && satisfies(propagate(negate(l), p), neg_asg);
          assert [negate(l)] + neg_asg in appendAssignments(negate(l), neg_solns);
          propagateSoundness(negate(l), p, [negate(l)] + neg_asg);
          assert satisfies(p, [negate(l)] + neg_asg);
          
          // Use helper lemma to show solution is in final result
          var pos_result := solve(problemSize(p) * 2 - 1, propagate(l, rest));
          match pos_result {
            case Result(pos_solns) => {
              solveReturnsResult(p, l, pos_solns, neg_solns, [negate(l)] + neg_asg);
              propagatePreservesSatisfaction(p, sat_asg, pos_solns);
            }
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
