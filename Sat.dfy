// A Very Small SAT Solver in Dafny
// https://web.archive.org/web/20201109101535/http://www.cse.chalmers.se/~algehed/blogpostsHTML/SAT.html
// translated from the original Haskell
// for ideas on what to prove, see this old port to Coq here: https://github.com/acorrenson/SATurne
// see also my older DPLL work based on Adam's Chlipala textbook exercise: https://github.com/namin/coq-sandbox/blob/master/Dpll.v
//
// used LLMs inculding ChatGPT 4o, (Cursor) Claude Sonnet 3.5 and more recently Claude Code (Opus)
// - for initial translation,
// - for stating high-level properties,
// - for the decomposition into lemmas and their proofs,
// - for great simplifications, eventually (with Opus 4.5).

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

function appendAssignments(l: Literal, assignments: seq<Assignment>): seq<Assignment>
{
  if assignments == [] then []
  else
    var first := assignments[0];
    var rest := assignments[1..];
    [[l] + first] + appendAssignments(l, rest)
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
    removeReduces(c[1..], l);
  }
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
    } else {
      removeReduces(c, negate(l));
      propagateReduces(l, rest);
    }
  }
}

/*
-- a simple backtracking search where we propagate the choice of the literal to the rest of the problem and check the smaller problem
solve :: Problem -> [Assignment]
solve []    = [[]]
solve (c:p) = do
  (l:c) <- [c]
  ([l:as | as <- solve (propagate l p)] ++ [negate l:as | as <- solve (propagate (negate l) (c:p))])
*/
function solve(p: Problem): seq<Assignment>
  decreases problemSize(p)
{
  if p == [] then [[]]
  else if p[0] == [] then []
  else
    var l := p[0][0];
    var rest := p[1..];
    propagateReduces(l, rest);
    propagateReduces(negate(l), p);
    appendAssignments(l, solve(propagate(l, rest))) +
    appendAssignments(negate(l), solve(propagate(negate(l), p)))
}

method MainExamples()
{
  var problem1 := [[Pos(1), Neg(2)], [Neg(1), Pos(2)], [Pos(2), Pos(3)], [Neg(3)]];
  var result1 := solve(problem1);
  print "Solutions: ", result1, "\n";

  var problem2 := [[Pos(1)], [Neg(1)]]; // UNSAT (contradiction)
  var result2 := solve(problem2);
  print "No solutions found: ", result2, "\n";
}

// ## Consistent
predicate isConsistent(asg: Assignment)
{
  forall l :: l in asg ==> negate(l) !in asg
}

function satisfies(p: Problem, asg: Assignment): bool
{
  forall c: Clause :: c in p ==> exists l: Literal :: l in asg && l in c
}

// ## Sound
lemma solveSound(p: Problem, asg: Assignment)
  requires asg in solve(p)
  ensures satisfies(p, asg)
  decreases problemSize(p)
{
  if p != [] && p[0] != [] {
    var l := p[0][0];
    var rest := p[1..];

    if asg in appendAssignments(l, solve(propagate(l, rest))) {
      appendAssignmentsContains(l, solve(propagate(l, rest)), asg);
      var pos_asg :| asg == [l] + pos_asg && pos_asg in solve(propagate(l, rest));
      propagateReduces(l, rest);
      solveSound(propagate(l, rest), pos_asg);
      prependInSequence(l, pos_asg);
      propagateSoundness(l, rest, asg);
      forall c | c in p ensures exists lit :: lit in c && lit in asg {
        if c == p[0] { assert l in asg; } else { assert c in rest; }
      }
    } else {
      appendAssignmentsContains(negate(l), solve(propagate(negate(l), p)), asg);
      var neg_asg :| asg == [negate(l)] + neg_asg && neg_asg in solve(propagate(negate(l), p));
      propagateReduces(negate(l), p);
      solveSound(propagate(negate(l), p), neg_asg);
      prependInSequence(negate(l), neg_asg);
      propagateSoundness(negate(l), p, asg);
    }
  }
}

// ## Complete

predicate coversAllVariables(p: Problem, asg: Assignment)
{
  forall c, lit | c in p && lit in c ::
    lit in asg || negate(lit) in asg
}

lemma propagatePreservesCoverage(l: Literal, p: Problem, asg: Assignment)
  requires coversAllVariables(p, asg)
  ensures coversAllVariables(propagate(l, p), asg)
{
  forall c, lit | c in propagate(l, p) && lit in c
  ensures lit in asg || negate(lit) in asg
  {
    propagateHasOriginal(l, p, c);
    var orig_c :| orig_c in p && l !in orig_c && c == remove(orig_c, negate(l));
    removeContains(orig_c, negate(l), lit);
  }
}

lemma solveComplete(p: Problem, sat_asg: Assignment)
  requires satisfies(p, sat_asg)
  requires isConsistent(sat_asg)
  requires coversAllVariables(p, sat_asg)
  ensures exists asg :: asg in solve(p) && satisfies(p, asg) &&
                 forall l :: l in asg ==> (l in sat_asg || negate(l) in sat_asg)
  decreases problemSize(p)
{
  if p == [] {
    assert [] in solve(p) && satisfies(p, []);
  } else if p[0] == [] {
    assert p[0] in p;
  } else {
    var l := p[0][0];
    var rest := p[1..];

    if l in sat_asg {
      satisfiesSubsequence(p, sat_asg, 1);
      propagateSatisfactionLemma(l, rest, sat_asg);
      forall c, lit | c in rest && lit in c ensures lit in sat_asg || negate(lit) in sat_asg { assert c in p; }
      propagatePreservesCoverage(l, rest, sat_asg);
      propagateReduces(l, rest);
      solveComplete(propagate(l, rest), sat_asg);
      var pos_asg :| pos_asg in solve(propagate(l, rest)) &&
                     satisfies(propagate(l, rest), pos_asg) &&
                     forall m :: m in pos_asg ==> (m in sat_asg || negate(m) in sat_asg);
      appendAssignmentsIncludes(l, solve(propagate(l, rest)), pos_asg);
      prependInSequence(l, pos_asg);
      propagateSoundnessWithPrefix(l, p, rest, pos_asg);
    } else {
      propagateSatisfactionLemma(negate(l), p, sat_asg);
      propagatePreservesCoverage(negate(l), p, sat_asg);
      propagateReduces(negate(l), p);
      solveComplete(propagate(negate(l), p), sat_asg);
      var neg_asg :| neg_asg in solve(propagate(negate(l), p)) &&
                     satisfies(propagate(negate(l), p), neg_asg) &&
                     forall m :: m in neg_asg ==> (m in sat_asg || negate(m) in sat_asg);
      appendAssignmentsIncludes(negate(l), solve(propagate(negate(l), p)), neg_asg);
      prependInSequence(negate(l), neg_asg);
      prependPreservesSatisfaction(negate(l), propagate(negate(l), p), neg_asg);
      propagateSoundness(negate(l), p, [negate(l)] + neg_asg);
      forall m | m in [negate(l)] + neg_asg ensures m in sat_asg || negate(m) in sat_asg {
        if m == negate(l) { assert p[0] in p && l in p[0]; }
      }
    }
  }
}

// ## Helper Lemmas

lemma propagateSoundness(l: Literal, p: Problem, asg: Assignment)
  requires l in asg
  requires satisfies(propagate(l, p), asg)
  ensures satisfies(p, asg)
{
  forall c | c in p ensures exists lit :: lit in c && lit in asg {
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
  if c != [] && c[0] == l {
    removeContains(c[1..], l, x);
  } else if c != [] && x != c[0] {
    removeContains(c[1..], l, x);
  }
}

lemma propagateContains(l: Literal, p: Problem, c: Clause)
  requires c in p
  requires l !in c
  ensures remove(c, negate(l)) in propagate(l, p)
  decreases p
{
  if p != [] && c != p[0] {
    propagateContains(l, p[1..], c);
  }
}

lemma appendAssignmentsContains(l: Literal, assignments: seq<Assignment>, asg: Assignment)
  requires asg in appendAssignments(l, assignments)
  ensures exists orig :: asg == [l] + orig && orig in assignments
{
  if assignments != [] && asg != [l] + assignments[0] {
    appendAssignmentsContains(l, assignments[1..], asg);
  }
}

lemma prependInSequence<T>(x: T, s: seq<T>)
  ensures x in [x] + s
{}

lemma propagateHasOriginal(l: Literal, p: Problem, c: Clause)
  requires c in propagate(l, p)
  ensures exists orig_c :: orig_c in p && l !in orig_c && c == remove(orig_c, negate(l))
  decreases p
{
  if p != [] && (l in p[0] || c != remove(p[0], negate(l))) {
    propagateHasOriginal(l, p[1..], c);
  }
}

lemma removePreservesNonMatch(c: Clause, l: Literal, x: Literal)
  requires x in c && x != l
  ensures x in remove(c, l)
{
  if c != [] && x != c[0] {
    removePreservesNonMatch(c[1..], l, x);
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
    var lit :| lit in orig_c && lit in sat_asg;
    removePreservesNonMatch(orig_c, negate(l), lit);
  }
}

lemma appendAssignmentsIncludes(l: Literal, assignments: seq<Assignment>, asg: Assignment)
  requires asg in assignments
  ensures [l] + asg in appendAssignments(l, assignments)
{
  if assignments != [] && asg != assignments[0] {
    appendAssignmentsIncludes(l, assignments[1..], asg);
  }
}

lemma satisfiesSubsequence(p: Problem, asg: Assignment, start: nat)
  requires satisfies(p, asg)
  requires start <= |p|
  ensures satisfies(p[start..], asg)
{
  forall c | c in p[start..] ensures exists l :: l in c && l in asg { assert c in p; }
}

lemma prependPreservesSatisfaction(l: Literal, p: Problem, asg: Assignment)
  requires satisfies(p, asg)
  ensures satisfies(p, [l] + asg)
{}

lemma propagateSoundnessWithPrefix(l: Literal, p: Problem, rest: Problem, asg: Assignment)
  requires p != [] && p[0] != []
  requires l == p[0][0]
  requires rest == p[1..]
  requires satisfies(propagate(l, rest), asg)
  ensures satisfies(p, [l] + asg)
{
  forall c | c in p
  ensures exists lit :: lit in c && lit in ([l] + asg)
  {
    if c != p[0] && l !in c {
      propagateContains(l, rest, c);
      var lit :| lit in remove(c, negate(l)) && lit in asg;
      removeContains(c, negate(l), lit);
    }
  }
}