// http://www.cis.upenn.edu/~bcpierce/sf/Imp.html

// Arithmetic and Boolean Expressions

// Syntax
datatype aexp = ANum(int) | APlus(aexp, aexp) | AMinus(aexp, aexp) | AMult(aexp, aexp);

datatype bexp = BTrue | BFalse | BEq(aexp, aexp) | BLe(aexp, aexp) | BNot(bexp) | BAnd(bexp, bexp);

// Evaluation
function aeval(e: aexp): int
{
  match e
  case ANum(n) => n
  case APlus(a1, a2) => aeval(a1) + aeval(a2)
  case AMinus(a1, a2) => aeval(a1) - aeval(a2)
  case AMult(a1, a2) => aeval(a1) * aeval(a2)
}

function beval(e: bexp): bool
{
  match e
  case BTrue => true
  case BFalse => false
  case BEq(a1, a2) => aeval(a1) == aeval(a2)
  case BLe(a1, a2) => aeval(a1) < aeval(a2)
  case BNot(b1) => !beval(b1)
  case BAnd(b1, b2) => beval(b1) && beval(b2)
}

// Optimization
function optimize_0plus(e: aexp): aexp
  ensures aeval(optimize_0plus(e)) == aeval(e);
{
  match e
  case ANum(n) => ANum(n)
  case APlus(e1, e2) =>
    if (e1 == ANum(0)) then optimize_0plus(e2)
    else APlus(optimize_0plus(e1), optimize_0plus(e2))
  case AMinus(e1, e2) => AMinus(optimize_0plus(e1), optimize_0plus(e2))
  case AMult(e1, e2) => AMult(optimize_0plus(e1), optimize_0plus(e2))
}