// Inspired by http://www.cis.upenn.edu/~bcpierce/sf/Types.html

// Typed Arithmetic Expressions

// Syntax

datatype tm = ttrue | tfalse | tif(c: tm, a: tm, b: tm) | tzero | tsucc(p: tm) | tpred(s: tm) | tiszero(n: tm) | terror ;

function bvalue(t: tm): bool
{
  t == ttrue || t == tfalse
}

function nvalue(t: tm): bool
{
  t.tzero? || (t.tsucc? && nvalue(t.p))
}

function value(t: tm): bool
{
  bvalue(t) || nvalue(t)
}

// Operational Semantics
function step(t: tm): tm
{
  /* IfTrue */     if (t.tif? && t.c == ttrue) then t.a
  /* IfFalse */    else if (t.tif? && t.c == tfalse) then t.b
  /* If */         else if (t.tif? && step(t.c) != terror) then tif(step(t.c), t.a, t.b)
  /* Succ */       else if (t.tsucc? && step(t.p) != terror) then tsucc(step(t.p))
  /* PredZero */   else if (t.tpred? && t.s == tzero) then tzero
  /* PredSucc */   else if (t.tpred? && t.s.tsucc? && nvalue(t.s.p)) then t.s.p
  /* Pred */       else if (t.tpred? && step(t.s) != terror) then tpred(step(t.s))
  /* IszeroZero */ else if (t.tiszero? && t.n == tzero) then ttrue
  /* IszeroSucc */ else if (t.tiszero? && nvalue(t.n)) then tfalse
  /* Iszero */     else if (t.tiszero? && step(t.n) != terror) then tiszero(step(t.n))
                   else terror
}

function normal_form(t: tm): bool
{
  step(t) == terror
}

function stuck(t: tm): bool
{
  normal_form(t) && !value(t)
}

ghost method example_some_term_is_stuck()
  ensures exists t :: stuck(t);
{
}

ghost method lemma_value_is_nf(t: tm)
  requires value(t);
  ensures normal_form(t);
{
  if (t.tsucc?) {
    lemma_value_is_nf(t.p);
  }
}

// Typing

datatype ty = TBool | TNat | TError;

function has_type(t: tm): ty
{
  /* True */       if (t.ttrue?) then TBool
  /* False */      else if (t.tfalse?) then TBool
  /* If */         else if (t.tif? && has_type(t.c) == TBool && has_type(t.a) == has_type(t.b)) then has_type(t.a)
  /* Zero */       else if (t.tzero?) then TNat
  /* Succ */       else if (t.tsucc? && has_type(t.p) == TNat) then TNat
  /* Pred */       else if (t.tpred? && has_type(t.s) == TNat) then TNat
  /* IsZero */     else if (t.tiszero? && has_type(t.n) == TNat) then TBool
                   else TError
}

ghost method theorem_progress(t: tm, T: ty)
  requires has_type(t) == T && T != TError;
  ensures value(t) || (exists t' :: step(t) == t' && t' != terror);
{
  if (t.tif?) {
    theorem_progress(t.c, TBool);
    theorem_progress(t.a, T);
    theorem_progress(t.b, T);
  }
  if (t.tsucc?) {
    theorem_progress(t.p, TNat);
    assert T == TNat;
  }
  if (t.tpred?) {
    theorem_progress(t.s, TNat);
    assert T == TNat;
  }
  if (t.tiszero?) {
    theorem_progress(t.n, TNat);
    assert T == TBool;
  }
}

ghost method theorem_preservation(t: tm, t': tm, T: ty)
  requires has_type(t) == T && T != TError;
  requires step(t) == t' && t' != terror;
  ensures has_type(t') == T;
{
  if (t.tif? && step(t.c) != terror) {
    theorem_preservation(t.c, step(t.c), TBool);
  }
  if (t.tsucc? && step(t.p) != terror) {
    theorem_preservation(t.p, step(t.p), TNat);
  }
  if (t.tpred? && step(t.s) != terror) {
    theorem_preservation(t.s, step(t.s), TNat);
  }
  if (t.tiszero? && step(t.n) != terror) {
    theorem_preservation(t.n, step(t.n), TNat);
  }
}

function reduces_to(t: tm, t': tm, n: nat): bool
  decreases n;
{
  t == t' || (n > 0 && step(t) != terror && reduces_to(step(t), t', n-1))
}

ghost method corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(t) == T && T != TError;
  requires reduces_to(t, t', n);
  ensures !stuck(t');
{
  theorem_progress(t, T);
  var i: nat := n;
  var ti := t;
  while (i > 0 && step(ti) != terror && ti != t')
    invariant has_type(ti) == T;
    invariant reduces_to(ti, t', i);
    invariant !stuck(ti);
  {
    theorem_preservation(ti, step(ti), T);
    i := i - 1;
    ti := step(ti);
    theorem_progress(ti, T);
  }
}

