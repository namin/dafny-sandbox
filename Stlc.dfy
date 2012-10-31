// The Simply Typed Lambda-Calculus
// http://www.cis.upenn.edu/~bcpierce/sf/Stlc.html

// Utilities
datatype option<A> = None | Some(get: A);


// Syntax

// Types
datatype ty = TBool | TArrow(paramT: ty, bodyT: ty);

// Terms
datatype tm = tvar(id: nat) | tapp(f: tm, arg: tm) | tabs(x: nat, T: ty, body: tm) | ttrue | tfalse | tif(c: tm, a: tm, b: tm);


// Operational Semantics

// Values
function value(t: tm): bool
{
  t.tabs? || t.ttrue? || t.tfalse?
}

// Free Variables and Substitution
function subst(x: nat, s: tm, t: tm): tm
{
  match t
  case tvar(x') => if x==x' then s else t
  case tabs(x', T, t1) => tabs(x', T, if x==x' then t1 else subst(x, s, t1))
  case tapp(t1, t2) => tapp(subst(x, s, t1), subst(x, s, t2))
  case ttrue => ttrue
  case tfalse => tfalse
  case tif(t1, t2, t3) => tif(subst(x, s, t1), subst(x, s, t2), subst(x, s, t3))
}

// Reduction
function step(t: tm): option<tm>
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then Some(subst(t.f.x, t.arg, t.f.body))
  /* App1 */       else if (t.tapp? && step(t.f).Some?) then Some(tapp(step(t.f).get, t.arg))
  /* App2 */       else if (t.tapp? && step(t.arg).Some?) then Some(tapp(t.f, step(t.arg).get))
  /* IfTrue */     else if (t.tif? && t.c == ttrue) then Some(t.a)
  /* IfFalse */    else if (t.tif? && t.c == tfalse) then Some(t.b)
  /* If */         else if (t.tif? && step(t.c).Some?) then Some(tif(step(t.c).get, t.a, t.b))
                   else None
}

function reduces_to(t: tm, t': tm, n: nat): bool
  decreases n;
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
}

// Examples
ghost method lemma_step_example1(n: nat)
  requires n > 0;
  ensures reduces_to(tapp(tabs(0, TArrow(TBool, TBool), tvar(0)), tabs(0, TBool, tvar(0))), tabs(0, TBool, tvar(0)), n);
{
}


// Typing

// Contexts

datatype partial_map<A> = Empty | Extend(x: nat, v: A, rest: partial_map<A>);
function find<A>(m: partial_map<A>, x: nat): option<A>
{
  match m
  case Empty => None
  case Extend(x', v, rest) => if x==x' then Some(v) else find(rest, x)
}

ghost method lemma_extend_eq<A>(m: partial_map<A>, x: nat, v: A)
  ensures find(Extend(x, v, m), x) == Some(v);
{
}
ghost method lemma_extend_neq<A>(m: partial_map<A>, x1: nat, v: A, x2: nat)
  requires x1 != x2;
  ensures find(Extend(x2, v, m), x1) == find(m, x1);
{
}

datatype context = Context(m: partial_map<ty>);

// Typing Relation
function has_type(c: context, t: tm): option<ty>
  decreases t;
{
  match t
  /* Var */        case tvar(id) => find(c.m, id)
  /* Abs */        case tabs(x, T, body) =>
                     var ty_body := has_type(Context(Extend(x, T, c.m)), body);
                     if (ty_body.Some?) then Some(TArrow(T, ty_body.get)) else None
  /* App */        case tapp(f, arg) =>
                     var ty_f := has_type(c, f);
                     var ty_arg := has_type(c, arg);
                     if (ty_f.Some? && ty_arg.Some? && ty_f.get.TArrow? && ty_f.get.paramT == ty_arg.get)
                     then Some(ty_f.get.bodyT)
                     else None
 /* True */        case ttrue => Some(TBool)
 /* False */       case tfalse => Some(TBool)
 /* If */          case tif(cond, a, b) =>
                     var ty_c := has_type(c, cond);
                     var ty_a := has_type(c, a);
                     var ty_b := has_type(c, b);
                     if (ty_c.Some? && ty_a.Some? && ty_b.Some? && ty_c.get == TBool && ty_a.get == ty_b.get)
                     then ty_a
                     else None
}

// Examples

ghost method example_typing_1()
  ensures has_type(Context(Empty), tabs(0, TBool, tvar(0))) == Some(TArrow(TBool, TBool));
{
}

ghost method example_typing_2()
  ensures has_type(Context(Empty), tabs(0, TBool, tabs(1, TArrow(TBool, TBool), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) ==
          Some(TArrow(TBool, TArrow(TArrow(TBool, TBool), TBool)));
{
  var c := Context(Extend(1, TArrow(TBool, TBool), Extend(0, TBool, Empty)));
  assert find(c.m, 0) == Some(TBool);
  assert has_type(c, tvar(0)) == Some(TBool);
  assert has_type(c, tvar(1)) == Some(TArrow(TBool, TBool));
  assert has_type(c, tapp(tvar(1), tapp(tvar(1), tvar(0)))) == Some(TBool);
}

ghost method nonexample_typing_1()
  ensures has_type(Context(Empty), tabs(0, TBool, tabs(1, TBool, tapp(tvar(0), tvar(1))))) == None;
{
  var c := Context(Extend(1, TBool, Extend(0, TBool, Empty)));
  assert find(c.m, 0) == Some(TBool);
  assert has_type(c, tapp(tvar(0), tvar(1))) == None;
}

ghost method nonexample_typing_3(S: ty, T: ty)
  ensures has_type(Context(Empty), tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
{
  var c:= Context(Extend(0, S, Empty));
  assert has_type(c, tapp(tvar(0), tvar(0))) == None;
}


// Properties


// Progress
ghost method theorem_progress(t: tm)
  requires has_type(Context(Empty), t).Some?;
  ensures value(t) || step(t).Some?;
{
}


// Free Occurrences
function appears_free_in(x: nat, t: tm): bool
{
  /* var */  (t.tvar? && t.id==x) ||
  /* app1 */ (t.tapp? && appears_free_in(x, t.f)) ||
  /* app2 */ (t.tapp? && appears_free_in(x, t.arg)) ||
  /* abs */  (t.tabs? && t.x!=x && appears_free_in(x, t.body)) ||
  /* if1 */  (t.tif? && appears_free_in(x, t.c)) ||
  /* if2 */  (t.tif? && appears_free_in(x, t.a)) ||
  /* if3 */  (t.tif? && appears_free_in(x, t.b))
}

function closed(t: tm): bool
{
  forall x: nat :: !appears_free_in(x, t)
}


// Substitution Lemma

ghost method lemma_free_in_context(c: context, x: nat, t: tm)
  requires appears_free_in(x, t);
  requires has_type(c, t).Some?;
  ensures find(c.m, x).Some?;
  ensures has_type(c, t).Some?;
  decreases t;
{
  if (t.tabs?) {
    assert t.x != x;
    lemma_free_in_context(Context(Extend(t.x, t.T, c.m)), x, t.body);
    assert find(Extend(t.x, t.T, c.m), x).Some?;
  }
}

ghost method corollary_typable_empty__closed(t: tm)
  requires has_type(Context(Empty), t).Some?;
  ensures closed(t);
{
  parallel (x: nat)
    ensures !appears_free_in(x, t);
  {
    if (appears_free_in(x, t)) {
      lemma_free_in_context(Context(Empty), x, t);
      assert find(Empty, x).Some?;
      assert false;
    }
    assert !appears_free_in(x, t);
  }
}

ghost method lemma_context_invariance(c: context, c': context, t: tm)
  requires has_type(c, t).Some?;
  requires forall x: nat :: appears_free_in(x, t) ==> find(c.m, x) == find(c'.m, x);
  ensures has_type(c, t) == has_type(c', t);
  decreases t;
{
  if (t.tabs?) {
    assert find(Extend(t.x, t.T, c.m), t.x) == find(Extend(t.x, t.T, c'.m), t.x);
    lemma_context_invariance(Context(Extend(t.x, t.T, c.m)), Context(Extend(t.x, t.T, c'.m)), t.body);
  }
}

ghost method lemma_substitution_preserves_typing(c: context, x: nat, t': tm, t: tm)
  requires has_type(Context(Empty), t').Some?;
  requires has_type(Context(Extend(x, has_type(Context(Empty), t').get, c.m)), t).Some?;
  ensures has_type(c, subst(x, t', t)) == has_type(Context(Extend(x, has_type(Context(Empty), t').get, c.m)), t);
  decreases t;
{
  if (t.tvar? && t.id==x) {
    corollary_typable_empty__closed(t');
    lemma_context_invariance(Context(Empty), c, t');
  }
  if (t.tabs?) {
    var U := has_type(Context(Empty), t').get;
    if (t.x==x) {
      lemma_context_invariance(Context(Extend(x, U, c.m)), c, t);
    } else {
      var c_px := Context(Extend(t.x, t.T, Extend(x, U, c.m)));
      var c_xp := Context(Extend(x, U, Extend(t.x, t.T, c.m)));
      var c_p := Context(Extend(t.x, t.T, c.m));
      assert find(c_px.m, x) == find(c_xp.m, x);
      assert find(c_px.m, t.x) == find(c_xp.m, t.x);
      lemma_context_invariance(c_px, c_xp, t.body);
      lemma_substitution_preserves_typing(c_p, x, t', t.body);
    }
  }
}


// Preservation
ghost method theorem_preservation(t: tm)
  requires has_type(Context(Empty), t).Some?;
  requires step(t).Some?;
  ensures has_type(Context(Empty), step(t).get) == has_type(Context(Empty), t);
{
  if (t.tapp? && step(t.f).None? && step(t.arg).None?) {
    lemma_substitution_preserves_typing(Context(Empty), t.f.x, t.arg, t.f.body);
  }
}


// Type Soundness

function normal_form(t: tm): bool
{
  step(t).None?
}

function stuck(t: tm): bool
{
  normal_form(t) && !value(t)
}

ghost method corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(Context(Empty), t) == Some(T);
  requires reduces_to(t, t', n);
  ensures !stuck(t');
{
  theorem_progress(t);
  var i: nat := n;
  var ti := t;
  while (i > 0 && step(ti).Some? && ti != t')
    invariant has_type(Context(Empty), ti) == Some(T);
    invariant reduces_to(ti, t', i);
    invariant !stuck(ti);
  {
    theorem_preservation(ti);
    i := i - 1;
    ti := step(ti).get;
    theorem_progress(ti);
  }
}