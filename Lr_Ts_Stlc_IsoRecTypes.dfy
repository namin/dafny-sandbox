// Proving Type-Safety of the Simply Typed Lambda-Calculus
// with Iso-Recursive Types
// using Step-Indexed Logical Relations
// adapted from Lr_Ts_Stlc.dfy

datatype option<A> = None | Some(get: A);

// Syntax

// Types
datatype ty = TBool | TArrow(paramT: ty, bodyT: ty) |
              TVar(id: nat) | TRec(X: nat, T: ty);

// Terms
datatype tm = tvar(id: nat) | tapp(f: tm, arg: tm) | tabs(x: nat, T: ty, body: tm) | ttrue | tfalse | tif(c: tm, a: tm, b: tm) |
              tfold(Tf: ty, tf: tm) | tunfold(Tu: ty, tu: tm);


// Operational Semantics

// Values
function value(t: tm): bool
{
  t.tabs? || t.ttrue? || t.tfalse? ||
  (t.tfold? && value(t.tf))
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
  case tfold(T, t1) => tfold(T, subst(x, s, t1))
  case tunfold(T, t1) => tunfold(T, subst(x, s, t1))
}

function tsubst(X: nat, S: ty, T: ty): ty
{
  match T
  case TVar(X') => if X==X' then S else T
  case TRec(X', T1) => TRec(X', if X==X' then T1 else tsubst(X, S, T1))
  case TBool => TBool
  case TArrow(T1, T2) => TArrow(tsubst(X, S, T1), tsubst(X, S, T2))
}

// Reduction
function step(t: tm): option<tm>
  ensures step(t).Some? ==> !value(t);
  decreases t;
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then Some(subst(t.f.x, t.arg, t.f.body))
  /* App1 */       else if (t.tapp? && step(t.f).Some?) then Some(tapp(step(t.f).get, t.arg))
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg).Some?) then Some(tapp(t.f, step(t.arg).get))
  /* IfTrue */     else if (t.tif? && t.c == ttrue) then Some(t.a)
  /* IfFalse */    else if (t.tif? && t.c == tfalse) then Some(t.b)
  /* If */         else if (t.tif? && step(t.c).Some?) then Some(tif(step(t.c).get, t.a, t.b))
  /* UnfoldFold */ else if (t.tunfold? && t.tu.tfold? && value(t.tu.tf)) then Some(t.tu.tf)
  /* Fold */       else if (t.tfold? && step(t.tf).Some?) then Some(tfold(t.Tf, step(t.tf).get))
  /* Unfold */     else if (t.tunfold? && step(t.tu).Some?) then Some(tunfold(t.Tu, step(t.tu).get))
                   else None
}

predicate irred(t: tm)
{
  step(t).None?
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

datatype context = Context(m: partial_map<ty>);

// Typing Relation
function has_type(c: context, t: tm): option<ty>
  requires ty_closed_ctx(c.m);
  decreases t;
{
  match t
  /* Var */        case tvar(id) => find(c.m, id)
  /* Abs */        case tabs(x, T, body) =>
                     var ty_body := if (ty_closed(T)) then has_type(Context(Extend(x, T, c.m)), body) else None;
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
 /* Fold */        case tfold(U, t1) =>
                     var ty_t1 := if (ty_closed(U)) then has_type(c, t1) else None;
                     if (U.TRec? && ty_t1.Some? && ty_t1.get==tsubst(U.X, U, U.T))
                     then Some(U)
                     else None
/* Unfold */       case tunfold(U, t1) =>
                     var ty_t1 := if (ty_closed(U)) then has_type(c, t1) else None;
                     if (U.TRec? && ty_t1.Some? && ty_t1.get==U)
                     then Some(tsubst(U.X, U, U.T))
                     else None
}

// Properties

// Free Occurrences
function appears_free_in(x: nat, t: tm): bool
{
  /* var */    (t.tvar? && t.id==x) ||
  /* app1 */   (t.tapp? && appears_free_in(x, t.f)) ||
  /* app2 */   (t.tapp? && appears_free_in(x, t.arg)) ||
  /* abs */    (t.tabs? && t.x!=x && appears_free_in(x, t.body)) ||
  /* if1 */    (t.tif? && appears_free_in(x, t.c)) ||
  /* if2 */    (t.tif? && appears_free_in(x, t.a)) ||
  /* if3 */    (t.tif? && appears_free_in(x, t.b)) ||
  /* fold */   (t.tfold? && appears_free_in(x, t.tf)) ||
  /* unfold */ (t.tunfold? && appears_free_in(x, t.tu))
}

function ty_appears_free_in(X: nat, T: ty): bool
{
  /* Bool */
  /* Var */     (T.TVar? && T.id==X) ||
  /* Arrow1 */  (T.TArrow? && ty_appears_free_in(X, T.paramT)) ||
  /* Arrow2 */  (T.TArrow? && ty_appears_free_in(X, T.bodyT)) ||
  /* Rec */     (T.TRec? && T.X!=X && ty_appears_free_in(X, T.T))
}

function closed(t: tm): bool
{
  forall x: nat :: !appears_free_in(x, t)
}

function ty_closed(T: ty): bool
{
  forall X: nat :: !ty_appears_free_in(X, T)
}

ghost method lemma_free_in_context(c: context, x: nat, t: tm)
  requires ty_closed_ctx(c.m);
  requires appears_free_in(x, t);
  requires has_type(c, t).Some?;
  ensures find(c.m, x).Some?;
  ensures has_type(c, t).Some?;
  decreases t;
{
  if (t.tabs?) {
    assert t.x != x;
    assert has_type(Context(Extend(t.x, t.T, c.m)), t.body).Some?;
    lemma_free_in_context(Context(Extend(t.x, t.T, c.m)), x, t.body);
    assert find(Extend(t.x, t.T, c.m), x).Some?;
  }
}

ghost method corollary_typable_empty__closed(t: tm)
  requires has_type(Context(Empty), t).Some?;
  ensures closed(t);
{
  forall (x: nat)
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
  requires ty_closed_ctx(c.m) && ty_closed_ctx(c'.m);
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

// Multistep

function mstep(t: tm, t': tm, n: nat): bool
  decreases n;
{
  if (n==0) then t == t'
  else step(t).Some? && mstep(step(t).get, t', n-1)
}

// Properties of multistep

ghost method lemma_mstep_trans(t1: tm, t2: tm, t3: tm, n12: nat, n23: nat)
  requires mstep(t1, t2, n12);
  requires mstep(t2, t3, n23);
  ensures mstep(t1, t3, n12+n23);
  decreases n12+n23;
{
  if (n12>0) {
    lemma_mstep_trans(step(t1).get, t2, t3, n12-1, n23);
  } else if (n23>0) {
    lemma_mstep_trans(step(t1).get, step(t2).get, t3, n12, n23-1);
  }
}

ghost method lemma_mstep_trans'(t1: tm, t2: tm, t3: tm, n12: nat, n13: nat)
  requires n12 <= n13;
  requires mstep(t1, t2, n12);
  requires mstep(t1, t3, n13);
  ensures mstep(t2, t3, n13-n12);
  decreases n12;
{
  if (n12>0 && n13>0) {
    lemma_mstep_trans'(step(t1).get, t2, t3, n12-1, n13-1);
  }
}

// Congruence lemmas on multistep

ghost method lemma_mstep_if_c(c: tm, a: tm, b: tm, c': tm, ci: nat)
  requires mstep(c, c', ci);
  ensures mstep(tif(c, a, b), tif(c', a, b), ci);
  decreases ci;
{
  if (ci>0) {
    lemma_mstep_if_c(step(c).get, a, b, c', ci-1);
  }
}

ghost method lemma_mstep_app_f(f: tm, arg: tm, f': tm, fi: nat)
  requires mstep(f, f', fi);
  ensures mstep(tapp(f, arg), tapp(f', arg), fi);
  decreases fi;
{
  if (fi>0) {
    lemma_mstep_app_f(step(f).get, arg, f', fi-1);
  }
}

ghost method lemma_mstep_app_arg(f: tm, arg: tm, arg': tm, argi: nat)
  requires value(f);
  requires mstep(arg, arg', argi);
  ensures mstep(tapp(f, arg), tapp(f, arg'), argi);
  decreases argi;
{
  if (argi>0) {
    lemma_mstep_app_arg(f, step(arg).get, arg', argi-1);
  }
}

ghost method lemma_mstep_fold_tf(U: ty, tf: tm, tf': tm, tfi: nat)
  requires mstep(tf, tf', tfi);
  ensures mstep(tfold(U, tf), tfold(U, tf'), tfi);
  decreases tfi;
{
  if (tfi>0) {
    lemma_mstep_fold_tf(U, step(tf).get, tf', tfi-1);
  }
}

ghost method lemma_mstep_unfold_tu(U: ty, tu: tm, tu': tm, tui: nat)
  requires mstep(tu, tu', tui);
  ensures mstep(tunfold(U, tu), tunfold(U, tu'), tui);
  decreases tui;
{
  if (tui>0) {
    lemma_mstep_unfold_tu(U, step(tu).get, tu', tui-1);
  }
}

ghost method lemma_if_irred__c_mstep_irred(c: tm, a: tm, b: tm, t': tm, i: nat) returns (c': tm, ci: nat)
  requires mstep(tif(c, a, b), t', i);
  requires irred(t');
  ensures ci<=i && mstep(c, c', ci) && irred(c');
  decreases i;
{
  if (irred(c)) {
    c' := c;
    ci := 0;
  } else {
    assert step(c).Some?;
    assert step(tif(c, a, b)) == Some(tif(step(c).get, a, b));
    lemma_mstep_trans'(tif(c, a, b), tif(step(c).get, a, b), t', 1, i);
    assert mstep(tif(step(c).get, a, b), t', i-1);
    var c'', ci' := lemma_if_irred__c_mstep_irred(step(c).get, a, b, t', i-1);
    assert mstep(step(c).get, c'', ci');
    lemma_mstep_trans(c, step(c).get, c'', 1, ci');
    c' := c'';
    ci := ci'+1;
  }
}

ghost method lemma_app_irred__f_mstep_irred(f: tm, arg: tm, t': tm, i: nat) returns (f': tm, fi: nat)
  requires mstep(tapp(f, arg), t', i);
  requires irred(t');
  ensures fi<=i && mstep(f, f', fi) && irred(f');
  decreases i;
{
  if (irred(f)) {
    f' := f;
    fi := 0;
  } else {
    assert step(f).Some?;
    assert step(tapp(f, arg)) == Some(tapp(step(f).get, arg));
    lemma_mstep_trans'(tapp(f, arg), tapp(step(f).get, arg), t', 1, i);
    assert mstep(tapp(step(f).get, arg), t', i-1);
    var f'', fi' := lemma_app_irred__f_mstep_irred(step(f).get, arg, t', i-1);
    assert mstep(step(f).get, f'', fi');
    lemma_mstep_trans(f, step(f).get, f'', 1, fi');
    f' := f'';
    fi := fi'+1;
  }
}

ghost method lemma_app_irred__arg_mstep_irred(f: tm, arg: tm, t': tm, i: nat) returns (arg': tm, argi: nat)
  requires mstep(tapp(f, arg), t', i);
  requires irred(t');
  requires value(f);
  ensures argi<=i && mstep(arg, arg', argi) && irred(arg');
  decreases i;
{
  if (irred(arg)) {
    arg' := arg;
    argi := 0;
  } else {
    assert step(arg).Some?;
    assert step(tapp(f, arg)) == Some(tapp(f, step(arg).get));
    lemma_mstep_trans'(tapp(f, arg), tapp(f, step(arg).get), t', 1, i);
    assert mstep(tapp(f, step(arg).get), t', i-1);
    var arg'', argi' := lemma_app_irred__arg_mstep_irred(f, step(arg).get, t', i-1);
    assert mstep(step(arg).get, arg'', argi');
    lemma_mstep_trans(arg, step(arg).get, arg'', 1, argi');
    arg' := arg'';
    argi := argi'+1;
  }
}

ghost method lemma_fold_irred__tf_mstep_irred(U: ty, tf: tm, t': tm, i: nat) returns (tf': tm, tfi: nat)
  requires mstep(tfold(U, tf), t', i);
  requires irred(t');
  ensures tfi<=i && mstep(tf, tf', tfi) && irred(tf');
  decreases i;
{
  if (irred(tf)) {
    tf' := tf;
    tfi := 0;
  } else {
    assert step(tf).Some?;
    assert step(tfold(U, tf)) == Some(tfold(U, step(tf).get));
    lemma_mstep_trans'(tfold(U, tf), tfold(U, step(tf).get), t', 1, i);
    assert mstep(tfold(U, step(tf).get), t', i-1);
    var tf'', tfi' := lemma_fold_irred__tf_mstep_irred(U, step(tf).get, t', i-1);
    assert mstep(step(tf).get, tf'', tfi');
    lemma_mstep_trans(tf, step(tf).get, tf'', 1, tfi');
    tf' := tf'';
    tfi := tfi'+1;
  }
}

ghost method lemma_unfold_irred__tu_mstep_irred(U: ty, tu: tm, t': tm, i: nat) returns (tu': tm, tui: nat)
  requires mstep(tunfold(U, tu), t', i);
  requires irred(t');
  ensures tui<=i && mstep(tu, tu', tui) && irred(tu');
  decreases i;
{
  if (irred(tu)) {
    tu' := tu;
    tui := 0;
  } else {
    assert step(tu).Some?;
    assert step(tunfold(U, tu)) == Some(tunfold(U, step(tu).get));
    lemma_mstep_trans'(tunfold(U, tu), tunfold(U, step(tu).get), t', 1, i);
    assert mstep(tunfold(U, step(tu).get), t', i-1);
    var tu'', tui' := lemma_unfold_irred__tu_mstep_irred(U, step(tu).get, t', i-1);
    assert mstep(step(tu).get, tu'', tui');
    lemma_mstep_trans(tu, step(tu).get, tu'', 1, tui');
    tu' := tu'';
    tui := tui'+1;
  }
}

// Closed terms (multi)step to closed terms.

ghost method lemma_if_closed(c: tm, a: tm, b: tm)
  requires closed(tif(c, a, b));
  ensures closed(c) && closed(a) && closed(b);
{
  if (!closed(c)) {
    assert exists x:nat :: appears_free_in(x, c);
    forall (x:nat | appears_free_in(x, c))
      ensures appears_free_in(x, tif(c, a, b));
    {
    }
    assert exists x:nat :: appears_free_in(x, tif(c, a, b));
    assert false;
  }
  if (!closed(a)) {
    assert exists x:nat :: appears_free_in(x, a);
    forall (x:nat | appears_free_in(x, a))
      ensures appears_free_in(x, tif(c, a, b));
    {
    }
    assert exists x:nat :: appears_free_in(x, tif(c, a, b));
    assert false;
  }
  if (!closed(b)) {
    assert exists x:nat :: appears_free_in(x, b);
    forall (x:nat | appears_free_in(x, b))
      ensures appears_free_in(x, tif(c, a, b));
    {
    }
    assert exists x:nat :: appears_free_in(x, tif(c, a, b));
    assert false;
  }
}

ghost method lemma_app_closed(f: tm, arg: tm)
  requires closed(tapp(f, arg));
  ensures closed(f) && closed(arg);
{
  if (!closed(f)) {
    assert exists x:nat :: appears_free_in(x, f);
    forall (x:nat | appears_free_in(x, f))
      ensures appears_free_in(x, tapp(f, arg));
    {
    }
    assert exists x:nat :: appears_free_in(x, tapp(f, arg));
    assert false;
  }
  if (!closed(arg)) {
    assert exists x:nat :: appears_free_in(x, arg);
    forall (x:nat | appears_free_in(x, arg))
      ensures appears_free_in(x, tapp(f, arg));
    {
    }
    assert exists x:nat :: appears_free_in(x, tapp(f, arg));
    assert false;
  }
}

ghost method lemma_abs_closed(x: nat, T: ty, t: tm, y: nat)
  requires closed(tabs(x, T, t));
  requires y!=x;
  ensures !appears_free_in(y, t);
{
  assert forall z:nat :: !appears_free_in(z, tabs(x, T, t));
  forall (z:nat)
    ensures z==x || !appears_free_in(z, t);
  {
    if (z!=x) {
      assert !appears_free_in(z, tabs(x, T, t));
      assert !appears_free_in(z, t);
    }
  }
}

ghost method lemma_fold_closed(U: ty, t1: tm)
  requires closed(tfold(U, t1));
  ensures closed(t1);
{
  if (!closed(t1)) {
    assert exists x:nat :: appears_free_in(x, t1);
    forall (x:nat | appears_free_in(x, t1))
      ensures appears_free_in(x, tfold(U, t1));
    {
    }
    assert exists x:nat :: appears_free_in(x, tfold(U, t1));
    assert false;
  }
}

ghost method lemma_unfold_closed(U: ty, t1: tm)
  requires closed(tunfold(U, t1));
  ensures closed(t1);
{
  if (!closed(t1)) {
    assert exists x:nat :: appears_free_in(x, t1);
    forall (x:nat | appears_free_in(x, t1))
      ensures appears_free_in(x, tunfold(U, t1));
    {
    }
    assert exists x:nat :: appears_free_in(x, tunfold(U, t1));
    assert false;
  }
}

ghost method lemma_Arrow_ty_closed(T1: ty, T2: ty)
  requires ty_closed(TArrow(T1, T2));
  ensures ty_closed(T1) && ty_closed(T2);
{
  if (!ty_closed(T1)) {
    assert exists X:nat :: ty_appears_free_in(X, T1);
    forall (X:nat | ty_appears_free_in(X, T1))
      ensures ty_appears_free_in(X, TArrow(T1, T2));
    {
    }
    assert exists X:nat :: ty_appears_free_in(X, TArrow(T1, T2));
    assert false;
  }
  if (!ty_closed(T2)) {
    assert exists X:nat :: ty_appears_free_in(X, T2);
    forall (X:nat | ty_appears_free_in(X, T2))
      ensures ty_appears_free_in(X, TArrow(T1, T2));
    {
    }
    assert exists X:nat :: ty_appears_free_in(X, TArrow(T1, T2));
    assert false;
  }
}

ghost method lemma_Rec_ty_closed_any(X: nat, T: ty, Y: nat)
  requires ty_closed(TRec(X, T));
  requires X!=Y;
  ensures !ty_appears_free_in(Y, T);
{
  assert !ty_appears_free_in(Y, TRec(X, T));
}

ghost method lemma_Rec_ty_closed(X: nat, T: ty)
  requires ty_closed(TRec(X, T));
  ensures ty_closed(tsubst(X, TRec(X, T), T));
{
  forall (Y:nat)
    ensures !ty_appears_free_in(Y, tsubst(X, TRec(X, T), T));
  {
    if (Y==X) {
      lemma_tsubst_tafi'(X, TRec(X, T), T);
    } else {
      lemma_Rec_ty_closed_any(X, T, Y);
      lemma_tsubst_tafi''(X, TRec(X, T), T, Y);
    }
  }
}

ghost method lemma_subst_afi(x: nat, v: tm, t: tm, y: nat)
  requires closed(v);
  requires x!=y;
  requires !appears_free_in(y, subst(x, v, t));
  ensures !appears_free_in(y, t);
{
}

ghost method lemma_subst_afi'(x: nat, v: tm, t: tm)
  requires closed(v);
  ensures !appears_free_in(x, subst(x, v, t));
{
}

ghost method lemma_subst_afi''(x: nat, v: tm, t: tm, y: nat)
  requires !appears_free_in(y, t);
  requires closed(v);
  ensures !appears_free_in(y, subst(x, v, t));
{
}

ghost method lemma_tsubst_tafi(X: nat, V: ty, T: ty, Y: nat)
  requires ty_closed(V);
  requires X!=Y;
  requires !ty_appears_free_in(Y, tsubst(X, V, T));
  ensures !ty_appears_free_in(Y, T);
{
}

ghost method lemma_tsubst_tafi'(X: nat, V: ty, T: ty)
  requires ty_closed(V);
  ensures !ty_appears_free_in(X, tsubst(X, V, T));
{
}

ghost method lemma_tsubst_tafi''(X: nat, V: ty, T: ty, Y: nat)
  requires !ty_appears_free_in(Y, T);
  requires ty_closed(V);
  ensures !ty_appears_free_in(Y, tsubst(X, V, T));
{
}

ghost method lemma_step_preserves_closed(t: tm, t': tm)
  requires closed(t);
  requires step(t) == Some(t');
  ensures closed(t');
  decreases t;
{
  /* AppAbs */
  if (t.tapp? && t.f.tabs? && value(t.arg)) {
    assert t' == subst(t.f.x, t.arg, t.f.body);
    lemma_app_closed(t.f, t.arg);
    forall (y:nat)
      ensures !appears_free_in(y, t');
    {
      if (y==t.f.x) {
        lemma_subst_afi'(y, t.arg, t.f.body);
        assert !appears_free_in(y, t');
      } else {
        lemma_abs_closed(t.f.x, t.f.T, t.f.body, y);
        assert !appears_free_in(y, t.f.body);
        lemma_subst_afi''(t.f.x, t.arg, t.f.body, y);
        assert !appears_free_in(y, t');
      }
    }
    assert closed(t');
  }
  /* App1 */
  else if (t.tapp? && step(t.f).Some?) {
    assert t' == tapp(step(t.f).get, t.arg);
    lemma_app_closed(t.f, t.arg);
    lemma_step_preserves_closed(t.f, step(t.f).get);
    assert closed(t');
  }
  /* App2 */
  else if (t.tapp? && step(t.arg).Some?) {
    assert t' == tapp(t.f, step(t.arg).get);
    lemma_app_closed(t.f, t.arg);
    lemma_step_preserves_closed(t.arg, step(t.arg).get);
    assert closed(t');
  }
  /* IfTrue */
  else if (t.tif? && t.c == ttrue) {
    assert t' == t.a;
    lemma_if_closed(t.c, t.a, t.b);
    assert closed(t');
  }
  /* IfFalse */
  else if (t.tif? && t.c == tfalse) {
    assert t' == t.b;
    lemma_if_closed(t.c, t.a, t.b);
    assert closed(t');
  }
  /* If */
  else if (t.tif? && step(t.c).Some?) {
    assert t' == tif(step(t.c).get, t.a, t.b);
    lemma_if_closed(t.c, t.a, t.b);
    lemma_step_preserves_closed(t.c, step(t.c).get);
    assert closed(t');
  }
  /* UnfoldFold */
  else if (t.tunfold? && t.tu.tfold? && value(t.tu.tf)) {
    assert t' == t.tu.tf;
    lemma_unfold_closed(t.Tu, t.tu);
    lemma_fold_closed(t.tu.Tf, t.tu.tf);
    assert closed(t');
  }
  /* Fold */
  else if (t.tfold? && step(t.tf).Some?) {
    assert t' == tfold(t.Tf, step(t.tf).get);
    lemma_fold_closed(t.Tf, t.tf);
    lemma_step_preserves_closed(t.tf, step(t.tf).get);
    assert closed(t');
  }
  /* Unfold */
  else if (t.tunfold? && step(t.tu).Some?) {
    assert t' == tunfold(t.Tu, step(t.tu).get);
    lemma_unfold_closed(t.Tu, t.tu);
    lemma_step_preserves_closed(t.tu, step(t.tu).get);
    assert closed(t');
  }
}

ghost method lemma_multistep_preserves_closed(t: tm, t': tm, i: nat)
  requires closed(t);
  requires mstep(t, t', i);
  ensures closed(t');
  decreases i;
{
  if (i > 0) {
    lemma_step_preserves_closed(t, step(t).get);
    lemma_multistep_preserves_closed(step(t).get, t', i-1);
  }
}

// Multisubstitutions, multi-extensions, and instantiations

function msubst(e: partial_map<tm>, t: tm): tm
{
  match e
  case Empty => t
  case Extend(x, v, e') => msubst(e', subst(x, v, t))
}

function mextend<X>(init: partial_map<X>, c: partial_map<X>): partial_map<X>
{
  match c
  case Empty => init
  case Extend(x, v, c') => Extend(x, v, mextend(init, c'))
}

function lookup<X>(n: nat, nxs: partial_map<X>): option<X>
{
  find(nxs, n)
}

function drop<X>(n: nat, nxs: partial_map<X>): partial_map<X>
{
  match nxs
  case Empty => Empty
  case Extend(n', x, nxs') =>
    if (n'==n) then drop(n, nxs') else Extend(n', x, drop(n, nxs'))
}

// More substitution facts

ghost method lemma_vacuous_substitution(t: tm, x: nat)
  requires !appears_free_in(x, t);
  ensures forall t' :: subst(x, t', t) == t;
{
}

ghost method lemma_subst_closed(t: tm)
  requires closed(t);
  ensures forall x:nat, t' :: subst(x, t', t) == t;
{
  forall (x:nat)
    ensures forall t' :: subst(x, t', t) == t;
  {
    lemma_vacuous_substitution(t, x);
  }
}

ghost method lemma_subst_not_afi(t: tm, x: nat, v: tm)
  requires closed(v);
  ensures !appears_free_in(x, subst(x, v, t));
{
}

ghost method lemma_duplicate_subst(t': tm, x: nat, t: tm, v: tm)
  requires closed(v);
  ensures subst(x, t, subst(x, v, t')) == subst(x, v, t');
{
  lemma_subst_not_afi(t', x, v);
  lemma_vacuous_substitution(subst(x, v, t'), x);
}

ghost method lemma_swap_subst(t: tm, x: nat, x1: nat, v: tm, v1: tm)
  requires x != x1;
  requires closed(v);
  requires closed(v1);
  ensures subst(x1, v1, subst(x, v, t)) == subst(x, v, subst(x1, v1, t));
{
  if (t.tvar?) {
    if (t.id==x) {
      lemma_subst_closed(v);
    }
    if (t.id==x1) {
      lemma_subst_closed(v1);
    }
  }
}

// Properties of multi-substitutions

ghost method lemma_msubst_closed_any(t: tm, e: partial_map<tm>)
  requires closed(t);
  ensures msubst(e, t) == t;
{
  match e {
  case Empty =>
  case Extend(x, v, e') =>
    lemma_subst_closed(t);
    lemma_msubst_closed_any(t, e');
  }
}

ghost method lemma_msubst_closed(t: tm)
  requires closed(t);
  ensures forall e :: msubst(e, t) == t;
{
  forall (e: partial_map<tm>)
    ensures msubst(e, t) == t;
  {
    lemma_msubst_closed_any(t, e);
  }
}

function closed_env(e: partial_map<tm>): bool
{
  match e
  case Empty => true
  case Extend(x, t, e') => closed(t) && closed_env(e')
}

function ty_closed_ctx(c: partial_map<ty>): bool
{
  match c
  case Empty => true
  case Extend(x, T, c') => ty_closed(T) && ty_closed_ctx(c')
}

ghost method lemma_ctx_ty_closed_finds_ty_closed(c: partial_map<ty>, x: nat, T: ty)
  requires ty_closed_ctx(c);
  requires find(c, x) == Some(T);
  ensures ty_closed(T);
{
  match c {
  case Empty => assert false;
  case Extend(x', T', c') =>
    if (x'!=x) {
      lemma_ctx_ty_closed_finds_ty_closed(c', x, T);
    }
  }
}

ghost method lemma_subst_msubst(e: partial_map<tm>, x: nat, v: tm, t: tm)
  requires closed(v);
  requires closed_env(e);
  ensures msubst(e, subst(x, v, t)) == subst(x, v, msubst(drop(x, e), t));
{
  match e {
  case Empty =>
  case Extend(x', v', e') =>
    if (x==x') {
      lemma_duplicate_subst(t, x, v', v);
    }
    else {
      lemma_swap_subst(t, x, x', v, v');
    }
  }
}

ghost method lemma_msubst_var(e: partial_map<tm>, x: nat)
  requires closed_env(e);
  ensures lookup(x, e).None? ==> msubst(e, tvar(x)) == tvar(x);
  ensures lookup(x, e).Some? ==> msubst(e, tvar(x)) == lookup(x, e).get;
{
  match e {
  case Empty =>
  case Extend(x', t, e) =>
    if (x'==x) {
      lemma_msubst_closed(t);
    }
  }
}

ghost method lemma_msubst_abs(e: partial_map<tm>, x: nat, T: ty, t: tm)
  ensures msubst(e, tabs(x, T, t)) == tabs(x, T, msubst(drop(x, e), t));
{
  match e {
  case Empty =>
  case Extend(x', t', e') =>
  }
}

ghost method lemma_msubst_app(e: partial_map<tm>, t1: tm, t2: tm)
  ensures msubst(e, tapp(t1, t2)) == tapp(msubst(e, t1), msubst(e, t2));
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
  }
}

ghost method lemma_msubst_true(e: partial_map<tm>)
  ensures msubst(e, ttrue) == ttrue;
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
  }
}

ghost method lemma_msubst_false(e: partial_map<tm>)
  ensures msubst(e, tfalse) == tfalse;
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
  }
}

ghost method lemma_msubst_if(e: partial_map<tm>, c: tm, a: tm, b: tm)
  ensures msubst(e, tif(c, a, b)) == tif(msubst(e, c), msubst(e, a), msubst(e, b));
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
  }
}

ghost method lemma_msubst_fold(e: partial_map<tm>, U: ty, t1: tm)
  ensures msubst(e, tfold(U, t1)) == tfold(U, msubst(e, t1));
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
  }
}

ghost method lemma_msubst_unfold(e: partial_map<tm>, U: ty, t1: tm)
  ensures msubst(e, tunfold(U, t1)) == tunfold(U, msubst(e, t1));
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
  }
}

// Properties of multi-extensions

ghost method lemma_mextend(c: partial_map<ty>)
  ensures mextend(Empty, c) == c;
{
}

ghost method lemma_mextend_lookup(c: partial_map<ty>, x: nat)
  ensures lookup(x, c) == lookup(x, mextend(Empty, c));
{
}

ghost method lemma_mextend_drop(c: partial_map<ty>, init: partial_map<ty>, x: nat, x': nat)
  ensures lookup(x', mextend(init, drop(x, c))) == if x==x' then lookup(x', init) else lookup(x', mextend(init, c));
{
}

ghost method lemma_closed_env__closed_lookup(e: partial_map<tm>, x: nat)
  requires closed_env(e);
  requires lookup(x, e).Some?;
  ensures closed(lookup(x, e).get);
{
  match e {
  case Empty => assert false;
  case Extend(x', v', e') =>
    if (x'==x) {
      assert closed(v');
    } else {
      lemma_closed_env__closed_lookup(e', x);
    }
  }
}

// Type-Safety states that a well-typed term cannot get stuck:
predicate type_safety(t: tm)
{
  has_type(Context(Empty), t).Some? ==>
  forall t', n:nat :: mstep(t, t', n) ==>
  value(t') || step(t').Some?
}
// Note that this statement is generally stronger than progress, which is only the case n==0, and
// weaker than progress+preservation, which requires typing intermediary terms.

// How do we get a strong enough induction hypothesis for type-safety without preservation?
// Logical relations!
// The slogan: "Give me related inputs, I'll give you related outputs."

// We define two mutually recursive monotonic logical relations
// which captures what it means to have type T when taking at most k step:
// V_k(T, t) for values and E_k(T, t) for terms.

// V_k(T, t) is by structural induction over T
predicate V(T: ty, t: tm, k: nat)
  decreases k, T;
{
  match T
  case TBool => t==ttrue || t==tfalse
  case TArrow(T1, T2) => t.tabs? && (forall j:nat, v :: j <= k ==> closed(v) && V(T1, v, j) ==> E(T2, subst(t.x, v, t.body), j))
  case TVar(id) => false
  case TRec(X, T1) => t.tfold? && value(t) && (forall j:nat :: j<k ==> V(tsubst(X, T, T1), t.tf, j))
}

// We can fabricate values v in V_0(T, v).
ghost method make_V0(T: ty) returns (v: tm)
  requires ty_closed(T);
  ensures closed(v);
  ensures V(T, v, 0);
  decreases T;
{
  match T {
  case TBool =>
    v := ttrue;
  case TArrow(T1, T2) =>
    lemma_Arrow_ty_closed(T1, T2);
    var v' := make_V0(T2);
    v := tabs(0, T1, v');
  case TRec(X, T1) =>
    v := tfold(T, ttrue);
    assert value(v);
  case TVar(id) =>
    assert ty_appears_free_in(id, T);
    assert false;
  }
}

predicate E(T: ty, t: tm, k: nat)
  decreases k, T;
{
  if (k == 0) then true
  else forall i:nat, j:nat, t' :: i+j<k ==> mstep(t, t', i) && irred(t') ==> V(T, t', j)
}

// Since Dafny </3 quantifiers, let's extract/repeat the relevant tidbits from the relations:

ghost method lemma_E(T: ty, t: tm, k: nat, i: nat, j: nat, t': tm)
  requires E(T, t, k);
  requires i+j<k;
  requires mstep(t, t', i);
  ensures irred(t') ==> V(T, t', j);
{
}

ghost method lemma_V_value(T: ty, t: tm, k: nat)
  requires V(T, t, k);
  ensures value(t);
{
}

ghost method lemma_V_arrow(T1: ty, T2: ty, x: nat, body: tm, v: tm, k: nat, j: nat)
  requires V(TArrow(T1, T2), tabs(x, T1, body), k);
  requires j <= k;
  requires closed(v) && V(T1, v, j);
  ensures E(T2, subst(x, v, body), j);
{
}

ghost method lemma_V_rec(X: nat, T1: ty, v: tm, k: nat, j: nat)
  requires V(TRec(X, T1), tfold(TRec(X, T1), v), k);
  requires value(v);
  requires j<k;
  ensures V(tsubst(X, TRec(X, T1), T1), v, j);
{
}

// The logical relations V_k(T, t) and E_k(T, t) is only meant for _closed_ terms.

// Let's get around this by defining a logical relation for contexts g_k(c, e).
predicate g(c: partial_map<ty>, e: partial_map<tm>, k: nat)
{
  match c
  case Empty => e.Empty?
  case Extend(x, T, c') =>
    match e
    case Empty => false
    case Extend(x', v, e') => x==x' && closed(v) && V(T, v, k) && g(c', e', k)
}

// For step-indexed logical relations, we need to verify that the relations are monotonic / downward closed.

ghost method lemma_V_monotonic(T: ty, v: tm, k: nat, j: nat)
  requires V(T, v, k);
  requires j <= k;
  ensures V(T, v, j);
{
}

ghost method lemma_E_monotonic(T: ty, v: tm, k: nat, j: nat)
  requires E(T, v, k);
  requires j <= k;
  ensures E(T, v, j);
{
  if (k > 0) {

  }
}

ghost method lemma_g_monotonic(c: partial_map<ty>, e: partial_map<tm>, k: nat, j: nat)
  requires g(c, e, k);
  requires j <= k;
  ensures g(c, e, j);
{
  match c {
  case Empty =>
  case Extend(x', T, c') =>
    match e {
    case Empty =>
    case Extend(xe, v, e') =>
      lemma_V_monotonic(T, v, k, j);
      lemma_g_monotonic(c', e', k, j);
    }
  }
}


// Some properties of g_k(c, e), very similar to instantiation properties in Norm.dfy

ghost method lemma_g_env_closed(c: partial_map<ty>, e: partial_map<tm>, k: nat)
  requires g(c, e, k);
  ensures closed_env(e);
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
    match c {
      case Empty =>
      case Extend(x', T, c') =>
        assert closed(t);
        lemma_g_env_closed(c', e', k);
    }
  }
}

ghost method lemma_g_V(c: partial_map<ty>, e: partial_map<tm>, k: nat, x: nat, t: tm, T: ty)
  requires g(c, e, k);
  requires lookup(x, c) == Some(T);
  requires lookup(x, e) == Some(t);
  ensures V(T, t, k);
{
  match e {
  case Empty =>
  case Extend(x', t', e') =>
    match c {
    case Empty =>
    case Extend(x'', T', c') =>
      assert x'==x'';
      if (x==x') {
      }
      else {
        lemma_g_V(c', e', k, x, t, T);
      }
    }
  }
}

ghost method lemma_g_domains_match_any(c: partial_map<ty>, e: partial_map<tm>, k: nat, x: nat)
  requires g(c, e, k);
  requires lookup(x, c).Some?;
  ensures lookup(x, e).Some?;
{
  match c {
  case Empty =>
  case Extend(x', T, c') =>
    match e {
    case Empty =>
    case Extend(xe, t, e') =>
      assert x'==xe;
      if (x!=x') {
        lemma_g_domains_match_any(c', e', k, x);
      }
    }
  }
}

ghost method lemma_g_domains_match(c: partial_map<ty>, e: partial_map<tm>, k: nat)
  requires g(c, e, k);
  ensures forall x:nat :: lookup(x, c).Some? ==> lookup(x, e).Some?;
{
  forall (x:nat | lookup(x, c).Some?)
    ensures lookup(x, e).Some?;
  {
    lemma_g_domains_match_any(c, e, k, x);
  }
}

ghost method lemma_g_drop_any(c: partial_map<ty>, e: partial_map<tm>, k: nat, x: nat)
  requires g(c, e, k);
  ensures g(drop(x, c), drop(x, e), k);
{
  match e {
  case Empty =>
    assert drop(x, e) == e;
    match c {
    case Empty =>
      assert drop(x, c) == c;
    case Extend(x'', T', c') =>
    }
  case Extend(x', t', e') =>
    match c {
    case Empty =>
    case Extend(x'', T', c') =>
      assert x'==x'';
      lemma_g_drop_any(c', e', k, x);
    }
  }
}

ghost method lemma_g_drop(c: partial_map<ty>, e: partial_map<tm>, k: nat)
  requires g(c, e, k);
  ensures forall x:nat :: g(drop(x, c), drop(x, e), k);
{
  forall (x:nat)
    ensures g(drop(x, c), drop(x, e), k);
  {
    lemma_g_drop_any(c, e, k, x);
  }
}

ghost method lemma_typable__ty_closed(c: partial_map<ty>, t: tm, T: ty)
  requires ty_closed_ctx(c);
  requires has_type(Context(c), t) == Some(T);
  ensures ty_closed(T);
  decreases t;
{
  match t {
  case tvar(id) =>
    lemma_ctx_ty_closed_finds_ty_closed(c, id, T);
  case tabs(x, T1, body) =>
    lemma_typable__ty_closed(Extend(x, T1, c), body, T.bodyT);
  case tapp(f, arg) =>
    var ty_f := has_type(Context(c), f).get;
    lemma_typable__ty_closed(c, f, ty_f);
    lemma_Arrow_ty_closed(ty_f.paramT, ty_f.bodyT);
  case ttrue =>
  case tfalse =>
  case tif(cond, a, b) =>
    var ty_a := has_type(Context(c), a).get;
    lemma_typable__ty_closed(c, a, ty_a);
  case tfold(U, t1) =>
  case tunfold(U, t1) =>
    lemma_Rec_ty_closed(U.X, U.T);
  }
}

ghost method lemma_g_msubst_closed(c: partial_map<ty>, e: partial_map<tm>, k: nat, t: tm, T: ty)
  requires ty_closed_ctx(c);
  requires has_type(Context(c), t) == Some(T);
  requires g(c, e, k);
  ensures closed(msubst(e, t));
  decreases t;
{
  match t {
  case tvar(id) =>
    lemma_g_env_closed(c, e, k);
    lemma_g_domains_match(c, e, k);
    lemma_msubst_var(e, id);
    lemma_closed_env__closed_lookup(e, id);
  case tabs(x, T1, body) =>
    var c' := Extend(x, T1, c);
    lemma_g_monotonic(c, e, k, 0);
    var v := make_V0(T1);
    var e' := Extend(x, v, e);
    assert has_type(Context(c'), body) == Some(T.bodyT);
    lemma_g_msubst_closed(c', e', 0, body, T.bodyT);
    lemma_g_env_closed(c, e, k);
    lemma_subst_msubst(e, x, v, body);
    forall (y:nat | y!=x)
      ensures !appears_free_in(y, msubst(drop(x, e), body));
    {
      lemma_subst_afi(x, v, msubst(drop(x, e), body), y);
    }
    lemma_msubst_abs(e, x, T1, body);
  case tapp(f, arg) =>
    lemma_g_msubst_closed(c, e, k, f, has_type(Context(c), f).get);
    lemma_g_msubst_closed(c, e, k, arg, has_type(Context(c), arg).get);
    lemma_msubst_app(e, f, arg);
  case ttrue =>
    lemma_msubst_true(e);
  case tfalse =>
    lemma_msubst_false(e);
  case tif(cond, a, b) =>
    lemma_g_msubst_closed(c, e, k, cond, has_type(Context(c), cond).get);
    lemma_g_msubst_closed(c, e, k, a, has_type(Context(c), a).get);
    lemma_g_msubst_closed(c, e, k, b, has_type(Context(c), b).get);
    lemma_msubst_if(e, cond, a, b);
  case tfold(U, t1) =>
    lemma_g_msubst_closed(c, e, k, t1, has_type(Context(c), t1).get);
    lemma_msubst_fold(e, U, t1);
  case tunfold(U, t1) =>
    lemma_g_msubst_closed(c, e, k, t1, has_type(Context(c), t1).get);
    lemma_msubst_unfold(e, U, t1);
  }
}

// We're now ready to define our all-encompassing logical relation R(c, t, T).
predicate R(c: partial_map<ty>, t: tm, T: ty)
{
  forall e, k:nat :: g(c, e, k) ==> E(T, msubst(e, t), k)
}

ghost method lemma_R(c: partial_map<ty>, e: partial_map<tm>, k: nat, t: tm, T: ty)
  requires g(c, e, k);
  requires R(c, t, T);
  ensures E(T, msubst(e, t), k);
{
}

// We separate out and break down the app case, to avoid timeouts in the IDE.
ghost method theorem_fundamental_R_app_f(Tf: ty, mt: tm, mf: tm, marg: tm, t': tm, k: nat, i: nat, j: nat) returns (f': tm, fi: nat)
  requires mstep(tapp(mf, marg), t', i);
  requires mstep(mt, t', i);
  requires mt==tapp(mf, marg);
  requires irred(t');
  requires E(Tf, mf, k);
  requires i+j<k;
  requires Tf.TArrow?;
  ensures fi<=i;
  ensures mstep(tapp(f', marg), t', i-fi);
  ensures value(f');
  ensures f'.tabs?;
  ensures V(Tf, f', j+i-fi);
{
  f', fi := lemma_app_irred__f_mstep_irred(mf, marg, t', i);
  lemma_E(Tf, mf, k, fi, j+i-fi, f');
  lemma_V_value(Tf, f', j+i-fi);

  lemma_mstep_app_f(mf, marg, f', fi);
  lemma_mstep_trans'(mt, tapp(f', marg), t', fi, i);
}

ghost method theorem_fundamental_R_app(c: partial_map<ty>, e: partial_map<tm>, k: nat, f: tm, arg: tm, Tf: ty, Targ: ty)
  requires E(Tf, msubst(e, f), k);
  requires E(Targ, msubst(e, arg), k);
  requires closed(msubst(e, arg));
  requires Tf.TArrow? && Tf.paramT == Targ;
  ensures E(Tf.bodyT, msubst(e, tapp(f, arg)), k);
{
  var t := tapp(f, arg);
  var T := Tf.bodyT;
  lemma_msubst_app(e, f, arg);
  var mf := msubst(e, f);
  var marg := msubst(e, arg);
  var mt := msubst(e, t);

  forall (i:nat, j:nat, t' | i+j<k && mstep(mt, t', i) && irred(t'))
    ensures V(T, t', j);
  {
    var f', fi := theorem_fundamental_R_app_f(Tf, mt, mf, marg, t', k, i, j);

    var arg', argi := lemma_app_irred__arg_mstep_irred(f', marg, t', i-fi);
    lemma_E(Targ, marg, k, argi, j+i-fi-argi, arg');
    lemma_V_value(Targ, arg', j+i-fi-argi);

    lemma_multistep_preserves_closed(marg, arg', argi);

    lemma_V_arrow(Targ, T, f'.x, f'.body, arg', j+i-fi, j+i-fi-argi);

    lemma_mstep_app_arg(f', marg, arg', argi);
    lemma_mstep_trans'(tapp(f', marg), tapp(f', arg'), t', argi, i-fi);
    lemma_mstep_trans'(tapp(f', arg'), subst(f'.x, arg', f'.body), t', 1, i-fi-argi);

    lemma_E(T, subst(f'.x, arg', f'.body), j+i-fi-argi, i-fi-argi-1, j, t');
  }
  assert E(T, msubst(e, t), k);
}

// The Fundamental Theorem of Logical Relations relates well-typed terms to terms that are in the logical relation:
ghost method theorem_fundamental_R(c: partial_map<ty>, t: tm, T: ty)
  requires ty_closed_ctx(c);
  requires has_type(Context(c), t) == Some(T);
  ensures R(c, t, T);
  decreases t;
{
// The proof is by induction on the typing derivation, which is syntax-directed.
  forall (e, k:nat | g(c, e, k))
    ensures E(T, msubst(e, t), k);
  {
    match t {
    case tvar(id) =>
      lemma_g_env_closed(c, e, k);
      lemma_g_domains_match(c, e, k);
      lemma_msubst_var(e, id);
      lemma_g_V(c, e, k, id, lookup(id, e).get, T);
    case tabs(x, T1, body) =>
      var T2 := T.bodyT;
      var c' := Extend(x, T1, c);
      theorem_fundamental_R(c', body, T2);
      forall (j:nat, v | j<=k && closed(v) && V(T1, v, j))
        ensures E(T2, subst(x, v, msubst(drop(x, e), body)), j);
      {
        var e' := Extend(x, v, e);
        lemma_g_monotonic(c, e, k, j);
        lemma_R(c', e', j, body, T2);
        lemma_g_env_closed(c', e', j);
        lemma_subst_msubst(e, x, v, body);
      }
      assert E(T, tabs(x, T1, msubst(drop(x, e), body)), k);
      lemma_msubst_abs(e, x, T1, body);
    case tapp(f, arg) =>
      var Tf := has_type(Context(c), f).get;
      var Targ := has_type(Context(c), arg).get;
      theorem_fundamental_R(c, f, Tf);
      theorem_fundamental_R(c, arg, Targ);
      lemma_g_msubst_closed(c, e, k, arg, Targ);
      theorem_fundamental_R_app(c, e, k, f, arg, Tf, Targ);
    case ttrue =>
      lemma_msubst_true(e);
    case tfalse =>
      lemma_msubst_false(e);
    case tif(cond, a, b) =>
      theorem_fundamental_R(c, cond, TBool);
      theorem_fundamental_R(c, a, T);
      theorem_fundamental_R(c, b, T);
      lemma_msubst_if(e, cond, a, b);
      var mc := msubst(e, cond);
      var ma := msubst(e, a);
      var mb := msubst(e, b);
      var mt := msubst(e, t);

      forall (i:nat, j:nat, t' | i+j<k && mstep(mt, t', i) && irred(t'))
        ensures V(T, t', j);
      {
        var c', ci := lemma_if_irred__c_mstep_irred(mc, ma, mb, t', i);
        lemma_E(TBool, mc, k, ci, j, c');
        lemma_mstep_if_c(mc, ma, mb, c', ci);
        lemma_mstep_trans'(mt, tif(c', ma, mb), t', ci, i);
        if (c' == ttrue) {
          lemma_mstep_trans'(tif(c', ma, mb), ma, t', 1, i-ci);
          lemma_E(T, ma, k, i-ci-1, j, t');
        } else {
          lemma_mstep_trans'(tif(c', ma, mb), mb, t', 1, i-ci);
          lemma_E(T, mb, k, i-ci-1, j, t');
        }
      }
    case tfold(U, tf) =>
      var Ttf := has_type(Context(c), tf).get;
      theorem_fundamental_R(c, tf, Ttf);
      lemma_msubst_fold(e, U, tf);
      var mt := msubst(e, t);
      var mtf := msubst(e, tf);
      forall (i:nat, j:nat, t' | i+j<k && mstep(mt, t', i) && irred(t'))
        ensures V(T, t', j);
      {
        var tf', tfi := lemma_fold_irred__tf_mstep_irred(U, mtf, t', i);
        lemma_E(Ttf, mtf, k, tfi, j+i-tfi, tf');
        lemma_V_value(Ttf, tf', j+i-tfi);

        lemma_mstep_fold_tf(U, mtf, tf', tfi);
        lemma_mstep_trans'(mt, tfold(U, tf'), t', tfi, i);
      }
    case tunfold(U, tu) =>
      theorem_fundamental_R(c, tu, U);
      lemma_msubst_unfold(e, U, tu);
      var mt := msubst(e, t);
      var mtu := msubst(e, tu);
      forall (i:nat, j:nat, t' | i+j<k && mstep(mt, t', i) && irred(t'))
        ensures V(T, t', j);
      {
        var tu', tui := lemma_unfold_irred__tu_mstep_irred(U, mtu, t', i);
        lemma_E(U, mtu, k, tui, j+i-tui, tu');
        lemma_V_value(U, tu', j+i-tui);

        lemma_mstep_unfold_tu(U, mtu, tu', tui);
        lemma_mstep_trans'(mt, tunfold(U, tu'), t', tui, i);

        lemma_V_rec(U.X, U.T, tu'.tf, i+j-tui, i+j-tui-1);
      }
    }
  }
}

ghost method corollary_type_safety(t: tm)
  ensures type_safety(t);
{
  forall (T | has_type(Context(Empty), t).Some?)
    ensures forall t', n:nat :: mstep(t, t', n) ==> value(t') || step(t').Some?;
  {
    var T := has_type(Context(Empty), t).get;
    forall (t', n:nat | mstep(t, t', n))
      ensures value(t') || step(t').Some?;
    {
      theorem_fundamental_R(Empty, t, T);
      forall (e | g(Empty, e, n+1))
        ensures e==Empty;
        ensures value(t') || step(t').Some?;
      {
        lemma_E(T, t, n+1, n, 0, t');
        if (irred(t')) {
          assert V(T, t', 0);
          lemma_V_value(T, t', 0);
          assert value(t');
        } else {
          assert step(t').Some?;
        }
      }
    }
  }
}
