// Proving Type-Safety of the Simply Typed Lambda-Calculus using Logical Relations

// --- BEGIN excerpt from Stlc.dfy ---

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

// Properties

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

// --- END excerpt from Stlc.dfy ---

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

// BEGIN excerpt Norm.dfy

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
  parallel (x:nat)
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
  parallel (e: partial_map<tm>)
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

// Congruence lemmas on multistep
ghost method lemma_multistep_App2(v: tm, t: tm, t': tm, n: nat)
  requires value(v);
  requires mstep(t, t', n);
  ensures mstep(tapp(v, t), tapp(v, t'), n);
  decreases n;
{
  if (n > 0) {
    lemma_multistep_App2(v, step(t).get, t', n-1);
  }
}
// END excerpt Norm.dfy

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
  decreases T, k;
{
  match T
  case TBool => t==ttrue || t==tfalse
  case TArrow(T1, T2) => t.tabs? && (forall j:nat, v :: j <= k ==> closed(v) && V(T1, v, j) ==> E(T2, subst(t.x, v, t.body), j))
}

predicate E(T: ty, t: tm, k: nat)
  decreases T, k;
{
  if (k == 0) then true
  else forall i:nat, j:nat, t' :: i+j<k ==> mstep(t, t', i) && irred(t') ==> V(T, t', j)
}
// where
predicate irred(t: tm)
{
  step(t).None?
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

// The logical relations V_k(T, t) and E_k(T, t) is only meant for _closed_ terms.

/*
ghost method lemma_V_closed(T: ty, t: tm, k: nat)
  requires V(T, t, k);
  ensures closed(t);
{
  if (T.TArrow?) {
    parallel (x:nat | x!=t.x)
      ensures !appears_free_in(x, t.body);
    {
       parallel (j:nat, v | j<=k && closed(v) && V(T.paramT, v, j))
        ensures closed(subst(t.x, v, t.body));
      {
        lemma_V_arrow(T.paramT, T.bodyT, t.x, t.body, v, k, j);
        lemma_E_closed(T.bodyT, subst(t.x, v, t.body), j);
        assert closed(subst(t.x, v, t.body));
      }
    }
  }
}

ghost method lemma_E_closed(T: ty, t: tm, k: nat)
  requires E(T, t, k);
  ensures closed(t);
{
  if (irred(t)) {

  }
}
*/

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
  parallel (x:nat | lookup(x, c).Some?)
    ensures lookup(x, e).Some?;
  {
    lemma_g_domains_match_any(c, e, k, x);
  }
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

// NOTE BUG: work around because R(c', body, T2) gets forgotten.
ghost method lemma_g_monotonic_hack(c: partial_map<ty>, e: partial_map<tm>, k: nat, j: nat, c': partial_map<ty>, body: tm, T2: ty)
  requires g(c, e, k);
  requires j <= k;
  ensures g(c, e, j);
  requires R(c', body, T2);
  ensures R(c', body, T2);
{
  lemma_g_monotonic(c, e, k, j);
}

// NOTE BUG: ditto.
ghost method lemma_g_monotonic_hack'(c: partial_map<ty>, e: partial_map<tm>, k: nat, j: nat, c': partial_map<ty>, body: tm, T2: ty)
  requires g(c, e, k);
  requires j <= k;
  ensures g(c, e, j);
  requires has_type(Context(c'), body) == Some(T2);
  ensures has_type(Context(c'), body) == Some(T2);
{
  lemma_g_monotonic(c, e, k, j);
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
  parallel (x:nat)
    ensures g(drop(x, c), drop(x, e), k);
  {
    lemma_g_drop_any(c, e, k, x);
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

/*
ghost method lemma_multistep_preserves_E(T: ty, t: tm, t': tm, k: nat, i: nat)
  requires i<=k;
  requires E(T, t, k);
  requires mstep(t, t', i);
  ensures E(T, t', k-i);
  decreases t;
{
  if (k-i>0) {
    parallel (i':nat, j:nat, t'' | i'+j<k-i && mstep(t', t'', i') && irred(t''))
      ensures V(T, t'', j);
    {
      lemma_mstep_trans(t, t', t'', i, i');
    }
  }
}
*/

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

ghost method make_V0(T: ty) returns (v: tm)
  ensures closed(v);
  ensures V(T, v, 0);
  decreases T;
{
  match T {
  case TBool =>
    v := ttrue;
  case TArrow(T1, T2) =>
    var v' := make_V0(T2);
    v := tabs(0, T1, v');
  }
}

// NOTE BUG
ghost method make_V0_hack(T: ty, c': partial_map<ty>, t': tm, T': ty) returns (v: tm)
  ensures closed(v);
  ensures V(T, v, 0);
  requires has_type(Context(c'), t') == Some(T');
  ensures has_type(Context(c'), t') == Some(T');
{
  v := make_V0(T);
}

ghost method lemma_subst_afi(x: nat, y: nat, t: tm, v: tm)
  requires closed(v);
  requires x!=y;
  requires !appears_free_in(y, subst(x, v, t));
  ensures !appears_free_in(y, t);
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

ghost method lemma_g_msubst_closed(c: partial_map<ty>, e: partial_map<tm>, k: nat, t: tm, T: ty)
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
    lemma_g_monotonic_hack'(c, e, k, 0, c', body, T.bodyT);
    var v := make_V0_hack(T1, c', body, T.bodyT);
    var e' := Extend(x, v, e);
    lemma_g_msubst_closed(c', e', 0, body, T.bodyT);
    lemma_g_env_closed(c, e, k);
    lemma_subst_msubst(e, x, v, body);
    parallel (y:nat | y!=x)
      ensures !appears_free_in(y, msubst(drop(x, e), body));
    {
      lemma_subst_afi(x, y, msubst(drop(x, e), body), v);
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
  }
}

ghost method lemma_if_closed(c: tm, a: tm, b: tm)
  requires closed(tif(c, a, b));
  ensures closed(c) && closed(a) && closed(b);
{
  if (!closed(c)) {
    assert exists x:nat :: appears_free_in(x, c);
    parallel (x:nat | appears_free_in(x, c))
      ensures appears_free_in(x, tif(c, a, b));
    {
    }
    assert exists x:nat :: appears_free_in(x, tif(c, a, b));
    assert false;
  }
  if (!closed(a)) {
    assert exists x:nat :: appears_free_in(x, a);
    parallel (x:nat | appears_free_in(x, a))
      ensures appears_free_in(x, tif(c, a, b));
    {
    }
    assert exists x:nat :: appears_free_in(x, tif(c, a, b));
    assert false;
  }
  if (!closed(b)) {
    assert exists x:nat :: appears_free_in(x, b);
    parallel (x:nat | appears_free_in(x, b))
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
    parallel (x:nat | appears_free_in(x, f))
      ensures appears_free_in(x, tapp(f, arg));
    {
    }
    assert exists x:nat :: appears_free_in(x, tapp(f, arg));
    assert false;
  }
  if (!closed(arg)) {
    assert exists x:nat :: appears_free_in(x, arg);
    parallel (x:nat | appears_free_in(x, arg))
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
  parallel (z:nat)
    ensures z==x || !appears_free_in(z, t);
  {
    if (z!=x) {
      assert !appears_free_in(z, tabs(x, T, t));
      assert !appears_free_in(z, t);
    }
  }
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
    parallel (y:nat)
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

  parallel (i:nat, j:nat, t' | i+j<k && mstep(mt, t', i) && irred(t'))
    ensures V(T, t', j);
  {
    var f', fi := lemma_app_irred__f_mstep_irred(mf, marg, t', i);
    //assert fi<=i && mstep(mf, f', fi) && irred(f');
    lemma_E(Tf, mf, k, fi, j+i-fi, f');
    //assert V(Tf, f', j+i-fi);
    lemma_V_value(Tf, f', j+i-fi);
    //assert value(f');

    lemma_mstep_app_f(mf, marg, f', fi);
    //assert mstep(mt, t', i);
    lemma_mstep_trans'(mt, tapp(f', marg), t', fi, i);
    //assert mstep(tapp(f', marg), t', i-fi);

    var arg', argi := lemma_app_irred__arg_mstep_irred(f', marg, t', i-fi);
    //assert argi<=i && mstep(marg, arg', argi) && irred(arg');
    lemma_E(Targ, marg, k, argi, j+i-fi-argi, arg');
    //assert V(Targ, arg', j+i-fi-argi);
    lemma_V_value(Targ, arg', j+i-fi-argi);
    //assert value(arg');

    //assert closed(marg);
    lemma_multistep_preserves_closed(marg, arg', argi);
    //assert closed(arg');

    lemma_V_arrow(Targ, T, f'.x, f'.body, arg', j+i-fi, j+i-fi-argi);
    //assert E(T, subst(f'.x, arg', f'.body), j+i-fi-argi);

    //assert mstep(tapp(f', arg'), subst(f'.x, arg', f'.body), 1);
    lemma_mstep_app_arg(f', marg, arg', argi);
    //assert mstep(tapp(f', marg), tapp(f', arg'), argi);
    lemma_mstep_trans'(tapp(f', marg), tapp(f', arg'), t', argi, i-fi);
    lemma_mstep_trans'(tapp(f', arg'), subst(f'.x, arg', f'.body), t', 1, i-fi-argi);
    //assert mstep(subst(f'.x, arg', f'.body), t', i-fi-argi-1);

    lemma_E(T, subst(f'.x, arg', f'.body), j+i-fi-argi, i-fi-argi-1, j, t');
    //assert V(T, t', j);
  }
  assert E(T, msubst(e, t), k);
}

// The Fundamental Theorem of Logical Relations relates well-typed terms to terms that are in the logical relation:
ghost method theorem_fundamental_R(c: partial_map<ty>, t: tm, T: ty)
  requires has_type(Context(c), t) == Some(T);
  ensures R(c, t, T);
  decreases t;
{
// The proof is by induction on the typing derivation, which is syntax-directed.
  parallel (e, k:nat | g(c, e, k))
    ensures E(T, msubst(e, t), k);
  {
    match t {
    case tvar(id) =>
      lemma_g_env_closed(c, e, k);
      lemma_g_domains_match(c, e, k);
      lemma_msubst_var(e, id);
      lemma_g_V(c, e, k, id, lookup(id, e).get, T);
      //assert E(T, msubst(e, t), k);
      assert E(T, msubst(e, t), k);
    case tabs(x, T1, body) =>
      //assert T.TArrow? && T.paramT==T1;
      var T2 := T.bodyT;
      var c' := Extend(x, T1, c);
      //assert has_type(Context(c'), body) == Some(T2);
      theorem_fundamental_R(c', body, T2);
      //assert R(c', body, T2);
      parallel (j:nat, v | j<=k && closed(v) && V(T1, v, j))
        ensures E(T2, subst(x, v, msubst(drop(x, e), body)), j);
      {
        var e' := Extend(x, v, e);
        lemma_g_monotonic_hack(c, e, k, j, c', body, T2);
        //assert g(c', e', j);
        //assert R(c', body, T2);
        lemma_R(c', e', j, body, T2);
        //assert E(T2, msubst(e', body), j);
        lemma_g_env_closed(c', e', j);
        lemma_subst_msubst(e, x, v, body);
      }
      //assert forall j:nat, v :: j<=k && closed(v) && V(T1, v, j) ==> E(T2, subst(x, v, msubst(drop(x, e), body)), j);
      assert E(T, tabs(x, T1, msubst(drop(x, e), body)), k);
      lemma_msubst_abs(e, x, T1, body);
      assert E(T, msubst(e, t), k);
    case tapp(f, arg) =>
      var Tf := has_type(Context(c), f).get;
      var Targ := has_type(Context(c), arg).get;
      theorem_fundamental_R(c, f, Tf);
      theorem_fundamental_R(c, arg, Targ);
      lemma_g_msubst_closed(c, e, k, arg, Targ);
      theorem_fundamental_R_app(c, e, k, f, arg, Tf, Targ);
      assert E(T, msubst(e, t), k);
    case ttrue =>
      lemma_msubst_true(e);
      //assert msubst(e, ttrue) == ttrue;
      assert E(T, msubst(e, t), k);
    case tfalse =>
      lemma_msubst_false(e);
      //assert msubst(e, tfalse) == tfalse;
      assert E(T, msubst(e, t), k);
    case tif(cond, a, b) =>
      theorem_fundamental_R(c, cond, TBool);
      theorem_fundamental_R(c, a, T);
      theorem_fundamental_R(c, b, T);
      lemma_msubst_if(e, cond, a, b);
      var mc := msubst(e, cond);
      var ma := msubst(e, a);
      var mb := msubst(e, b);
      var mt := msubst(e, t);

      parallel (i:nat, j:nat, t' | i+j<k && mstep(mt, t', i) && irred(t'))
        ensures V(T, t', j);
      {
        var c', ci := lemma_if_irred__c_mstep_irred(mc, ma, mb, t', i);
        //assert ci<=i && mstep(mc, c', ci) && irred(c');
        lemma_E(TBool, mc, k, ci, j, c');
        //assert V(TBool, c', j);
        //assert c' == ttrue || c' == tfalse;
        lemma_mstep_if_c(mc, ma, mb, c', ci);
        //assert mstep(mt, t', i);
        lemma_mstep_trans'(mt, tif(c', ma, mb), t', ci, i);
        //assert mstep(tif(c', ma, mb), t', i-ci);
        if (c' == ttrue) {
          //assert step(tif(c', ma, mb)) == Some(ma);
          lemma_mstep_trans'(tif(c', ma, mb), ma, t', 1, i-ci);
          //assert mstep(ma, t', i-ci-1);
          lemma_E(T, ma, k, i-ci-1, j, t');
          //assert V(T, t', j);
        } else {
          //assert step(tif(c', ma, mb)) == Some(mb);
          lemma_mstep_trans'(tif(c', ma, mb), mb, t', 1, i-ci);
          //assert mstep(mb, t', i-ci-1);
          lemma_E(T, mb, k, i-ci-1, j, t');
          //assert V(T, t', j);
        }
      }
      assert E(T, msubst(e, t), k);
    }
  }
}

ghost method corollary_type_safety(t: tm)
  ensures type_safety(t);
{
  parallel (T | has_type(Context(Empty), t).Some?)
    ensures forall t', n:nat :: mstep(t, t', n) ==> value(t') || step(t').Some?;
  {
    var T := has_type(Context(Empty), t).get;
    parallel (t', n:nat | mstep(t, t', n))
      ensures value(t') || step(t').Some?;
    {
      theorem_fundamental_R(Empty, t, T);
      parallel (e | g(Empty, e, n+1))
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
