// Normalization of STLC
// http://www.cis.upenn.edu/~bcpierce/sf/Norm.html

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

function reduces_to(t: tm, t': tm, n: nat): bool
  decreases n;
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
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

// --- END excerpt from Stlc.dfy ---

function halts(t: tm): bool
{
  exists t', n:nat :: reduces_to(t, t', n) && value(t')
}

ghost method lemma_value_halts(v: tm)
  requires value(v);
  ensures halts(v);
{
  assert reduces_to(v, v, 0);
}

function R(T: ty, t: tm): bool
{
 match T
 /* bool */  case TBool =>
   has_type(Context(Empty), t) == Some(TBool) &&
   halts(t)
 /* arrow */ case TArrow(T1, T2) =>
   has_type(Context(Empty), t) == Some(TArrow(T1, T2)) &&
   halts(t) &&
   (forall s :: R(T1, s) ==> R(T2, tapp(t, s)))
}

ghost method lemma_R_halts(T: ty, t: tm)
  requires R(T, t);
  ensures halts(t);
{
}

ghost method lemma_R_typable_empty(T: ty, t: tm)
  requires R(T, t);
  ensures has_type(Context(Empty), t) == Some(T);
{
}

// Membership in R_T is invariant under evaluation

ghost method lemma_step_preserves_halting(t: tm, t': tm)
  requires step(t) == Some(t');
  ensures halts(t) <==> halts(t');
{
  if (halts(t)) {
    parallel (t'', n:nat | reduces_to(t, t'', n) && value(t''))
      ensures reduces_to(t', t'', n-1) && value(t'');
    {
    }
  }
  if (!halts(t)) {
    parallel (t'', n:nat | !reduces_to(t, t'', n+1) || !value(t''))
      ensures !reduces_to(t', t'', n) || !value(t'');
    {
    }
  }
}

ghost method lemma_step_preserves_R(T: ty, t: tm, t': tm)
  requires step(t) == Some(t');
  requires R(T, t);
  ensures R(T, t');
{
  theorem_preservation(t);
  lemma_step_preserves_halting(t, t');
  if (T.TArrow?) {
    var T1 := T.paramT;
    var T2 := T.bodyT;
    assert R(TArrow(T1, T2), t);
    parallel (s | R(T1, s))
      ensures R(T2, tapp(t', s));
    {
      assert R(T2, tapp(t, s));
      lemma_step_preserves_R(T2, tapp(t, s), tapp(t', s));
    }
  }
}

ghost method lemma_multistep_preserves_R(T: ty, t: tm, t': tm, n: nat)
  requires reduces_to(t, t', n);
  requires R(T, t);
  ensures R(T, t');
  decreases n;
{
  if (t != t' && n > 0) {
    lemma_step_preserves_R(T, t, step(t).get);
    lemma_multistep_preserves_R(T, step(t).get, t', n-1);
  }
}

ghost method lemma_step_preserves_R'(T: ty, t: tm, t': tm)
  requires has_type(Context(Empty), t) == Some(T);
  requires step(t) == Some(t');
  requires R(T, t');
  ensures R(T, t);
{
  lemma_step_preserves_halting(t, t');
  if (T.TArrow?) {
    var T1 := T.paramT;
    var T2 := T.bodyT;
    assert R(TArrow(T1, T2), t');
    parallel (s | R(T1, s))
      ensures R(T2, tapp(t, s));
    {
      assert R(T2, tapp(t', s));
      lemma_R_typable_empty(T1, s);
      lemma_step_preserves_R'(T2, tapp(t, s), tapp(t', s));
    }
  }
}

ghost method lemma_multistep_preserves_R'(T: ty, t: tm, t': tm, n: nat)
  requires has_type(Context(Empty), t) == Some(T);
  requires reduces_to(t, t', n);
  requires R(T, t');
  ensures R(T, t);
  decreases n;
{
  if (t != t' && n > 0) {
    theorem_preservation(t);
    lemma_multistep_preserves_R'(T, step(t).get, t', n-1);
    lemma_step_preserves_R'(T, t, step(t).get);
  }
}


// Closed instances of terms of type T belongs to R_T


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

function instantiation(c: partial_map<ty>, e: partial_map<tm>): bool
{
  match c
  case Empty => e.Empty?
  case Extend(x, T, c') =>
    match e
    case Empty => false
    case Extend(xe, v, e') =>
      xe==x && value(v) && R(T, v) && instantiation(c', e')
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

// Properties of Instantiations

ghost method lemma_instantiation_domains_match_any(c: partial_map<ty>, e: partial_map<tm>, x: nat)
  requires instantiation(c, e);
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
        lemma_instantiation_domains_match_any(c', e', x);
      }
    }
  }
}

ghost method lemma_instantiation_domains_match(c: partial_map<ty>, e: partial_map<tm>)
  requires instantiation(c, e);
  ensures forall x:nat :: lookup(x, c).Some? ==> lookup(x, e).Some?;
{
  parallel (x:nat | lookup(x, c).Some?)
    ensures lookup(x, e).Some?;
  {
    lemma_instantiation_domains_match_any(c, e, x);
  }
}

ghost method lemma_instantiation_env_closed(c: partial_map<ty>, e: partial_map<tm>)
  requires instantiation(c, e);
  ensures closed_env(e);
{
  match e {
  case Empty =>
  case Extend(x, t, e') =>
    match c {
    case Empty =>
    case Extend(x', T, c') =>
      assert x==x';
      lemma_R_typable_empty(T, t);
      corollary_typable_empty__closed(t);
      lemma_instantiation_env_closed(c', e');
    }
  }
}

ghost method lemma_instantiation_R(c: partial_map<ty>, e: partial_map<tm>, x: nat, t: tm, T: ty)
  requires instantiation(c, e);
  requires lookup(x, c) == Some(T);
  requires lookup(x, e) == Some(t);
  ensures R(T, t);
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
        lemma_instantiation_R(c', e', x, t, T);
      }
    }
  }
}

ghost method lemma_instantiation_drop_any(c: partial_map<ty>, e: partial_map<tm>, x: nat)
  requires instantiation(c, e);
  ensures instantiation(drop(x, c), drop(x, e));
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
      lemma_instantiation_drop_any(c', e', x);
    }
  }
}

ghost method lemma_instantiation_drop(c: partial_map<ty>, e: partial_map<tm>)
  requires instantiation(c, e);
  ensures forall x:nat :: instantiation(drop(x, c), drop(x, e));
{
  parallel (x:nat)
    ensures instantiation(drop(x, c), drop(x, e));
  {
    lemma_instantiation_drop_any(c, e, x);
  }
}

// Congruence lemmas on multistep
ghost method lemma_multistep_App2(v: tm, t: tm, t': tm, n: nat)
  requires value(v);
  requires reduces_to(t, t', n);
  ensures reduces_to(tapp(v, t), tapp(v, t'), n);
  decreases n;
{
  if (t != t') {
    lemma_multistep_App2(v, step(t).get, t', n-1);
  }
}


// The R Lemma


ghost method lemma_msubst_preserves_typing_any(c: partial_map<ty>, e: partial_map<tm>, init: partial_map<ty>, t: tm, S: ty)
  requires instantiation(c, e);
  requires has_type(Context(mextend(init, c)), t) == Some(S);
  ensures has_type(Context(init), msubst(e, t)) == Some(S);
{
  match c {
  case Empty =>
  case Extend(x, T, c') =>
    match e {
    case Empty =>
    case Extend(xe, v, e') =>
      lemma_R_typable_empty(T, v);
      lemma_substitution_preserves_typing(Context(mextend(init, c')), x, v, t);
      lemma_msubst_preserves_typing_any(c', e', init, subst(x, v, t), S);
    }
  }
}

ghost method lemma_msubst_preserves_typing(c: partial_map<ty>, e: partial_map<tm>)
  requires instantiation(c, e);
  ensures forall init, t, S ::
    has_type(Context(mextend(init, c)), t) == Some(S) ==>
    has_type(Context(init), msubst(e, t)) == Some(S);
{
  parallel (init, t, S | has_type(Context(mextend(init, c)), t) == Some(S))
    ensures has_type(Context(init), msubst(e, t)) == Some(S);
  {
    lemma_msubst_preserves_typing_any(c, e, init, t, S);
  }
}

// more helpers for R lemma

ghost method lemma_reduces_to_value_if(T: ty, c: tm, a: tm, b: tm, c': tm, a': tm, b': tm, nc: nat, na: nat, nb: nat)
  requires has_type(Context(Empty), c) == Some(TBool);
  requires has_type(Context(Empty), a) == Some(T);
  requires has_type(Context(Empty), b) == Some(T);
  requires reduces_to(c, c', nc) && value(c');
  requires reduces_to(a, a', na) && value(a');
  requires reduces_to(b, b', nb) && value(b');
  ensures c' == ttrue ==> reduces_to(tif(c, a, b), a', nc+na+1);
  ensures c' == tfalse ==> reduces_to(tif(c, a, b), b', nc+nb+1);
  ensures c' == ttrue || c' == tfalse;
  ensures has_type(Context(Empty), tif(c, a, b)) == Some(T);
  decreases nc+na+nb;
{
  if (c != c') {
    theorem_preservation(c);
    lemma_reduces_to_value_if(T, step(c).get, a, b, c', a', b', nc-1, na, nb);
  } else {
    if (c' == ttrue) {
      if (a != a') {
        theorem_preservation(a);
        lemma_reduces_to_value_if(T, c, step(a).get, b, c', a', b', nc, na-1, nb);
      }
    }
    if (c' == tfalse) {
      if (b != b') {
        theorem_preservation(b);
        lemma_reduces_to_value_if(T, c, a, step(b).get, c', a', b', nc, na, nb-1);
      }
    }
  }
}

ghost method lemma_R_if(T: ty, c: tm, a: tm, b: tm)
  requires R(TBool, c);
  requires R(T, a);
  requires R(T, b);
  requires has_type(Context(Empty), tif(c, a, b)) == Some(T);
  ensures R(T, tif(c, a, b));
{
  assert exists c', nc:nat :: reduces_to(c, c', nc) && value(c');
  assert exists a', na:nat :: reduces_to(a, a', na) && value(a');
  assert exists b', nb:nat :: reduces_to(b, b', nb) && value(b');
  parallel (c', a', b', nc:nat, na:nat, nb:nat |
            reduces_to(c, c', nc) && value(c') &&
            reduces_to(a, a', na) && value(a') &&
            reduces_to(b, b', nb) && value(b'))
  ensures R(T, tif(c, a, b));
  {
    lemma_reduces_to_value_if(has_type(Context(Empty), a).get, c, a, b, c', a', b', nc, na, nb);
    if (c' == ttrue) {
      lemma_multistep_preserves_R(T, a, a', na);
      lemma_multistep_preserves_R'(T, tif(c, a, b), a', nc+na+1);
    }
    if (c' == tfalse) {
      lemma_multistep_preserves_R(T, b, b', nb);
      lemma_multistep_preserves_R'(T, tif(c, a, b), b', nc+nb+1);
    }
  }
}

// the R lemma, finally...

ghost method lemma_msubst_R(c: partial_map<ty>, e: partial_map<tm>, t: tm, T: ty)
  requires has_type(Context(c), t) == Some(T);
  requires instantiation(c, e);
  ensures R(T, msubst(e, t));
  decreases t;
{
  lemma_instantiation_env_closed(c, e);
  match t {
  case tvar(id) =>
    lemma_instantiation_domains_match(c, e);
    lemma_msubst_var(e, id);
    lemma_instantiation_R(c, e, id, lookup(id, e).get, T);
  case tabs(x, T1, body) =>
    lemma_mextend(c);
    lemma_msubst_preserves_typing_any(c, e, Empty, tabs(x, T1, body), T);
    lemma_msubst_abs(e, x, T1, body);
    assert has_type(Context(Empty), tabs(x, T1, msubst(drop(x, e), body))) == Some(T);
    assert has_type(Context(Empty), msubst(e, t)) == Some(T);

    assert reduces_to(msubst(e, t), msubst(e, t), 0);
    assert value(msubst(e, t));
    assert halts(msubst(e, t));

    parallel(s | R(T1, s))
      ensures R(T.bodyT, tapp(msubst(e, t), s));
    {
      parallel(s', n:nat | reduces_to(s, s', n) && value(s'))
        ensures R(T.bodyT, tapp(msubst(e, t), s));
      {
        lemma_multistep_preserves_R(T1, s, s', n);
        lemma_R_typable_empty(T1, s');
        assert has_type(Context(Empty), tapp(msubst(e, t), s')) == Some(T.bodyT);

        corollary_typable_empty__closed(s');
        lemma_msubst_preserves_typing_any(c, e, Empty, tabs(x, T1, body), T);
        lemma_subst_msubst(e, x, s', body);
        lemma_msubst_R(Extend(x, T1, c), Extend(x, s', e), body, T.bodyT);
        lemma_step_preserves_R'(T.bodyT, tapp(msubst(e, t), s'), msubst(Extend(x, s', e), body));
        assert R(T.bodyT, tapp(msubst(e, t), s'));
        lemma_multistep_App2(msubst(e, t), s, s', n);
        lemma_multistep_preserves_R'(T.bodyT, tapp(msubst(e, t), s), tapp(msubst(e, t), s'), n);
      }
      assert forall s', n:nat :: reduces_to(s, s', n) && value(s') ==> R(T.bodyT, tapp(msubst(e, t), s));
      lemma_R_halts(T1, s);
      assert exists s', n:nat :: reduces_to(s, s', n) && value(s');
      assert R(T.bodyT, tapp(msubst(e, t), s));
    }
  case tapp(f, arg) =>
    lemma_msubst_R(c, e, f, has_type(Context(c), f).get);
    lemma_msubst_R(c, e, arg, has_type(Context(c), arg).get);
    lemma_msubst_app(e, f, arg);
  case ttrue =>
    lemma_msubst_true(e);
    assert reduces_to(ttrue, ttrue, 0);
  case tfalse =>
    lemma_msubst_false(e);
    assert reduces_to(tfalse, tfalse, 0);
  case tif(cond, a, b) =>
    lemma_msubst_R(c, e, cond, TBool);
    lemma_msubst_R(c, e, a, T);
    lemma_msubst_R(c, e, b, T);
    lemma_msubst_if(e, cond, a, b);
    lemma_mextend(c);
    lemma_msubst_preserves_typing_any(c, e, Empty, t, T);
    lemma_R_if(T, msubst(e, cond), msubst(e, a), msubst(e, b));
  }
}

// Normalization Theorem
ghost method theorem_normalization(t: tm)
  requires has_type(Context(Empty), t).Some?;
  ensures halts(t);
{
  var T := has_type(Context(Empty), t).get;
  lemma_msubst_R(Empty, Empty, t, T);
  lemma_R_halts(T, t);
}