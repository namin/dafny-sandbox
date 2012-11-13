// Proving Type-Safety of the Simply Typed Lambda-Calculus
// with Mutable References
// using Step-Indexed Logical Relations
// adapted from Lr_Ts_Stlc.dfy
//
// For a different approach, see http://www.cis.upenn.edu/~bcpierce/sf/References.html

datatype option<A> = None | Some(get: A);

// Syntax

// Types
datatype ty = TBool | TArrow(paramT: ty, bodyT: ty) |
              TUnit | TRef(cellT: ty);

// Terms
datatype tm = tvar(id: nat) | tapp(f: tm, arg: tm) | tabs(x: nat, T: ty, body: tm) | ttrue | tfalse | tif(c: tm, a: tm, b: tm) |
              tunit | tref(r: tm) | tderef(d: tm) | tassign(lhs: tm, rhs: tm) | tloc(l: nat);


// Operational Semantics

// Values
function value(t: tm): bool
{
  t.tabs? || t.ttrue? || t.tfalse? ||
  t.tunit? || t.tloc?
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
  case tunit => tunit
  case tref(t1) => tref(subst(x, s, t1))
  case tderef(t1) => tderef(subst(x, s, t1))
  case tassign(t1, t2) => tassign(subst(x, s, t1), subst(x, s, t2))
  case tloc(l) => tloc(l)
}

// Stores

datatype list<T> = Nil | Cons(head: T, tail: list<T>);
function length<T>(lst: list<T>): nat
{
  match lst
  case Nil => 0
  case Cons(head, tail) => 1+length(tail)
}
function nth<T>(n: nat, lst: list<tm>, d: tm): tm
{
  match lst
  case Nil => d
  case Cons(head, tail) => if (n==0) then head else nth(n-1, tail, d)
}
function snoc<T>(lst: list<T>, x: T): list<T>
{
  match lst
  case Nil => Cons(x, Nil)
  case Cons(head, tail) => Cons(head, snoc(tail, x))
}
function replace<T>(n: nat, x: T, lst: list<T>): list<T>
{
  match lst
  case Nil => Nil
  case Cons(head, tail) => if (n==0) then Cons(x, tail) else Cons(head, replace(n-1, x, tail))
}

datatype store = Store(lst: list<tm>);
function store_lookup(n: nat, st: store): tm
{
  nth(n, st.lst, tunit)
}

// Reduction
datatype pair<A,B> = P(fst: A, snd: B);

function step(t: tm, s: store): option<pair<tm, store>>
  decreases t;
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then
                     Some(P(subst(t.f.x, t.arg, t.f.body), s))
  /* App1 */       else if (t.tapp? && step(t.f, s).Some?) then
                     Some(P(tapp(step(t.f, s).get.fst, t.arg), step(t.f, s).get.snd))
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg, s).Some?) then
                     Some(P(tapp(t.f, step(t.arg, s).get.fst), step(t.arg, s).get.snd))
  /* IfTrue */     else if (t.tif? && t.c == ttrue) then
                     Some(P(t.a, s))
  /* IfFalse */    else if (t.tif? && t.c == tfalse) then
                     Some(P(t.b, s))
  /* If */         else if (t.tif? && step(t.c, s).Some?) then
                     Some(P(tif(step(t.c, s).get.fst, t.a, t.b), step(t.c, s).get.snd))
  /* RefValue */   else if (t.tref? && value(t.r)) then
                     Some(P(tloc(length(s.lst)), Store(snoc(s.lst, t.r))))
  /* Ref */        else if (t.tref? && step(t.r, s).Some?) then
                     Some(P(tref(step(t.r, s).get.fst), step(t.r, s).get.snd))
  /* DerefLoc */   else if (t.tderef? && t.d.tloc? && t.d.l < length(s.lst)) then
                     Some(P(store_lookup(t.d.l, s), s))
  /* Deref */      else if (t.tderef? && step(t.d, s).Some?) then
                     Some(P(tderef(step(t.d, s).get.fst), step(t.d, s).get.snd))
  /* Assign */     else if (t.tassign? && value(t.rhs) && t.lhs.tloc? && t.lhs.l < length(s.lst)) then
                     Some(P(tunit, Store(replace(t.lhs.l, t.rhs, s.lst))))
  /* Assign1 */    else if (t.tassign? && step(t.lhs, s).Some?) then
                     Some(P(tassign(step(t.lhs, s).get.fst, t.rhs), step(t.lhs, s).get.snd))
  /* Assign2 */    else if (t.tassign? && value(t.lhs) && step(t.rhs, s).Some?) then
                     Some(P(tassign(t.lhs, step(t.rhs, s).get.fst), step(t.rhs, s).get.snd))
                   else None
}

predicate irred(t: tm, s: store)
{
  step(t, s).None?
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
 /* Unit */        case tunit => Some(TUnit)
 /* Loc */         case tloc(l) => None // locations are not part of user programs
 /* Ref */         case tref(t1) =>
                     var ty1 := has_type(c, t1);
					           if (ty1.Some?) then Some(TRef(ty1.get)) else None
 /* Deref */       case tderef(t1) =>
                     var ty1 := has_type(c, t1);
					           if (ty1.Some? && ty1.get.TRef?) then Some(ty1.get.cellT) else None
 /* Assign */      case tassign(t1, t2) =>
                     var ty1 := has_type(c, t1);
					           var ty2 := has_type(c, t2);
					           if (ty1.Some? && ty2.Some? && ty1.get.TRef? && ty1.get.cellT == ty2.get)
					           then Some(TUnit)
          					 else None
}


// Properties

// Free Occurrences
function appears_free_in(x: nat, t: tm): bool
{
  /* var */     (t.tvar? && t.id==x) ||
  /* app1 */    (t.tapp? && appears_free_in(x, t.f)) ||
  /* app2 */    (t.tapp? && appears_free_in(x, t.arg)) ||
  /* abs */     (t.tabs? && t.x!=x && appears_free_in(x, t.body)) ||
  /* if1 */     (t.tif? && appears_free_in(x, t.c)) ||
  /* if2 */     (t.tif? && appears_free_in(x, t.a)) ||
  /* if3 */     (t.tif? && appears_free_in(x, t.b)) ||
  /* ref */     (t.tref? && appears_free_in(x, t.r)) ||
  /* deref */   (t.tderef? && appears_free_in(x, t.d)) ||
  /* assign1 */ (t.tassign? && appears_free_in(x, t.lhs)) ||
  /* assign2 */ (t.tassign? && appears_free_in(x, t.rhs))
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

// Multistep

function mstep(t: tm, s: store, t': tm, s': store, n: nat): bool
  decreases n;
{
  if (n==0) then t == t' && s == s'
  else step(t, s).Some? && mstep(step(t, s).get.fst, step(t, s).get.snd, t', s', n-1)
}

// Properties of multistep

ghost method lemma_mstep_trans(t1: tm, s1: store, t2: tm, s2: store, t3: tm, s3: store, n12: nat, n23: nat)
  requires mstep(t1, s1, t2, s2, n12);
  requires mstep(t2, s2, t3, s3, n23);
  ensures mstep(t1, s1, t3, s3, n12+n23);
  decreases n12+n23;
{
  if (n12>0) {
    lemma_mstep_trans(step(t1, s1).get.fst, step(t1, s1).get.snd, t2, s2, t3, s3, n12-1, n23);
  } else if (n23>0) {
    lemma_mstep_trans(step(t1, s1).get.fst, step(t1, s1).get.snd, step(t2, s2).get.fst, step(t2, s2).get.snd, t3, s3, n12, n23-1);
  }
}

ghost method lemma_mstep_trans'(t1: tm, s1: store, t2: tm, s2: store, t3: tm, s3: store, n12: nat, n13: nat)
  requires n12 <= n13;
  requires mstep(t1, s1, t2, s2, n12);
  requires mstep(t1, s1, t3, s3, n13);
  ensures mstep(t2, s2, t3, s3, n13-n12);
  decreases n12;
{
  if (n12>0 && n13>0) {
    lemma_mstep_trans'(step(t1, s1).get.fst, step(t1, s1).get.snd, t2, s2, t3, s3, n12-1, n13-1);
  }
}

// Congruence lemmas on multistep

ghost method lemma_mstep_if_c(c: tm, a: tm, b: tm, c': tm, s: store, s': store, ci: nat)
  requires mstep(c, s, c', s', ci);
  ensures mstep(tif(c, a, b), s, tif(c', a, b), s', ci);
  decreases ci;
{
  if (ci>0) {
    lemma_mstep_if_c(step(c, s).get.fst, a, b, c', step(c, s).get.snd, s', ci-1);
  }
}

ghost method lemma_mstep_app_f(f: tm, arg: tm, f': tm, s: store, s': store, fi: nat)
  requires mstep(f, s, f', s', fi);
  ensures mstep(tapp(f, arg), s, tapp(f', arg), s', fi);
  decreases fi;
{
  if (fi>0) {
    lemma_mstep_app_f(step(f, s).get.fst, arg, f', step(f, s).get.snd, s', fi-1);
  }
}

ghost method lemma_mstep_app_arg(f: tm, arg: tm, arg': tm, s: store, s': store, argi: nat)
  requires value(f);
  requires mstep(arg, s, arg', s', argi);
  ensures mstep(tapp(f, arg), s, tapp(f, arg'), s', argi);
  decreases argi;
{
  if (argi>0) {
    lemma_mstep_app_arg(f, step(arg, s).get.fst, arg', step(arg, s).get.snd, s', argi-1);
  }
}

ghost method lemma_if_irred__c_mstep_irred(c: tm, a: tm, b: tm, t': tm, s: store, s': store, i: nat) returns (c': tm, sc': store, ci: nat)
  requires mstep(tif(c, a, b), s, t', s', i);
  requires irred(t', s');
  ensures ci<=i && mstep(c, s, c', sc', ci) && irred(c', sc');
  decreases i;
{
  if (irred(c, s)) {
    c' := c;
	sc' := s;
    ci := 0;
  } else {
    assert step(c, s).Some?;
    lemma_mstep_trans'(tif(c, a, b), s, tif(step(c, s).get.fst, a, b), step(c, s).get.snd, t', s', 1, i);
    var c'', sc'', ci' := lemma_if_irred__c_mstep_irred(step(c, s).get.fst, a, b, t', step(c, s).get.snd, s', i-1);
    lemma_mstep_trans(c, s, step(c, s).get.fst, step(c, s).get.snd, c'', sc'', 1, ci');
    c' := c'';
	  sc' := sc'';
    ci := ci'+1;
  }
}

ghost method lemma_app_irred__f_mstep_irred(f: tm, arg: tm, t': tm, s: store, s': store, i: nat) returns (f': tm, sf': store, fi: nat)
  requires mstep(tapp(f, arg), s, t', s', i);
  requires irred(t', s');
  ensures fi<=i && mstep(f, s, f', sf', fi) && irred(f', sf');
  decreases i;
{
  if (irred(f, s)) {
    f' := f;
	  sf' := s;
    fi := 0;
  } else {
    assert step(f, s).Some?;
    lemma_mstep_trans'(tapp(f, arg), s, tapp(step(f, s).get.fst, arg), step(f, s).get.snd, t', s', 1, i);
    var f'', sf'', fi' := lemma_app_irred__f_mstep_irred(step(f, s).get.fst, arg, t', step(f, s).get.snd, s', i-1);
    lemma_mstep_trans(f, s, step(f, s).get.fst, step(f, s).get.snd, f'', sf'', 1, fi');
    f' := f'';
  	sf' := sf'';
    fi := fi'+1;
  }
}

ghost method lemma_app_irred__arg_mstep_irred(f: tm, arg: tm, t': tm, s: store, s': store, i: nat) returns (arg': tm, sarg': store, argi: nat)
  requires mstep(tapp(f, arg), s, t', s', i);
  requires irred(t', s');
  requires value(f);
  ensures argi<=i && mstep(arg, s, arg', sarg', argi) && irred(arg', sarg');
  decreases i;
{
  if (irred(arg, s)) {
    arg' := arg;
	  sarg' := s;
    argi := 0;
  } else {
    assert step(arg, s).Some?;
    lemma_mstep_trans'(tapp(f, arg), s, tapp(f, step(arg, s).get.fst), step(arg, s).get.snd, t', s', 1, i);
    var arg'', sarg'', argi' := lemma_app_irred__arg_mstep_irred(f, step(arg, s).get.fst, t', step(arg, s).get.snd, s', i-1);
    lemma_mstep_trans(arg, s, step(arg, s).get.fst, step(arg, s).get.snd, arg'', sarg'', 1, argi');
    arg' := arg'';
	  sarg' := sarg'';
    argi := argi'+1;
  }
}

// Closed terms (multi)step to closed terms.

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

ghost method lemma_ref_closed(r: tm)
  requires closed(tref(r));
  ensures closed(r);
{
  if (!closed(r)) {
    assert exists x:nat :: appears_free_in(x, r);
    parallel (x:nat | appears_free_in(x, r))
      ensures appears_free_in(x, tref(r));
    {
    }
    assert exists x:nat :: appears_free_in(x, tref(r));
    assert false;
  }
}

ghost method lemma_deref_closed(d: tm)
  requires closed(tderef(d));
  ensures closed(d);
{
  if (!closed(d)) {
    assert exists x:nat :: appears_free_in(x, d);
    parallel (x:nat | appears_free_in(x, d))
      ensures appears_free_in(x, tderef(d));
    {
    }
    assert exists x:nat :: appears_free_in(x, tderef(d));
    assert false;
  }
}

ghost method lemma_assign_closed(lhs: tm, rhs: tm)
  requires closed(tassign(lhs, rhs));
  ensures closed(lhs) && closed(rhs);
{
  if (!closed(lhs)) {
    assert exists x:nat :: appears_free_in(x, lhs);
    parallel (x:nat | appears_free_in(x, lhs))
      ensures appears_free_in(x, tassign(lhs, rhs));
    {
    }
    assert exists x:nat :: appears_free_in(x, tassign(lhs, rhs));
    assert false;
  }
  if (!closed(rhs)) {
    assert exists x:nat :: appears_free_in(x, rhs);
    parallel (x:nat | appears_free_in(x, rhs))
      ensures appears_free_in(x, tassign(lhs, rhs));
    {
    }
    assert exists x:nat :: appears_free_in(x, tassign(lhs, rhs));
    assert false;
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

predicate closed_tm_list(lst: list<tm>)
  ensures closed_tm_list(lst) && lst.Cons? ==> closed_tm_list(lst.tail);
{
  match lst
  case Nil => true
  case Cons(head, tail) => closed(head) && closed_tm_list(tail)
}

predicate closed_store(s: store)
{
  closed_tm_list(s.lst)
}

ghost method lemma_closed_tm_list__closed_store(lst: list<tm>)
  requires closed_tm_list(lst);
  ensures closed_store(Store(lst));
{
}

ghost method lemma_tm_list__cons_or_nil(lst: list<tm>)
  ensures lst.Cons? || lst.Nil?;
{
}

ghost method lemma_store_lst_cons_or_nil(s: store)
  ensures s.lst.Cons? || s.lst.Nil?;
{
  lemma_tm_list__cons_or_nil(s.lst);
}

ghost method lemma_closed_store__closed_lookup(s: store, l: nat)
  requires closed_store(s);
  ensures closed(store_lookup(l, s));
  decreases s.lst;
{
  lemma_store_lst_cons_or_nil(s);
  assert s.lst.Cons? || s.lst.Nil?;
  if (l>0) {
    if (s.lst.Cons?) {
      lemma_closed_store__closed_lookup(Store(s.lst.tail), l-1);
    }
  }
}

ghost method lemma_closed_tm_list_snoc(lst: list<tm>, v: tm)
  requires closed_tm_list(lst);
  requires closed(v);
  ensures closed_tm_list(snoc(lst, v)); 
{
  if (lst.Nil?) {
    assert closed_tm_list(Cons(v, Nil));
    assert closed_tm_list(snoc(lst, v));
  }
  if (lst.Cons?) {
    lemma_closed_tm_list_snoc(lst.tail, v);
    assert closed_tm_list(snoc(lst, v));
  }
}

// NOTE BUG: really weird "proof" -- why is it needed?
ghost method lemma_closed_tm_list_replace(lst: list<tm>, l: nat, v: tm)
  requires closed_tm_list(lst);
  requires closed(v);
  ensures closed_tm_list(replace(l, v, lst));
{
  if (lst.Cons?) {
    if (l>0) {
      assert closed_tm_list(replace(l, v, lst));
    } else {
      assert closed_tm_list(replace(l, v, lst));
    }
  } else {
    assert closed_tm_list(replace(l, v, lst));
  }
}

ghost method lemma_step_preserves_closed(t: tm, s: store, t': tm, s': store)
  requires closed_store(s);
  requires closed(t);
  requires step(t, s) == Some(P(t', s'));
  ensures closed(t');
  ensures closed_store(s');
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
  else if (t.tapp? && step(t.f, s).Some?) {
    lemma_app_closed(t.f, t.arg);
    lemma_step_preserves_closed(t.f, s, step(t.f, s).get.fst, step(t.f, s).get.snd);
    assert closed(t');
  }
  /* App2 */
  else if (t.tapp? && step(t.arg, s).Some?) {
    lemma_app_closed(t.f, t.arg);
    lemma_step_preserves_closed(t.arg, s, step(t.arg, s).get.fst, step(t.arg, s).get.snd);
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
  else if (t.tif? && step(t.c, s).Some?) {
    lemma_if_closed(t.c, t.a, t.b);
    lemma_step_preserves_closed(t.c, s, step(t.c, s).get.fst, step(t.c, s).get.snd);
    assert closed(t');
  }
  /* RefValue */
  else if (t.tref? && value(t.r)) {
    assert t' == tloc(length(s.lst));
    var lst' := snoc(s.lst, t.r);
	  assert s' == Store(lst');
    assert lst' == snoc(s.lst, t.r);

    lemma_ref_closed(t.r);
    lemma_closed_tm_list_snoc(s.lst, t.r);
    lemma_closed_tm_list__closed_store(lst');

	  assert closed(t');
	  assert closed_store(s');
  }
  /* Ref */
  else if (t.tref? && step(t.r, s).Some?) {
  	lemma_ref_closed(t.r);
	  lemma_step_preserves_closed(t.r, s, step(t.r, s).get.fst, step(t.r, s).get.snd);
	  assert closed(t');
  }
  /* DerefLoc */
  else if (t.tderef? && t.d.tloc? && t.d.l < length(s.lst)) {
    assert t' == store_lookup(t.d.l, s);
    lemma_closed_store__closed_lookup(s, t.d.l);
	  assert closed(t');
  }
  /* Deref */
  else if (t.tderef? && step(t.d, s).Some?) {
	  lemma_deref_closed(t.d);
	  lemma_step_preserves_closed(t.d, s, step(t.d, s).get.fst, step(t.d, s).get.snd);
	  assert closed(t');
  }
  /* Assign */
  else if (t.tassign? && value(t.rhs) && t.lhs.tloc? && t.lhs.l < length(s.lst)) {
    assert t' == tunit;
    var lst' := replace(t.lhs.l, t.rhs, s.lst);
    assert s' == Store(lst');

    lemma_assign_closed(t.lhs, t.rhs);
    lemma_closed_tm_list_replace(s.lst, t.lhs.l, t.rhs);

	  assert closed(t');
    assert closed_store(s');
  }
  /* Assign1 */
  else if (t.tassign? && step(t.lhs, s).Some?) {
	  lemma_assign_closed(t.lhs, t.rhs);
	  lemma_step_preserves_closed(t.lhs, s, step(t.lhs, s).get.fst, step(t.lhs, s).get.snd);
	  assert closed(t');
  }
  /* Assign2 */
  else if (t.tassign? && value(t.lhs) && step(t.rhs, s).Some?) {
	  lemma_assign_closed(t.lhs, t.rhs);
	  lemma_step_preserves_closed(t.rhs, s, step(t.rhs, s).get.fst, step(t.rhs, s).get.snd);
	  assert closed(t');
  }
}

ghost method lemma_multistep_preserves_closed(t: tm, s: store, t': tm, s': store, i: nat)
  requires closed_store(s);
  requires closed(t);
  requires mstep(t, s, t', s', i);
  ensures closed(t');
  ensures closed_store(s');
  decreases i;
{
  if (i > 0) {
    lemma_step_preserves_closed(t, s, step(t, s).get.fst, step(t, s).get.snd);
    lemma_multistep_preserves_closed(step(t, s).get.fst, step(t, s).get.snd, t', s', i-1);
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
  forall t', s', n:nat :: mstep(t, Store(Nil), t', s', n) ==>
  value(t') || step(t', s').Some?
}
// TODO: Proof