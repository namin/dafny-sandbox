// Proving type safety of System F

/// Utilities

datatype option<A> = None | Some(get: A);
datatype pair<A,B> = P(fst: A, snd: B);

/// -----
/// Model
/// -----

/// Syntax

// Nominal Abstract Syntax
type Ty_Binder
type Tm_Binder
function ty_undo_bind(b: Ty_Binder): pair<int,ty>
function ty_bind(p: pair<int,ty>): Ty_Binder ensures ty_undo_bind(ty_bind(p))==p;
function tm_undo_bind(b: Tm_Binder): pair<int,tm>
function tm_bind(p: pair<int,tm>): Tm_Binder ensures tm_undo_bind(tm_bind(p))==p;
function ty_unbind(b: Ty_Binder, t: ty): pair<int,ty> { ty_unbind_without(b, t, {}) }
function tm_unbind(b: Tm_Binder, t: tm): pair<int,tm> { tm_unbind_without(b, t, {}) }
function ty_unbind_without(b: Ty_Binder, t: ty, s: set<int>): pair<int,ty> ensures ty_unbind_without(b, t, s).snd<ty_unbind_without(b, t, s)<t; ensures ty_unbind_without(b, t, s).fst !in s;
function tm_unbind_without(b: Tm_Binder, t: tm, s: set<int>): pair<int,tm> ensures tm_unbind_without(b, t, s).snd<tm_unbind_without(b, t, s)<t; ensures tm_unbind_without(b, t, s).fst !in s;

function var_swap(a: int, b: int, x: int): int
{
  if a==x then b else if b==x then a else x
}

function ty_swap(A: int, B: int, T: ty): ty
  decreases ty_size(T);
{
  match T
  case TVar(X) => TVar(var_swap(A, B, X))
  case TForall(b) =>
    var p := ty_undo_bind(b);
    assume ty_size(p.snd)==ty_size(ty_unbind(b, T).snd);
    TForall(ty_bind(P(p.fst, ty_swap(A, B, p.snd))))
  case TArrow(T1, T2) => TArrow(ty_swap(A, B, T1), ty_swap(A, B, T2))
  case TBase => TBase
}
function tm_swap(A: int, B: int, t: tm): tm
  decreases tm_size(t);
{
  match t
  case tyabs(b) =>
    var p := tm_undo_bind(b);
    assume tm_size(p.snd)==tm_size(tm_unbind(b, t).snd);
    tyabs(tm_bind(P(p.fst, tm_swap(A, B, p.snd))))
  case tvar(x) => t
  case tabs(x, T, t1) => tabs(x, T, tm_swap(A, B, t1))
  case tapp(t1, t2) => tapp(tm_swap(A, B, t1), tm_swap(A, B, t2))
  case tyapp(tf, targ) => tyapp(tm_swap(A, B, tf), ty_swap(A, B, targ))
}
predicate ty_alpha_eq(T1: ty, T2: ty)
  decreases ty_size(T1);
{
  match T1
  case TVar(X) => T1==T2
  case TBase => T1==T2
  case TArrow(T11, T12) => T2.TArrow? && ty_alpha_eq(T1.T1, T2.T1) && ty_alpha_eq(T1.T2, T2.T2)
  case TForall(b) => T2.TForall? && (
    var p1 := ty_undo_bind(T1.b);
    assume ty_size(p1.snd)==ty_size(ty_unbind(T1.b, T1).snd);
    var p2 := ty_undo_bind(T2.b);
    if (p1.fst==p2.fst) then ty_alpha_eq(p1.snd, p2.snd) else
    p1.fst !in ty_fv(p2.snd) && ty_alpha_eq(p1.snd, ty_swap(p1.fst, p2.fst, p2.snd))
  )
}
predicate tm_alpha_eq(t1: tm, t2: tm)
  decreases tm_size(t1);
{
  match t1
  case tyabs(b) => t2.tyabs? && (
    var p1 := tm_undo_bind(t1.b);
    assume tm_size(p1.snd)==tm_size(tm_unbind(t1.b, t1).snd);
    var p2 := tm_undo_bind(t2.b);
    if (p1.fst==p2.fst) then tm_alpha_eq(p1.snd, p2.snd) else
    p1.fst !in fv(p2.snd) && tm_alpha_eq(p1.snd, tm_swap(p1.fst, p2.fst, p2.snd))
  )
  case tvar(x) => t1==t2
  case tabs(x, T, body) => t2.tabs? && t1.x==t2.x && ty_alpha_eq(t1.T, t2.T) && tm_alpha_eq(t1.body, t2.body)
  case tapp(f, arg) => t2.tapp? && tm_alpha_eq(t1.f, t2.f) && tm_alpha_eq(t1.arg, t2.arg)
  case tyapp(tf, targ) => t2.tyapp? && tm_alpha_eq(t1.tf, t2.tf) && ty_alpha_eq(t1.targ, t2.targ)

}
predicate axiom_ty_alpha_eq(t1: ty, t2: ty)
  ensures ty_alpha_eq(t1, t2) <==> t1==t2;
predicate axiom_tm_alpha_eq(t1: tm, t2: tm)
  ensures tm_alpha_eq(t1, t2) <==> t1==t2;
ghost method nominal_axioms()
  ensures forall t1, t2 :: ty_alpha_eq(t1, t2) <==> t1==t2;
  ensures forall t1, t2 :: tm_alpha_eq(t1, t2) <==> t1==t2;
  ensures forall t:tm, p1, L1, p2, L2 :: (t.tyabs? && p1==tm_unbind_without(t.b, t, L1) && p2==tm_unbind_without(t.b, t, L2)) ==> tyabs(tm_bind(p1))==tyabs(tm_bind(p2));
  ensures forall t:tm :: t.tyabs? ==> forall p, L :: p==tm_unbind_without(t.b, t, L) ==> tm_size(t)>tm_size(p.snd);
  ensures forall t:ty, p1, L1, p2, L2 :: (t.TForall? && p1==ty_unbind_without(t.b, t, L1) && p2==ty_unbind_without(t.b, t, L2)) ==> TForall(ty_bind(p1))==TForall(ty_bind(p2));
  ensures forall t:ty :: t.TForall? ==> forall p, L :: p==ty_unbind_without(t.b, t, L) ==> ty_size(t)>ty_size(p.snd);

// Types
datatype ty =  TBase                             // (opaque base type)
            |  TArrow(T1: ty, T2: ty)            // T1 => T2
            |  TVar(id: int)
            |  TForall(b: Ty_Binder)
            ;

// Terms
datatype tm = tvar(id: int)                      // x                  (variable)
            | tapp(f: tm, arg: tm)               // t t                (application)
            | tabs(x: int, T: ty, body: tm)      // \x:T.t             (abstraction)
            | tyapp(tf: tm, targ: ty)
            | tyabs(b: Tm_Binder)
            ;
predicate axiom_tm_size(t: tm)
  ensures t.tyabs? ==> forall p, L :: p==tm_unbind_without(t.b, t, L) ==> tm_size(t)>tm_size(p.snd);
function tm_size(t: tm): nat
  ensures t.tapp? ==> tm_size(t)>tm_size(t.f);
{
  match t
  case tvar(x') => 1
  case tabs(x', T, t1) => 1+ty_size(T)+tm_size(t1)
  case tapp(t1, t2) => 1+tm_size(t1)+tm_size(t2)
  case tyabs(b) =>
    var p := tm_unbind(b, t);
    1+tm_size(p.snd)
  case tyapp(tf, targ) => 1+tm_size(tf)+ty_size(targ)
}
predicate axiom_ty_size(T: ty)
  ensures T.TForall? ==> forall p, L :: p==ty_unbind_without(T.b, T, L) ==> ty_size(T)>ty_size(p.snd);
function ty_size(T: ty): nat
  ensures T.TArrow? ==> ty_size(T)>ty_size(T.T1);
{
  match T
  case TVar(id) => 1
  case TForall(b) =>
    var p := ty_unbind(b, T);
    1+ty_size(p.snd)
  case TArrow(T1, T2) => 1+ty_size(T1)+ty_size(T2)
  case TBase => 1
}

/// Operational Semantics

// Values
predicate value(t: tm)
{
  t.tabs?
  || t.tyabs?
}

// Free Variables and Substitution

function fv(t: tm): set<int> //of free variables of t
  decreases tm_size(t);
{
  match t
  // interesting cases...
  case tvar(id) => {id}
  case tabs(x, T, body) => fv(body)-{x}//x is bound
  // congruent cases...
  case tapp(f, arg) => fv(f)+fv(arg)
  case tyabs(b) => var p := tm_unbind(b, t); fv(p.snd)
  case tyapp(tf, targ) => fv(tf)
}

function subst(x: int, s: tm, t: tm): tm //[x -> s]t
  decreases tm_size(t);
{
  match t
  // interesting cases...
  case tvar(x') => if x==x' then s else t
  // N.B. only capture-avoiding if s is closed...
  case tabs(x', T, t1) => tabs(x', T, if x==x' then t1 else subst(x, s, t1))
  // congruent cases...
  case tapp(t1, t2) => tapp(subst(x, s, t1), subst(x, s, t2))
  case tyabs(b) => var p := tm_unbind(b, t); tyabs(tm_bind(P(p.fst, subst(x, s, p.snd))))
  case tyapp(tf, targ) => tyapp(subst(x, s, tf), targ)
}

function ty_fv(T: ty): set<int> //of free variables of T
  decreases ty_size(T);
{
  match T
  // interesting cases...
  case TVar(id) => {id}
  case TForall(b) => var p := ty_unbind(b, T); ty_fv(p.snd)-{p.fst}
  // congruent cases...
  case TArrow(T1, T2) => ty_fv(T1)+ty_fv(T2)
  case TBase => {}
}
function ty_tm_fv(t: tm): set<int> //of free type variables of t
  decreases tm_size(t);
{
  match t
  // interesting cases...
  case tyabs(b) => var p := tm_unbind(b, t); ty_tm_fv(p.snd)-{p.fst}
  // congruent cases...
  case tvar(id) => {}
  case tabs(x, T, body) => ty_fv(T)+ty_tm_fv(body)
  case tapp(f, arg) => ty_tm_fv(f)+ty_tm_fv(arg)
  case tyapp(tf, targ) => ty_tm_fv(tf)+ty_fv(targ)
}

function ty_ty_subst(X: int, S: ty, T: ty): ty //[X -> S]T
  decreases ty_size(T);
{
  match T
  // interesting cases...
  case TVar(X') => if X'==X then S else T
  case TForall(b) =>
    var p := ty_unbind_without(b, T, ty_fv(S));
    var _ := axiom_ty_size(T);
    TForall(ty_bind(P(p.fst, ty_ty_subst(X, S, p.snd))))
  // congruent cases...
  case TArrow(T1, T2) => TArrow(ty_ty_subst(X, S, T1), ty_ty_subst(X, S, T2))
  case TBase => TBase
}

function ty_tm_subst(X: int, S: ty, t: tm): tm //[X -> S]t
  decreases tm_size(t);
{
  match t
  // interesting cases...
  case tyabs(b) =>
    var p := tm_unbind_without(b, t, ty_fv(S));
    var _ := axiom_tm_size(t);
    tyabs(tm_bind(P(p.fst, ty_tm_subst(X, S, p.snd))))
  // congruent cases...
  case tvar(x) => t
  case tabs(x, T, t1) => tabs(x, T, ty_tm_subst(X, S, t1))
  case tapp(t1, t2) => tapp(ty_tm_subst(X, S, t1), ty_tm_subst(X, S, t2))
  case tyapp(tf, targ) => tyapp(ty_tm_subst(X, S, tf), ty_ty_subst(X, S, targ))
}

// Reduction
function step(t: tm): option<tm>
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then
  Some(subst(t.f.x, t.arg, t.f.body))
  /* App1 */       else if (t.tapp? && step(t.f).Some?) then
  Some(tapp(step(t.f).get, t.arg))
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg).Some?) then
  Some(tapp(t.f, step(t.arg).get))
  /* TyAppTyAbs */ else if (t.tyapp? && t.tf.tyabs?) then
  var p := tm_unbind(t.tf.b, t);
  Some(ty_tm_subst(p.fst, t.targ, p.snd))
  /* TyApp */      else if (t.tyapp? && step(t.tf).Some?) then
  Some(tyapp(step(t.tf).get, t.targ))
  else None
}

// Multistep reduction:
// The term t reduces to the term t' in n or less number of steps.
predicate reduces_to(t: tm, t': tm, n: nat)
  decreases n;
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
}

// Examples
ghost method lemma_step_example1(n: nat)
  requires n > 0;
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
}


/// Typing

// A context is a partial map from variable names to types.
function find(c: map<int,ty>, x: int): option<ty>
{
  if (x in c) then Some(c[x]) else None
}
function extend(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x:=T]
}

ghost method lemma_seq_assoc<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)
  ensures s1+s2+s3==s1+(s2+s3);
{
}

predicate wf(T: ty, L: set<int>)
{
  forall x :: x in ty_fv(T) ==> x in L
}

// Typing Relation
function has_type(c: map<int,ty>, t: tm, L: set<int>): option<ty>
  decreases tm_size(t);
{
  match t
  /* Var */  case tvar(id) => find(c, id)
  /* Abs */  case tabs(x, T, body) =>
  if wf(T, L) then
  var ty_body := has_type(extend(x, T, c), body, L);
                     if (ty_body.Some?) then
  Some(TArrow(T, ty_body.get))          else None else None
  /* App */  case tapp(f, arg) =>
  var ty_f   := has_type(c, f, L);
  var ty_arg := has_type(c, arg, L);
                     if (ty_f.Some? && ty_arg.Some?) then
  if ty_f.get.TArrow? && ty_f.get.T1==ty_arg.get then
  Some(ty_f.get.T2)  else None else None
  /* TyApp */ case tyapp(f, ty_arg) =>
  if wf(ty_arg, L) then
  var ty_f    := has_type(c, f, L);
                      if (ty_f.Some?) then
  if (ty_f.get.TForall?) then
  var p_f := ty_unbind(ty_f.get.b, ty_f.get);
  Some(ty_ty_subst(p_f.fst, ty_arg, p_f.snd)) else None else None else None
  /* TyAbs */ case tyabs(b) =>
  var p := tm_unbind_without(b, t, L);
  var _ := axiom_tm_size(t);
  var ty_body  := has_type(c, p.snd, L+{p.fst});
                      if (ty_body.Some?) then
  Some(TForall(ty_bind(P(p.fst, ty_body.get)))) else None
}

// Examples

ghost method example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0)), {}) == Some(TArrow(TBase, TBase));
{
}

ghost method example_typing_2()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0))))), {}) ==
          Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
{
  var c := extend(1, TArrow(TBase, TBase), extend(0, TBase, map[]));
  assert find(c, 0) == Some(TBase);
  assert has_type(c, tvar(0), {}) == Some(TBase);
  assert has_type(c, tvar(1), {}) == Some(TArrow(TBase, TBase));
  assert has_type(c, tapp(tvar(1), tvar(0)), {}) == Some(TBase);
  assert has_type(c, tapp(tvar(1), tapp(tvar(1), tvar(0))), {}) == Some(TBase);
}

ghost method nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1)))), {}) == None;
{
  var c := extend(1, TBase, extend(0, TBase, map[]));
  assert find(c, 0) == Some(TBase);
  assert has_type(c, tapp(tvar(0), tvar(1)), {}) == None;
}

/// -----------------------
/// Type-Safety Properties
/// -----------------------

// Progress:
// A well-typed term is either a value or it can step.
ghost method theorem_progress(t: tm)
  requires has_type(map[], t, {}).Some?;
  ensures value(t) || step(t).Some?;
{
}

// Towards preservation and the substitution lemma

// If x is free in t and t is well-typed in some context,
// then this context must contain x.
ghost method {:induction c, t, L} lemma_free_in_context(c: map<int,ty>, x: int, t: tm, L: set<int>)
  requires x in fv(t);
  requires has_type(c, t, L).Some?;
  ensures find(c, x).Some?;
  decreases tm_size(t);
{
  nominal_axioms();
  if (t.tyabs?) {
    var p := tm_unbind_without(t.b, t, L);
    lemma_free_in_context(c, x, p.snd, L+{p.fst});
  }
}

// A closed term does not contain any free variables.
// N.B. We're only interested in proving type soundness of closed terms.
predicate closed(t: tm)
{
  forall x :: x !in fv(t)
}

// If a term can be well-typed in an empty context,
// then it is closed.
ghost method corollary_typable_empty__closed(t: tm, L: set<int>)
  requires has_type(map[], t, L).Some?;
  ensures closed(t);
{
  forall (x:int) ensures x !in fv(t);
  {
    if (x in fv(t)) {
      lemma_free_in_context(map[], x, t, L);
      assert false;
    }
  }
}

// If a term t is well-typed in context c,
//    and context c' agrees with c on all free variables of t,
// then the term t is well-typed in context c',
//      with the same type as in context c.
ghost method lemma_context_invariance(c: map<int,ty>, c': map<int,ty>, t: tm, L: set<int>)
  requires has_type(c, t, L).Some?;
  requires forall x: int :: x in fv(t) ==> find(c, x).Some? && find(c', x).Some? && find(c, x).get==find(c', x).get;
  ensures has_type(c', t, L).Some?;
  ensures has_type(c, t, L).get==has_type(c', t, L).get;
  decreases t;
{
  nominal_axioms();
  var T := has_type(c, t, L).get;
  if (t.tyabs?) {
    var p := tm_unbind_without(t.b, t, L);
    var L' := L+{p.fst};
    lemma_context_invariance(c, c', p.snd, L');
  }
}

ghost method lemma_L_invariance(c: map<int,ty>, t: tm, L: set<int>, L': set<int>)
  requires has_type(c, t, L).Some?;
  ensures has_type(c, t, L+L').Some?;
  ensures has_type(c, t, L).get==has_type(c, t, L+L').get;
  decreases tm_size(t);
{
  nominal_axioms();
  if (t.tyabs?) {
    var p := tm_unbind_without(t.b, t, L+L');
    lemma_L_invariance(c, p.snd, L+{p.fst}, L');
    // TODO
    assume has_type(c, t, L+L').Some?;
    assume has_type(c, t, L).get==has_type(c, t, L+L').get;
  }
}

// Substitution preserves typing:
// If  s has type S in an empty context,
// and t has type T in a context extended with x having type S,
// then [x -> s]t has type T as well.
ghost method lemma_substitution_preserves_typing(c: map<int,ty>, x: int, s: tm, S: ty, t: tm, L: set<int>)
  requires has_type(map[], s, L).Some?;
  requires has_type(map[], s, L).get==S;
  requires has_type(extend(x, S, c), t, L).Some?;
  ensures has_type(c, subst(x, s, t), L).Some?;
  ensures has_type(c, subst(x, s, t), L).get==has_type(extend(x, S, c), t, L).get;
  decreases t;
{
  nominal_axioms();
  var cs := extend(x, S, c);
  var T  := has_type(cs, t, L).get;
  if (t.tvar?) {
    if (t.id==x) {
      assert T == S;
      corollary_typable_empty__closed(s, L);
      lemma_context_invariance(map[], c, s, L);
    }
  } else if (t.tabs?) {
    if (t.x==x) {
      assert x !in fv(t);
      forall (x | x in fv(t))
      ensures find(c, x).Some? && find(cs, x).Some? && find(c, x).get==find(cs, x).get;
      {
        lemma_free_in_context(cs, x, t, L);
      }
      lemma_context_invariance(cs, c, t, L);
    } else {
      var cx  := extend(t.x, t.T, c);
      var csx := extend(x, S, cx);
      var cxs := extend(t.x, t.T, cs);
      forall (x | x in fv(t.body))
      ensures find(csx, x).Some? && find(cxs, x).Some? && find(csx, x).get==find(cxs, x).get;
      {
        lemma_free_in_context(cxs, x, t.body, L);
      }

      lemma_context_invariance(cxs, csx, t.body, L);
      lemma_substitution_preserves_typing(cx, x, s, S, t.body, L);
    }
  } else if (t.tapp?) {
    lemma_substitution_preserves_typing(c, x, s, S, t.f, L);
    lemma_substitution_preserves_typing(c, x, s, S, t.arg, L);
  } else if (t.tyabs?) {
    var p := tm_unbind_without(t.b, t, L);
    lemma_L_invariance(map[], s, L, {p.fst});
    lemma_substitution_preserves_typing(c, x, s, S, p.snd, L+{p.fst});
     assume has_type(c, subst(x, s, t), L).Some?;
     assume has_type(c, subst(x, s, t), L).get==has_type(extend(x, S, c), t, L).get;
  } else if (t.tyapp?) {
    lemma_substitution_preserves_typing(c, x, s, S, t.tf, L);
  }
}

// Preservation:
// A well-type term which steps preserves its type.
ghost method theorem_preservation(t: tm, L: set<int>)
  requires has_type(map[], t, L).Some?;
  requires step(t).Some?;
  ensures has_type(map[], step(t).get, L).Some?;
  ensures has_type(map[], step(t).get, L).get==has_type(map[], t, L).get;
{
  nominal_axioms();
  if (t.tapp? && value(t.f) && value(t.arg)) {
    lemma_substitution_preserves_typing(map[], t.f.x, t.arg, t.f.T, t.f.body, L);
  }
  /* App1 */       else if (t.tapp? && step(t.f).Some?) {
    theorem_preservation(t.f, L);
  }
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg).Some?) {}
  /* TyAppTyAbs */ else if (t.tyapp? && t.tf.tyabs?) {
    assume has_type(map[], step(t).get, L).Some?;
    assume has_type(map[], step(t).get, L).get==has_type(map[], t, L).get;
  }
  /* TyApp */      else if (t.tyapp? && step(t.tf).Some?) {}
  else {}
}

// A normal form cannot step.
predicate normal_form(t: tm)
{
  step(t).None?
}

// A stuck term is a normal form that is not a value.
predicate stuck(t: tm)
{
  normal_form(t) && !value(t)
}

// Type soundness:
// A well-typed term cannot be stuck.
ghost method corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(map[], t, {}).Some?;
  requires has_type(map[], t, {}).get==T;
  requires reduces_to(t, t', n);
  ensures !stuck(t');
  decreases n;
{
  nominal_axioms();
  theorem_progress(t);
  if (t != t') {
   theorem_preservation(t, {});
   var T' := has_type(map[], step(t).get, {}).get;
   corollary_soundness(step(t).get, t', T', n-1);
  }
}
/// QED
