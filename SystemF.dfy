// Proving type safety of System F

/// Utilities

// ... handy for partial functions
datatype option<A> = None | Some(get: A);

/// -----
/// Model
/// -----

/// Syntax

// Types
datatype ty =  TBase                             // (opaque base type)
            |  TArrow(T1: ty, T2: ty)            // T1 => T2
            |  TVar(id: int)
            |  TForall(x: int, body: ty)
            ;

// Terms
datatype tm = tvar(id: int)                      // x                  (variable)
            | tapp(f: tm, arg: tm)               // t t                (application)
            | tabs(x: int, T: ty, body: tm)      // \x:T.t             (abstraction)
            | tyapp(tf: tm, targ: ty)
            | tyabs(tx: int, tbody: tm)
            ;

/// Operational Semantics

// Values
predicate value(t: tm)
{
  t.tabs?
  || t.tyabs?
}

// Free Variables and Substitution

function fv(t: tm): set<int> //of free variables of t
{
  match t
  // interesting cases...
  case tvar(id) => {id}
  case tabs(x, T, body) => fv(body)-{x}//x is bound
  // congruent cases...
  case tapp(f, arg) => fv(f)+fv(arg)
  case tyabs(x, body) => fv(body)
  case tyapp(tf, targ) => fv(tf)
}

function subst(x: int, s: tm, t: tm): tm //[x -> s]t
{
  match t
  // interesting cases...
  case tvar(x') => if x==x' then s else t
  // N.B. only capture-avoiding if s is closed...
  case tabs(x', T, t1) => tabs(x', T, if x==x' then t1 else subst(x, s, t1))
  // congruent cases...
  case tapp(t1, t2) => tapp(subst(x, s, t1), subst(x, s, t2))
  case tyabs(x', body) => tyabs(x', subst(x, s, body))
  case tyapp(tf, targ) => tyapp(subst(x, s, tf), targ)
}

function tm_size(t: tm): nat
  ensures t.tapp? ==> tm_size(t)>tm_size(t.f);
{
  match t
  case tvar(x') => 1
  case tabs(x', T, t1) => 1+ty_size(T)+tm_size(t1)
  case tapp(t1, t2) => 1+tm_size(t1)+tm_size(t2)
  case tyabs(x', body) => 1+tm_size(body)
  case tyapp(tf, targ) => 1+tm_size(tf)+ty_size(targ)
}
function ty_size(T: ty): nat
  ensures T.TArrow? ==> ty_size(T)>ty_size(T.T1);
{
  match T
  case TVar(id) => 1
  case TForall(X, body) => 1+ty_size(body)
  case TArrow(T1, T2) => 1+ty_size(T1)+ty_size(T2)
  case TBase => 1
}

function ty_fv(T: ty): set<int> //of free variables of T
{
  match T
  // interesting cases...
  case TVar(id) => {id}
  case TForall(X, body) => ty_fv(body)-{X}//x is bound
  // congruent cases...
  case TArrow(T1, T2) => ty_fv(T1)+ty_fv(T2)
  case TBase => {}
}
function ty_tm_fv(t: tm): set<int> //of free type variables of t
{
  match t
  // interesting cases...
  case tyabs(x, body) => ty_tm_fv(body)-{x}
  // congruent cases...
  case tvar(id) => {}
  case tabs(x, T, body) => ty_fv(T)+ty_tm_fv(body)
  case tapp(f, arg) => ty_tm_fv(f)+ty_tm_fv(arg)
  case tyapp(tf, targ) => ty_tm_fv(tf)+ty_fv(targ)
}

function not_in(s: set<int>, r: nat): nat
{
  if (!exists x :: x in s) then r+1 else
  var x :| x in s;
  if (x<r) then not_in(s-{x}, r) else not_in(s-{x}, r)
}

function ty_var_swap(X: int, Y: int, Z: int): int
{
  if X==Z then Y else if Y==Z then X else Z
}
ghost method sym_ty_var_swap(X: int, Y: int, Z: int)
  ensures ty_var_swap(X, Y, Z)==ty_var_swap(Y, X, Z);
{
}
function ty_ty_swap(X: int, Y: int, T: ty): ty
  ensures ty_size(T)==ty_size(ty_ty_swap(X, Y, T));
{
  match T
  case TVar(X') => TVar(ty_var_swap(X, Y, X'))
  case TForall(X', body) => TForall(ty_var_swap(X, Y, X'), ty_ty_swap(X, Y, body))
  case TArrow(T1, T2) => TArrow(ty_ty_swap(X, Y, T1), ty_ty_swap(X, Y, T2))
  case TBase => TBase
}
ghost method sym_ty_ty_swap(X: int, Y: int, T: ty)
  ensures ty_ty_swap(X, Y, T)==ty_ty_swap(Y, X, T);
{
}
function ty_tm_swap(X: int, Y: int, t: tm): tm
{
  match t
  case tyabs(X', body) => tyabs(ty_var_swap(X, Y, X'), ty_tm_swap(X, Y, body))
  case tvar(x) => t
  case tabs(x, T, t1) => tabs(x, ty_ty_swap(X, Y, T), ty_tm_swap(X, Y, t1))
  case tapp(t1, t2) => tapp(ty_tm_swap(X, Y, t1), ty_tm_swap(X, Y, t2))
  case tyapp(tf, targ) => tyapp(ty_tm_swap(X, Y, tf), ty_ty_swap(X, Y, targ))
}
ghost method sym_ty_tm_swap(X: int, Y: int, t: tm)
  ensures ty_tm_swap(X, Y, t)==ty_tm_swap(Y, X, t);
{
  if (t.tabs?) {
    sym_ty_ty_swap(X, Y, t.T);
  } else if (t.tyapp?) {
    sym_ty_ty_swap(X, Y, t.targ);
  }
}

predicate ty_eq(T1: ty, T2: ty)
  ensures ty_eq(T1, T2) ==> ((T1.TArrow? <==> T2.TArrow?) &&
                             (T1.TBase? <==> T2.TBase?) &&
                             (T1.TVar? <==> T2.TVar?) &&
                             (T1.TForall? <==> T2.TForall?) &&
                             ((T1.TArrow? && T2.TArrow?) ==> (ty_eq(T1.T1, T2.T1) && ty_eq(T1.T2, T2.T2))));
  decreases ty_size(T1);
{
  match T1
  case TBase => T2==T1
  case TVar(X1) => T2==T1
  case TForall(X1, body1) => T2.TForall? && (
     if (T2.x==X1) then ty_eq(body1, T2.body) else
     T2.x !in ty_fv(body1) &&
     ty_eq(body1, ty_ty_swap(X1, T2.x, T2.body))
  )
  case TArrow(T11, T12) => T2.TArrow? && ty_eq(T11, T2.T1) && ty_eq(T12, T2.T2)
}
ghost method lemma_ty_eq_swap_fv(X: int, Y: int, T: ty)
  ensures forall Z :: Z in ty_fv(T) && Z!=X && Z!=Y ==> Z in ty_fv(ty_ty_swap(X, Y, T));
  ensures forall Z :: Z !in ty_fv(T) && Z!=X && Z!=Y ==> Z !in ty_fv(ty_ty_swap(X, Y, T));
  ensures X in ty_fv(T) <==> Y in ty_fv(ty_ty_swap(X, Y, T));
  ensures X !in ty_fv(T) <==> Y !in ty_fv(ty_ty_swap(X, Y, T));
  ensures Y in ty_fv(T) <==> X in ty_fv(ty_ty_swap(X, Y, T));
  ensures Y !in ty_fv(T) <==> X !in ty_fv(ty_ty_swap(X, Y, T));
{
}
ghost method axiom_set_extensionality(s1: set<int>, s2: set<int>)
  requires forall Z :: Z in s1 <==> Z in s2;
  ensures s1 == s2;
{
}
ghost method lemma_ty_eq_fv(T1: ty, T2: ty)
  requires ty_eq(T1, T2);
  ensures ty_fv(T1)==ty_fv(T2);
{
  if (T1.TForall? && T2.TForall? && T2.x!=T1.x) {
    lemma_ty_eq_swap_fv(T1.x, T2.x, T2.body);
    axiom_set_extensionality(ty_fv(T1), ty_fv(T2));
  }
}
ghost method refl_ty_eq(T: ty)
  ensures ty_eq(T, T);
{
}
ghost method sym_ty_eq(T1: ty, T2: ty)
  requires ty_eq(T1, T2);
  ensures ty_eq(T2, T1);
{
  assume ty_eq(T2, T1);
}
ghost method trans_ty_eq(T1: ty, T2: ty, T3: ty)
  requires ty_eq(T1, T2);
  requires ty_eq(T2, T3);
  ensures ty_eq(T1, T3);
{
  assume ty_eq(T1, T3);
}

function ty_ty_subst(X: int, S: ty, T: ty): ty //[X -> S]T
  ensures S.TVar? ==> ty_size(ty_ty_subst(X, S, T))==ty_size(T);
  decreases ty_size(T);
{
  match T
  // interesting cases...
  case TVar(X') => if X'==X then S else T
  case TForall(X', body) =>
    if X'==X then T
    else if X' in ty_fv(S) then
      // capture-avoiding substitution
      var X'' := not_in(ty_fv(S)+{X}+ty_fv(T), 0);
      TForall(X'', ty_ty_subst(X, S, ty_ty_subst(X', TVar(X''), body)))
    else TForall(X', ty_ty_subst(X, S, body))
  // congruent cases...
  case TArrow(T1, T2) => TArrow(ty_ty_subst(X, S, T1), ty_ty_subst(X, S, T2))
  case TBase => TBase
}

function ty_tm_subst(X: int, S: ty, t: tm): tm //[X -> S]t
  ensures S.TVar? ==> tm_size(ty_tm_subst(X, S, t))==tm_size(t);
  decreases tm_size(t);
{
  match t
  // interesting cases...
  case tyabs(X', body) =>
    if X'==X then t
    else if X' in ty_fv(S) then
      // capture-avoiding substitution
      var X'' := not_in(ty_fv(S)+{X}+ty_tm_fv(t), 0);
      tyabs(X'', ty_tm_subst(X, S, ty_tm_subst(X', TVar(X''), body)))
    else tyabs(X', ty_tm_subst(X, S, body))
  // congruent cases...
  case tvar(x) => t
  case tabs(x, T, t1) => tabs(x, T, ty_tm_subst(X, S, t1))
  case tapp(t1, t2) => tapp(ty_tm_subst(X, S, t1), ty_tm_subst(X, S, t2))
  case tyapp(tf, targ) => tyapp(ty_tm_subst(X, S, tf), ty_ty_subst(X, S, targ))
}

ghost method lemma_ty_ty_subst_eq1(X: int, S: ty, T1: ty, T2: ty)
  requires ty_eq(T1, T2);
  ensures ty_eq(ty_ty_subst(X, S, T1), ty_ty_subst(X, S, T2));
{
  assume ty_eq(ty_ty_subst(X, S, T1), ty_ty_subst(X, S, T2));
}
ghost method lemma_ty_ty_subst_eq2(X: int, S1: ty, S2: ty, T: ty)
  requires ty_eq(S1, S2);
  ensures ty_eq(ty_ty_subst(X, S1, T), ty_ty_subst(X, S2, T));
{
  assume ty_eq(ty_ty_subst(X, S1, T), ty_ty_subst(X, S2, T));
}
ghost method lemma_ty_ty_subst_eq3(S: ty, T1: ty, T2: ty)
  requires T1.TForall? && T2.TForall?;
  requires ty_eq(T1, T2);
  ensures ty_eq(ty_ty_subst(T1.x, S, T1.body), ty_ty_subst(T2.x, S, T2.body));
{
  assume ty_eq(ty_ty_subst(T1.x, S, T1.body), ty_ty_subst(T2.x, S, T2.body));
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
  Some(ty_tm_subst(t.tf.tx, t.targ, t.tf.tbody))
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
  decreases t;
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
  if ty_f.get.TArrow? && ty_eq(ty_f.get.T1, ty_arg.get) then
  Some(ty_f.get.T2)  else None else None
  /* TyApp */ case tyapp(f, ty_arg) =>
  var ty_f    := has_type(c, f, L);
                      if (ty_f.Some?) then
  if (ty_f.get.TForall?) then
  Some(ty_ty_subst(ty_f.get.x, ty_arg, ty_f.get.body)) else None else None
  /* TyAbs */ case tyabs(x, body) =>
  var ty_body  := has_type(c, body, L+{x});
                      if (ty_body.Some?) then
  Some(TForall(x, ty_body.get))          else None
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
}

ghost method nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1)))), {}) == None;
{
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
  decreases t;
{
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

ghost method {:timeLimit 20} boilerplate_lemmas()
  ensures forall T1 :: ty_eq(T1, T1);
  ensures forall T1, T2, T3 :: ty_eq(T1, T2) && ty_eq(T2, T3) ==> ty_eq(T1, T3);
  ensures forall T1, T2 :: ty_eq(T1, T2) ==> ty_eq(T2, T1);
  ensures forall X, S, T1, T2 :: ty_eq(T1, T2) ==> ty_eq(ty_ty_subst(X, S, T1), ty_ty_subst(X, S, T2));
  ensures forall X, S1, S2, T :: ty_eq(S1, S2) ==> ty_eq(ty_ty_subst(X, S1, T), ty_ty_subst(X, S2, T));
  ensures forall S, T1:ty, T2: ty :: (T1.TForall? && T2.TForall? && ty_eq(T1, T2)) ==> ty_eq(ty_ty_subst(T1.x, S, T1.body), ty_ty_subst(T2.x, S, T2.body));
{
  forall (T1)
  ensures ty_eq(T1, T1);
  {
    refl_ty_eq(T1);
  }
  forall (T1, T2, T3 | ty_eq(T1, T2) && ty_eq(T2, T3))
  ensures ty_eq(T1, T3);
  {
    trans_ty_eq(T1, T2, T3);
  }
  forall (T1, T2 | ty_eq(T1, T2))
  ensures ty_eq(T2, T1);
  {
    sym_ty_eq(T1, T2);
  }
  forall (X, S, T1, T2 | ty_eq(T1, T2))
  ensures ty_eq(ty_ty_subst(X, S, T1), ty_ty_subst(X, S, T2));
  {
    lemma_ty_ty_subst_eq1(X, S, T1, T2);
  }
  forall (X, S1, S2, T | ty_eq(S1, S2))
  ensures ty_eq(ty_ty_subst(X, S1, T), ty_ty_subst(X, S2, T));
  {
    lemma_ty_ty_subst_eq2(X, S1, S2, T);
  }
  forall (S, T1:ty, T2:ty | T1.TForall? && T2.TForall? && ty_eq(T1, T2))
  ensures ty_eq(ty_ty_subst(T1.x, S, T1.body), ty_ty_subst(T2.x, S, T2.body));
  {
    lemma_ty_ty_subst_eq3(S, T1, T2);
  }
}
// If a term t is well-typed in context c,
//    and context c' agrees with c on all free variables of t,
// then the term t is well-typed in context c',
//      with the same type as in context c.
ghost method lemma_context_invariance(c: map<int,ty>, c': map<int,ty>, t: tm, L: set<int>)
  requires has_type(c, t, L).Some?;
  requires forall x: int :: x in fv(t) ==> find(c, x).Some? && find(c', x).Some? && ty_eq(find(c, x).get, find(c', x).get);
  ensures has_type(c', t, L).Some?;
  ensures ty_eq(has_type(c, t, L).get, has_type(c', t, L).get);
  decreases t;
{
  boilerplate_lemmas();
  var T := has_type(c, t, L).get;
  if (t.tvar?) {}
  else if (t.tapp?) {
    lemma_context_invariance(c, c', t.f, L);
    lemma_context_invariance(c, c', t.arg, L);
    var ty_f := has_type(c, t.f, L).get;
    var ty_f' := has_type(c', t.f, L).get;
    var ty_arg := has_type(c, t.arg, L).get;
    var ty_arg' := has_type(c', t.arg, L).get;
    assert ty_eq(ty_f, ty_f');
    assert ty_eq(ty_arg, ty_arg');
  }
  else if (t.tabs?) {
    lemma_context_invariance(extend(t.x, t.T, c), extend(t.x, t.T, c'), t.body, L); 
  }
  else if (t.tyabs?) {
    var L' := L+{t.tx};
    lemma_context_invariance(c, c', t.tbody, L');
  }
  else if (t.tyapp?) {
    var ty_f  := has_type(c, t.tf, L);
    var ty_f' := has_type(c', t.tf, L);
    lemma_context_invariance(c, c', t.tf, L);
    assert ty_eq(ty_f.get, ty_f'.get);
  }
  else {}
}

/*
// TODO
// finish it up
/*
// Substitution preserves typing:
// If  s has type S in an empty context,
// and t has type T in a context extended with x having type S,
// then [x -> s]t has type T as well.
ghost method lemma_substitution_preserves_typing(c: map<int,ty>, x: int, s: tm, t: tm, L: set<int>)
  requires has_type(map[], s, L).Some?;
  requires has_type(extend(x, has_type(map[], s, L).get, c), t, L).Some?;
  ensures has_type(c, subst(x, s, t), L).Some?;
  ensures ty_eq(has_type(c, subst(x, s, t), L).get, has_type(extend(x, has_type(map[], s, L).get, c), t, L).get, {});
  decreases t;
{
  var S := has_type(map[], s, L).get;
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
      lemma_context_invariance(cs, c, t, L);
    } else {
      var cx  := extend(t.x, t.T, c);
      var csx := extend(x, S, cx);
      var cxs := extend(t.x, t.T, cs);
      lemma_context_invariance(cxs, csx, t.body, L);
      lemma_substitution_preserves_typing(cx, x, s, t.body, L);
    }
  }
}


// Preservation:
// A well-type term which steps preserves its type.
ghost method theorem_preservation(t: tm, L: set<int>)
  requires has_type(map[], t, L).Some?;
  requires step(t).Some?;
  ensures has_type(map[], step(t).get, L).Some?;
  ensures ty_eq(has_type(map[], step(t).get, L).get, has_type(map[], t, L).get, L);
{
  if (t.tapp? && value(t.f) && value(t.arg)) {
    lemma_substitution_preserves_typing(map[], t.f.x, t.arg, t.f.body, L);
  }
  /* TyAppTyAbs */ else if (t.tyapp? && t.tf.tyabs?) {}
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
  requires ty_eq(has_type(map[], t, {}).get, T, {});
  requires reduces_to(t, t', n);
  ensures !stuck(t');
  decreases n;
{
  theorem_progress(t);
  if (t != t') {
   theorem_preservation(t, {});
   var T' := has_type(map[], step(t).get, {}).get;
   corollary_soundness(step(t).get, t', T', n-1);
  }
}
*/
/// QED
*/