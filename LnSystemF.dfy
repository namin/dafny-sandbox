datatype option<A> = None | Some(get: A);
function chain(a: option, b: option): option
{
  if (a.None?) then b else a
}

datatype pair<A,B> = P(fst: A, snd: B);

function not_in(s: set<int>, r: nat, sr: set<int>, so: set<int>): nat
  requires forall x :: x in sr ==> x<=r;
  requires s+sr==so;
  ensures not_in(s, r, sr, so) !in so;
{
  if (!exists x :: x in s) then r+1 else
  var x :| x in s;
  if (x<r) then not_in(s-{x}, r, sr+{x}, so) else not_in(s-{x}, x, sr+{x}, so)
}
function notin(s: set<int>): int
  ensures notin(s) !in s;
{
  not_in(s, 0, {}, s)
}

/// Definition of System F
/// https://github.com/plclub/metalib/blob/master/Fsub_LetSum_Definitions.v

datatype typ =
    typ_top
  | typ_bvar(n: nat)
  | typ_fvar(a: int)
  | typ_arrow(ty1: typ, ty2: typ)
  | typ_all(ty0: typ)

datatype exp =
    exp_bvar(n: nat)
  | exp_fvar(a: int)
  | exp_abs(ty: typ, e0: exp)
  | exp_app(f: exp, arg: exp)
  | exp_tabs(te0: exp)
  | exp_tapp(tf: exp, targ: typ)

function typ_size(T: typ): nat
{
  match T
  case typ_top => 1
  case typ_bvar(J) => 1
  case typ_fvar(X) => 1
  case typ_arrow(T1, T2) => 1+typ_size(T1)+typ_size(T2)
  case typ_all(T1) => 1+typ_size(T1)
}
function exp_size(e: exp): nat
{
  match e
  case exp_bvar(i) => 1
  case exp_fvar(x) => 1
  case exp_abs(V, e1) => 1+typ_size(V)+exp_size(e1)
  case exp_app(e1, e2) => 1+exp_size(e1)+exp_size(e2)
  case exp_tabs(e1) => 1+exp_size(e1)
  case exp_tapp(e1, V) => 1+exp_size(e1)+typ_size(V)
}

function open_tt_rec(K : nat, U : typ, T : typ): typ
  ensures U.typ_fvar? ==> typ_size(T)==typ_size(open_tt_rec(K, U, T));
  decreases T;
{
  match T
  case typ_top => typ_top
  case typ_bvar(J) => if K == J then U else typ_bvar(J)
  case typ_fvar(X) => typ_fvar(X)
  case typ_arrow(T1, T2) => typ_arrow(open_tt_rec(K, U, T1), open_tt_rec(K, U, T2))
  case typ_all(T1) => typ_all(open_tt_rec(K+1, U, T1))
}
function open_te_rec(K : nat, U : typ, e : exp): exp
  ensures U.typ_fvar? ==> exp_size(e)==exp_size(open_te_rec(K, U, e));
  decreases e;
{
  match e
  case exp_bvar(i) => exp_bvar(i)
  case exp_fvar(x) => exp_fvar(x)
  case exp_abs(V, e1) => exp_abs(open_tt_rec(K, U, V), open_te_rec(K, U, e1))
  case exp_app(e1, e2) => exp_app(open_te_rec(K, U, e1), open_te_rec(K, U, e2))
  case exp_tabs(e1) => exp_tabs(open_te_rec(K+1, U, e1))
  case exp_tapp(e1, V) => exp_tapp(open_te_rec(K, U, e1), open_tt_rec(K, U, V))
}
function open_ee_rec(k : nat, f : exp, e : exp): exp
  ensures f.exp_fvar? ==> exp_size(e)==exp_size(open_ee_rec(k, f, e));
  decreases e;
{
  match e
  case exp_bvar(i) => if k == i then f else exp_bvar(i)
  case exp_fvar(x) => exp_fvar(x)
  case exp_abs(V, e1) => exp_abs(V, open_ee_rec(k+1, f, e1))
  case exp_app(e1, e2) => exp_app(open_ee_rec(k, f, e1),open_ee_rec(k, f, e2))
  case exp_tabs(e1) => exp_tabs(open_ee_rec(k, f, e1))
  case exp_tapp(e1, V) => exp_tapp(open_ee_rec(k, f, e1), V)
}

function open_tt(T: typ, U: typ): typ { open_tt_rec(0, U, T) }
function open_te(e: exp, U: typ): exp { open_te_rec(0, U, e) }
function open_ee(e1: exp, e2: exp): exp { open_ee_rec(0, e2, e1) }

predicate typ_lc(T: typ)
  decreases typ_size(T);
{
  match T
  case typ_top => true
  case typ_bvar(J) => false
  case typ_fvar(X) => true
  case typ_arrow(T1, T2) => typ_lc(T1) && typ_lc(T2)
  case typ_all(T1) => exists L:set<int> :: forall X :: X !in L ==> typ_lc(open_tt(T1, typ_fvar(X)))
}
predicate exp_lc(e: exp)
  decreases exp_size(e);
{
  match e
  case exp_bvar(i) => false
  case exp_fvar(x) => true
  case exp_abs(V, e1) => typ_lc(V) && (exists L:set<int> :: forall x :: x !in L ==> exp_lc(open_ee(e1, exp_fvar(x))))
  case exp_app(e1, e2) => exp_lc(e1) && exp_lc(e2)
  case exp_tabs(e1) => exists L:set<int> :: forall X :: X !in L ==> exp_lc(open_te(e1, typ_fvar(X)))
  case exp_tapp(e1, V) => exp_lc(e1) && typ_lc(V)
}
predicate body_lc(e: exp)
{
  exists L:set<int> :: forall x :: x !in L ==> exp_lc(open_ee(e, exp_fvar(x)))
}

datatype binding =
    bd_typ(x: int, ty: typ)
  | bd_var(X: int)
datatype env = Env(bds: seq<binding>)
function env_plus_var(X: int, E: env): env
{
  Env([bd_var(X)]+E.bds)
}
predicate env_has_var(X: int, E: env)
{
  bd_var(X) in E.bds
}
function env_extend(x: int, T: typ, E: env): env
{
  Env([bd_typ(x, T)]+E.bds)
}
function env_lookup(x: int, E: env): option<typ>
{
  bds_lookup(x, E.bds)
}
function bds_lookup(x: int, bds: seq<binding>): option<typ>
{
  if |bds|==0 then None else chain(bd_lookup(x, bds[0]), bds_lookup(x, bds[1..]))
}
function bd_lookup(y: int, bd: binding): option<typ>
{
  match bd
  case bd_typ(x, T) => if x==y then Some(T) else None
  case bd_var(X) => None
}
function env_concat(E1: env, E2: env): env
{
  Env(E1.bds+E2.bds)
}
function env_concat3(E1: env, E2: env, E3: env): env
{
  Env(E1.bds+E2.bds+E3.bds)
}
ghost method env_plus_concat(X: int, E1: env, E2: env)
  ensures env_concat(env_plus_var(X, E1), E2)==env_plus_var(X, env_concat(E1, E2));
{
  assert env_concat(env_plus_var(X, E1), E2)==Env([bd_var(X)]+E1.bds+E2.bds);
  assert env_plus_var(X, env_concat(E1, E2))==Env([bd_var(X)]+Env(E1.bds+E2.bds).bds);
  assert Env(E1.bds+E2.bds).bds == E1.bds+E2.bds;
  assert [bd_var(X)]+(E1.bds+E2.bds)==[bd_var(X)]+E1.bds+E2.bds;
}
ghost method env_plus_concat3(X: int, E1: env, E2: env, E3: env)
  ensures env_concat3(env_plus_var(X, E1), E2, E3)==env_plus_var(X, env_concat3(E1, E2, E3));
{
  assert env_concat3(env_plus_var(X, E1), E2, E3)==Env([bd_var(X)]+E1.bds+E2.bds+E3.bds);
  assert env_plus_var(X, env_concat3(E1, E2, E3))==Env([bd_var(X)]+Env(E1.bds+E2.bds+E3.bds).bds);
  assert Env(E1.bds+E2.bds+E3.bds).bds == E1.bds+E2.bds+E3.bds;
  assert [bd_var(X)]+(E1.bds+E2.bds+E3.bds)==[bd_var(X)]+E1.bds+E2.bds+E3.bds;
}
ghost method env_concat_empty(E: env)
  ensures env_concat(Env([]), E)==E;
{
  assert env_concat(Env([]), E)==Env(Env([]).bds+E.bds);
  assert Env([]).bds==[];
  assert []+E.bds==E.bds;
}
ghost method env_concat3_empty(E1: env, E2: env)
  ensures env_concat3(Env([]), E1, E2)==env_concat(E1, E2);
{
  assert env_concat3(Env([]), E1, E2)==Env(Env([]).bds+E1.bds+E2.bds);
  assert Env([]).bds==[];
  assert []+E1.bds+E2.bds==E1.bds+E2.bds;
}
ghost method env_plus_uniq(X: int, E: env)
  requires X !in env_dom(E);
  requires env_uniq(E);
  ensures env_uniq(env_plus_var(X, E));
{
}

predicate typ_wf(E: env, T: typ)
  decreases typ_size(T);
{
  match T
  case typ_top => true
  case typ_bvar(J) => false
  case typ_fvar(X) => env_has_var(X, E)
  case typ_arrow(T1, T2) => typ_wf(E, T1) && typ_wf(E, T2)
  case typ_all(T1) => exists L:set<int> :: forall X :: X !in L ==> typ_wf(env_plus_var(X, E), open_tt(T1, typ_fvar(X)))
}

function bd_dom(bd: binding): set<int>
{
  match bd
  case bd_typ(x, T) => {x}
  case bd_var(X) => {X}
}
function bds_dom(bds: seq<binding>): set<int>
{
  if |bds|==0 then {} else bd_dom(bds[0])+bds_dom(bds[1..])
}
function env_dom(E: env): set<int>
{
  bds_dom(E.bds)
}
ghost method bds_concat_dom(bds1: seq<binding>, bds2: seq<binding>)
  ensures bds_dom(bds1+bds2)==bds_dom(bds1)+bds_dom(bds2);
{
  if (|bds1|==0) {
    assert bds_dom(bds1)=={};
    assert bds1+bds2==bds2;
  } else {
    bds_concat_dom(bds1[1..], bds2);
    assert bds_dom(bds1[1..]+bds2)==bds_dom(bds1[1..])+bds_dom(bds2);
    assert [bds1[0]]+bds1[1..]==bds1;
    assert bd_dom(bds1[0])+bds_dom(bds1[1..])==bds_dom(bds1);
    assert bds1[1..]+bds2 == (bds1+bds2)[1..];
  }  
}
ghost method env_concat_dom(E1: env, E2: env)
  ensures env_dom(env_concat(E1, E2))==env_dom(E1)+env_dom(E2);
{
  bds_concat_dom(E1.bds, E2.bds);
}
ghost method bds_concat3_dom(bds1: seq<binding>, bds2: seq<binding>, bds3: seq<binding>)
  ensures bds_dom(bds1+bds2+bds3)==bds_dom(bds1)+bds_dom(bds2)+bds_dom(bds3);
{
  assert bds1+bds2+bds3==bds1+(bds2+bds3);
  bds_concat_dom(bds1, bds2+bds3);
  bds_concat_dom(bds2, bds3);
}
ghost method env_concat3_dom(E1: env, E2: env, E3: env)
  ensures env_dom(env_concat3(E1, E2, E3))==env_dom(E1)+env_dom(E2)+env_dom(E3);
{
  bds_concat3_dom(E1.bds, E2.bds, E3.bds);
}
predicate bds_wf(bds: seq<binding>)
  decreases bds, 0;
{
  |bds|==0 || (
    var bds' := bds[1..];
     bds_wf(bds') && bd_wf(bds[0], bds')
  )
}
predicate bd_wf(bd: binding, bds: seq<binding>)
  requires bds_wf(bds);
  decreases bds, 1;
{
  match bd
  case bd_typ(x, T) => typ_wf(Env(bds), T) && x !in bds_dom(bds)
  case bd_var(X) => X !in bds_dom(bds)
}
predicate env_wf(E: env)
{
  bds_wf(E.bds)
}
predicate bds_uniq(bds: seq<binding>)
  decreases bds;
{
  |bds|==0 || (
    var bds' := bds[1..];
     bds_uniq(bds') && bd_uniq(bds[0], bds_dom(bds'))
  )
}
predicate bd_uniq(bd: binding, dom_bds: set<int>)
{
  match bd
  case bd_typ(x, T) => x !in dom_bds
  case bd_var(X) => X !in dom_bds
}
predicate env_uniq(E: env)
{
  bds_uniq(E.bds)
}

function typing(E: env, e: exp): option<typ>
  decreases exp_size(e);
{
  match e
  case exp_bvar(i) => None
  case exp_fvar(x) => if (env_wf(E)) then env_lookup(x, E) else None
  case exp_abs(V, e1) => if (exists L:set<int>, T1 :: forall x :: x !in L ==> typing(env_extend(x, V, E), open_ee(e1, exp_fvar(x))) == Some(T1)) then
    var L:set<int>, T1 :| forall x :: x !in L ==> typing(env_extend(x, V, E), open_ee(e1, exp_fvar(x))) == Some(T1);
    Some(typ_arrow(V, T1))
    else None
  case exp_app(e1, e2) => if (typing(E, e1).Some? && typing(E, e2).Some? && typing(E, e1).get.typ_arrow? && typing(E, e2).get==typing(E, e1).get.ty1) then
    Some(typing(E, e1).get.ty2)
    else None
  case exp_tabs(e1) => if (exists L:set<int>, T1 :: forall X :: X !in L ==> typing(env_plus_var(X, E), open_te(e1, typ_fvar(X)))==Some(open_tt(T1, typ_fvar(X)))) then
    var L:set<int>, T1 :| forall X :: X !in L ==> typing(env_plus_var(X, E), open_te(e1, typ_fvar(X)))==Some(open_tt(T1, typ_fvar(X)));
    Some(typ_all(T1))
    else None
  case exp_tapp(e1, T) => if (typing(E, e1).Some? && typing(E, e1).get.typ_all?) then
    Some(open_tt(typing(E, e1).get.ty0, T))
    else None
}

predicate value(e: exp)
{
  match e
  case exp_abs(V, e1) => exp_lc(e)
  case exp_tabs(e1) => exp_lc(e)
  case exp_bvar(i) => false
  case exp_fvar(x) => false
  case exp_app(e1, e2) => false
  case exp_tapp(e1, V) => false
}

function red(e: exp): option<exp>
{
  // red_app_1
  if (e.exp_app? && exp_lc(e.arg) && red(e.f).Some?) then
    Some(exp_app(red(e.f).get, e.arg))
  // red_app_2
  else if (e.exp_app? && value(e.f) && red(e.arg).Some?) then
    Some(exp_app(e.f, red(e.arg).get))
  // red_tapp
  else if (e.exp_tapp? && typ_lc(e.targ) && red(e.tf).Some?) then
    Some(exp_tapp(red(e.tf).get, e.targ))
  // red_abs
  else if (e.exp_app? && value(e.f) && value(e.arg) && e.f.exp_abs?) then
    Some(open_ee(e.f.e0, e.arg))
  // red_tabs
  else if (e.exp_tapp? && value(e.tf) && typ_lc(e.targ) && e.tf.exp_tabs?) then
    Some(open_te(e.tf.te0, e.targ))
  else None
}

/// Infrastructure
/// https://github.com/plclub/metalib/blob/master/Fsub_LetSum_Infrastructure.v

function fv_tt(T: typ): set<int>
{
  match T
  case typ_top => {}
  case typ_bvar(J) => {}
  case typ_fvar(X) => {X}
  case typ_arrow(T1, T2) => fv_tt(T1) + fv_tt(T2)
  case typ_all(T1) => fv_tt(T1)
}

function fv_te(e: exp): set<int>
{
  match e
  case exp_bvar(i) => {}
  case exp_fvar(x) => {}
  case exp_abs(V, e1)  => fv_tt(V) + fv_te(e1)
  case exp_app(e1, e2) => fv_te(e1) + fv_te(e2)
  case exp_tabs(e1) => fv_te(e1)
  case exp_tapp(e1, V) => fv_tt(V) + fv_te(e1)
}

function fv_ee(e: exp): set<int>
{
  match e
  case exp_bvar(i) => {}
  case exp_fvar(x) => {x}
  case exp_abs(V, e1) => fv_ee(e1)
  case exp_app(e1, e2) => fv_ee(e1) + fv_ee(e2)
  case exp_tabs(e1) => fv_ee(e1)
  case exp_tapp(e1, V) => fv_ee(e1)
}

function subst_tt (Z: int, U: typ, T : typ): typ
  decreases T;
{
  match T
  case typ_top => typ_top
  case typ_bvar(J) => typ_bvar(J)
  case typ_fvar(X) => if X == Z then U else T
  case typ_arrow(T1, T2) => typ_arrow(subst_tt(Z, U, T1), subst_tt(Z, U, T2))
  case typ_all(T1) => typ_all(subst_tt(Z, U, T1))
}
function subst_te(Z: int, U: typ, e : exp): exp
  decreases e;
{
  match e
  case exp_bvar(i) => exp_bvar(i)
  case exp_fvar(x) => exp_fvar(x)
  case exp_abs(V, e1) => exp_abs(subst_tt(Z, U, V),subst_te(Z, U, e1))
  case exp_app(e1, e2) => exp_app(subst_te(Z, U, e1), subst_te(Z, U, e2))
  case exp_tabs(e1) => exp_tabs(subst_te(Z, U, e1))
  case exp_tapp(e1, V) => exp_tapp(subst_te(Z, U, e1), subst_tt(Z, U, V))
}
function subst_ee(z: int, u: exp, e: exp): exp
  decreases e;
{
  match e
  case exp_bvar(i) => exp_bvar(i)
  case exp_fvar(x) => if x == z then u else e
  case exp_abs(V, e1) => exp_abs(V, subst_ee(z, u, e1))
  case exp_app(e1, e2) => exp_app(subst_ee(z, u, e1), subst_ee(z, u, e2))
  case exp_tabs(e1) => exp_tabs(subst_ee(z, u, e1))
  case exp_tapp(e1, V) => exp_tapp(subst_ee(z, u, e1), V)
}

ghost method {:induction T, j, i} lemma_open_tt_rec_type_aux(T: typ, j: nat, V: typ, i: nat, U: typ)
  requires i != j;
  requires open_tt_rec(j, V, T) == open_tt_rec(i, U, open_tt_rec(j, V, T));
  ensures T == open_tt_rec(i, U, T);
{
}

ghost method lemma_open_tt_rec_type(T: typ, U: typ, k: nat)
  requires typ_lc(T);
  ensures T == open_tt_rec(k, U, T);
  decreases typ_size(T);
{
  if (T.typ_all?) {
    var L:set<int> :| forall X :: X !in L ==> typ_lc(open_tt(T.ty0, typ_fvar(X)));
    var X := notin(L);
    lemma_open_tt_rec_type(open_tt(T.ty0, typ_fvar(X)), U, k+1);
    lemma_open_tt_rec_type_aux(T.ty0, 0, typ_fvar(X), k+1, U);
  }
}

ghost method lemma_subst_tt_fresh(Z: int, U: typ, T: typ)
  requires Z !in fv_tt(T);
  ensures T == subst_tt(Z, U, T);
{
}

ghost method lemma_subst_tt_open_tt_rec(T1: typ, T2: typ, X: int, P: typ, k: nat)
  requires typ_lc(P);
  ensures subst_tt(X, P, open_tt_rec(k, T2, T1))
       == open_tt_rec(k, subst_tt(X, P, T2), subst_tt(X, P, T1));
{
  if (T1.typ_fvar? && T1.a==X) {
    lemma_open_tt_rec_type(P, subst_tt(X, P, T2), k);
  }
}

ghost method lemma_subst_tt_open_tt(T1: typ, T2: typ, X: int, P: typ)
  requires typ_lc(P);
  ensures subst_tt(X, P, open_tt(T1, T2)) == open_tt(subst_tt(X, P, T1), subst_tt(X, P, T2));
{
  lemma_subst_tt_open_tt_rec(T1, T2, X, P, 0);
}

ghost method lemma_subst_tt_open_tt_var(X: int, Y: int, P: typ, T: typ)
  requires Y != X;
  requires typ_lc(P);
  ensures open_tt(subst_tt(X, P, T), typ_fvar(Y)) == subst_tt(X, P, open_tt(T, typ_fvar(Y)));
{
  lemma_subst_tt_open_tt(T, typ_fvar(Y), X, P);
}

ghost method lemma_subst_tt_intro_rec(X: int, T2: typ, U: typ, k: nat)
  requires X !in fv_tt(T2);
  ensures open_tt_rec(k, U, T2) == subst_tt(X, U, open_tt_rec(k, typ_fvar(X), T2));
{
}

ghost method lemma_subst_tt_intro(X: int, T2: typ, U: typ)
  requires X !in fv_tt(T2);
  ensures open_tt(T2, U) == subst_tt(X, U, open_tt(T2, typ_fvar(X)));
{
  lemma_subst_tt_intro_rec(X, T2, U, 0);
}

ghost method {:induction e, j, i} lemma_open_te_rec_expr_aux(e: exp, j: nat, u: exp, i: nat, P: typ)
  requires open_ee_rec(j, u, e) == open_te_rec(i, P, open_ee_rec(j, u, e));
  ensures e == open_te_rec(i, P, e);
{
}

ghost method {:induction e, j, i} lemma_open_te_rec_type_aux(e: exp, j: nat, Q: typ, i: nat, P: typ)
  requires i != j;
  requires open_te_rec(j, Q, e) == open_te_rec(i, P, open_te_rec(j, Q, e));
  ensures e == open_te_rec(i, P, e);
{
  forall (V | i !=j && open_tt_rec(j, Q, V) == open_tt_rec(i, P, open_tt_rec(j, Q, V)))
  ensures V == open_tt_rec(i, P, V);
  {
    lemma_open_tt_rec_type_aux(V, j, Q, i, P);
  }
}

ghost method lemma_open_te_rec_expr(e: exp, U: typ, k: nat)
  requires exp_lc(e);
  ensures e == open_te_rec(k, U, e);
  decreases exp_size(e);
{
  forall (V | typ_lc(V))
  ensures V == open_tt_rec(k, U, V);
  {
    lemma_open_tt_rec_type(V, U, k);
  }
  if (e.exp_abs?) {
    var L:set<int> :| forall x :: x !in L ==> exp_lc(open_ee(e.e0, exp_fvar(x)));
    var x := notin(L);
    lemma_open_te_rec_expr(open_ee(e.e0, exp_fvar(x)), U, k);
    lemma_open_te_rec_expr_aux(e.e0, 0, exp_fvar(x), k, U);
  } else if (e.exp_tabs?) {
    var L:set<int> :| forall X :: X !in L ==> exp_lc(open_te(e.te0, typ_fvar(X)));
    var X := notin(L);
    lemma_open_te_rec_type_aux(e.te0, 0, typ_fvar(X), k+1, U);
  }
}

ghost method lemma_subst_te_fresh(X: int, U: typ, e: exp)
  requires X !in fv_te(e);
  ensures e == subst_te(X, U, e);
{
  forall (T | X !in fv_tt(T))
  ensures T == subst_tt(X, U, T);
  {
    lemma_subst_tt_fresh(X, U, T);
  }
}

ghost method lemma_subst_te_open_te_rec(e: exp, T: typ, X: int, U: typ, k: nat)
  requires typ_lc(U);
  ensures subst_te(X, U, open_te_rec(k, T, e))
       == open_te_rec(k, subst_tt(X, U, T), subst_te(X, U, e));
{
  forall (V | V<e)
  ensures subst_tt(X, U, open_tt_rec(k, T, V))
       == open_tt_rec(k, subst_tt(X, U, T), subst_tt(X, U, V));
  {
    lemma_subst_tt_open_tt_rec(V, T, X, U, k);
  }
}

ghost method lemma_subst_te_open_te(e: exp, T: typ, X: int, U: typ)
  requires typ_lc(U);
  ensures subst_te(X, U, open_te(e, T)) == open_te(subst_te(X, U, e), subst_tt(X, U, T));
{
  lemma_subst_te_open_te_rec(e, T, X, U, 0);
}

ghost method lemma_subst_te_open_te_var(X: int, Y: int, U: typ, e: exp)
  requires Y != X;
  requires typ_lc(U);
  ensures open_te(subst_te(X, U, e), typ_fvar(Y)) == subst_te(X, U, open_te(e, typ_fvar(Y)));
{
  lemma_subst_te_open_te(e, typ_fvar(Y), X, U);
}

ghost method lemma_subst_te_intro_rec(X: int, e: exp, U: typ, k: nat)
  requires X !in fv_te(e);
  ensures open_te_rec(k, U, e) == subst_te(X, U, open_te_rec(k, typ_fvar(X), e));
{
  forall (V | V<e && X !in fv_tt(V))
  ensures open_tt_rec(k, U, V) == subst_tt(X, U, open_tt_rec(k, typ_fvar(X), V));
  {
    lemma_subst_tt_intro_rec(X, V, U, k);
  }
}

ghost method lemma_subst_te_intro(X: int, e: exp, U: typ)
  requires X !in fv_te(e);
  ensures open_te(e, U) == subst_te(X, U, open_te(e, typ_fvar(X)));
{
  lemma_subst_te_intro_rec(X, e, U, 0);
}

ghost method {:induction e, j, i} lemma_open_ee_rec_expr_aux(e: exp, j: nat, v: exp, u: exp, i: nat)
  requires i != j;
  requires open_ee_rec(j, v, e) == open_ee_rec(i, u, open_ee_rec(j, v, e));
  ensures e == open_ee_rec(i, u, e);
{
}

ghost method {:induction e, j, i} lemma_open_ee_rec_type_aux(e: exp, j: nat, V: typ, u: exp, i: nat)
  requires open_te_rec(j, V, e) == open_ee_rec(i, u, open_te_rec(j, V, e));
  ensures e == open_ee_rec(i, u, e);
{
}

ghost method lemma_open_ee_rec_expr(u: exp, e: exp, k: nat)
  requires exp_lc(e);
  ensures e == open_ee_rec(k, u, e);
  decreases exp_size(e);
{
  if (e.exp_abs?) {
    var L:set<int> :| forall x :: x !in L ==> exp_lc(open_ee(e.e0, exp_fvar(x)));
    var x := notin(L);
    lemma_open_ee_rec_expr(u, open_ee(e.e0, exp_fvar(x)), k);
    lemma_open_ee_rec_expr_aux(e.e0, 0, exp_fvar(x), u, k+1);
  } else if (e.exp_tabs?) {
    var L:set<int> :| forall X :: X !in L ==> exp_lc(open_te(e.te0, typ_fvar(X)));
    var X := notin(L);
    lemma_open_ee_rec_type_aux(e.te0, 0, typ_fvar(X), u, k);
  }
}

ghost method lemma_subst_ee_fresh(x: int, u: exp, e: exp)
  requires x !in fv_ee(e);
  ensures e == subst_ee(x, u, e);
{
}

ghost method lemma_subst_ee_open_ee_rec(e1: exp, e2: exp, x: int, u: exp, k: nat)
  requires exp_lc(u);
  ensures subst_ee(x, u, open_ee_rec(k, e2, e1))
       == open_ee_rec(k, subst_ee(x, u, e2), subst_ee(x, u, e1));
{
  if (e1.exp_fvar? && e1.a==x) {
    lemma_open_ee_rec_expr(subst_ee(x, u, e2), u, k);
  }
}

ghost method lemma_subst_ee_open_ee(e1: exp, e2: exp, x: int, u: exp)
  requires exp_lc(u);
  ensures subst_ee(x, u, open_ee(e1, e2))
       == open_ee(subst_ee(x, u, e1), subst_ee(x, u, e2));
{
  lemma_subst_ee_open_ee_rec(e1, e2, x, u, 0);
}

ghost method lemma_subst_ee_open_ee_var(x: int, y: int, u: exp, e: exp)
  requires y != x;
  requires exp_lc(u);
  ensures open_ee(subst_ee(x, u, e), exp_fvar(y)) == subst_ee(x, u, open_ee(e, exp_fvar(y)));
{
  lemma_subst_ee_open_ee(e, exp_fvar(y), x, u);
}

ghost method lemma_subst_te_open_ee_rec(e1: exp, e2: exp, Z: int, P: typ, k: nat)
  ensures subst_te(Z, P, open_ee_rec(k, e2, e1))
       == open_ee_rec(k, subst_te(Z, P, e2), subst_te(Z, P, e1));
{
}

ghost method lemma_subst_te_open_ee(e1: exp, e2: exp, Z: int, P: typ)
  ensures subst_te(Z, P, open_ee(e1, e2)) == open_ee(subst_te(Z, P, e1), subst_te(Z, P, e2));
{
  lemma_subst_te_open_ee_rec(e1, e2, Z, P, 0);
}

ghost method lemma_subst_te_open_ee_var(Z: int, x: int, P: typ, e: exp)
  ensures open_ee(subst_te(Z, P, e), exp_fvar(x)) == subst_te(Z, P, open_ee(e, exp_fvar(x)));
{
  lemma_subst_te_open_ee(e, exp_fvar(x), Z, P);
}

ghost method lemma_subst_ee_open_te_rec(e: exp, P: typ, z: int, u: exp, k: nat)
  requires exp_lc(u);
  ensures subst_ee(z, u, open_te_rec(k, P, e)) == open_te_rec(k, P, subst_ee(z, u, e));
{
  if (e.exp_fvar? && e.a==z) {
    lemma_open_te_rec_expr(u, P, k);
  }
}

ghost method lemma_subst_ee_open_te(e: exp, P: typ, z: int, u: exp)
  requires exp_lc(u);
  ensures subst_ee(z, u ,open_te(e, P)) == open_te(subst_ee(z, u, e), P);
{
  lemma_subst_ee_open_te_rec(e, P, z, u, 0);
}

ghost method lemma_subst_ee_open_te_var(z: int, X: int, u: exp, e: exp)
  requires exp_lc(u);
  ensures open_te(subst_ee(z, u, e), typ_fvar(X)) == subst_ee(z, u, open_te(e, typ_fvar(X)));
{
  lemma_subst_ee_open_te(e, typ_fvar(X), z, u);
}

ghost method lemma_subst_ee_intro_rec(x: int, e: exp, u: exp, k: nat)
  requires x !in fv_ee(e);
  ensures open_ee_rec(k, u, e) == subst_ee(x, u, open_ee_rec(k, exp_fvar(x), e));
{
}

ghost method lemma_subst_ee_intro(x: int, e: exp, u: exp)
  requires x !in fv_ee(e);
  ensures open_ee(e, u) == subst_ee(x, u, open_ee(e, exp_fvar(x)));
{
  lemma_subst_ee_intro_rec(x, e, u, 0);
}

ghost method lemma_subst_tt_type(Z: int, P: typ, T: typ)
  requires typ_lc(T);
  requires typ_lc(P);
  ensures typ_lc(subst_tt(Z, P, T));
  decreases typ_size(T);
{
  if (T.typ_all?) {
    var L:set<int> :| forall X :: X !in L ==> typ_lc(open_tt(T.ty0, typ_fvar(X)));
    var L' := L+{Z};
    forall (X | X !in L')
    ensures typ_lc(open_tt(subst_tt(Z, P, T.ty0), typ_fvar(X)));
    {
      lemma_subst_tt_type(Z, P, open_tt(T.ty0, typ_fvar(X)));
      lemma_subst_tt_open_tt_var(Z, X, P, T.ty0);
    }
  }
}

ghost method lemma_subst_te_expr(Z: int, P: typ, e: exp)
  requires exp_lc(e);
  requires typ_lc(P);
  ensures exp_lc(subst_te(Z, P, e));
  decreases exp_size(e);
{
  forall (V | V<e && typ_lc(V))
  ensures typ_lc(subst_tt(Z, P, V));
  {
    lemma_subst_tt_type(Z, P, V);
  }
  if (e.exp_abs?) {
    var L:set<int> :| forall x :: x !in L ==> exp_lc(open_ee(e.e0, exp_fvar(x)));
    forall (x | x !in L)
    ensures exp_lc(open_ee(subst_te(Z, P, e.e0), exp_fvar(x)));
    {
      lemma_subst_te_expr(Z, P, open_ee(e.e0, exp_fvar(x)));
      lemma_subst_te_open_ee_var(Z, x, P, e.e0);
    }
  } else if (e.exp_tabs?) {
    var L:set<int> :| forall X :: X !in L ==> exp_lc(open_te(e.te0, typ_fvar(X)));
    var L' := L+{Z};
    forall (X | X !in L')
    ensures exp_lc(open_te(subst_te(Z, P, e.te0), typ_fvar(X)));
    {
      lemma_subst_te_expr(Z, P, open_te(e.te0, typ_fvar(X)));
      lemma_subst_te_open_te_var(Z, X, P, e.te0);
    }
  }
}

ghost method lemma_subst_ee_expr(z: int, e1: exp, e2: exp)
  requires exp_lc(e1);
  requires exp_lc(e2);
  ensures exp_lc(subst_ee(z, e2, e1));
  decreases exp_size(e1);
{
  if (e1.exp_abs?) {
    var L:set<int> :| forall x :: x !in L ==> exp_lc(open_ee(e1.e0, exp_fvar(x)));
    var L' := L+{z};
    forall (x | x !in L')
    ensures exp_lc(open_ee(subst_ee(z, e2, e1.e0), exp_fvar(x)));
    {
      lemma_subst_ee_expr(z, open_ee(e1.e0, exp_fvar(x)), e2);
      lemma_subst_ee_open_ee_var(z, x, e2, e1.e0);
    }
  } else if (e1.exp_tabs?) {
    var L:set<int> :| forall X :: X !in L ==> exp_lc(open_te(e1.te0, typ_fvar(X)));
    forall (X | X !in L)
    ensures exp_lc(open_te(subst_ee(z, e2, e1.te0), typ_fvar(X)));
    {
      lemma_subst_ee_expr(z, open_te(e1.te0, typ_fvar(X)), e2);
      lemma_subst_ee_open_te_var(z, X, e2, e1.te0);
    }
  }
}

ghost method lemma_open_ee_body_e(e1: exp, e2: exp)
  requires body_lc(e1);
  requires exp_lc(e2);
  ensures exp_lc(open_ee(e1, e2));
{
  var L:set<int> :| forall x :: x !in L ==> exp_lc(open_ee(e1, exp_fvar(x)));
  var L' := L+fv_ee(e1);
  var x := notin(L');
  lemma_subst_ee_intro(x, e1, e2);
  lemma_subst_ee_expr(x, open_ee(e1, exp_fvar(x)), e2);
}

ghost method auto_infrastructure()
  ensures  forall Z, P, T :: (typ_lc(T) && typ_lc(P)) ==> typ_lc(subst_tt(Z, P, T));
{
  forall (Z, P, T | typ_lc(T) && typ_lc(P))
  ensures typ_lc(subst_tt(Z, P, T));
  {
    lemma_subst_tt_type(Z, P, T);
  }
}

/// Lemmas
/// https://github.com/plclub/metalib/blob/master/Fsub_LetSum_Lemmas.v

ghost method {:induction E, T} lemma_typ_lc_from_wf(E: env, T: typ)
  requires typ_wf(E, T);
  ensures typ_lc(T);
  decreases typ_size(T);
{
}

ghost method lemma_wf_typ_weakening(T: typ, E: env, F: env, G: env)
  requires typ_wf(env_concat(G, E), T);
  requires env_uniq(env_concat3(G, F, E));
  ensures typ_wf(env_concat3(G, F, E), T);
  decreases typ_size(T);
{
  if (T.typ_all?) {
    var L:set<int> :| forall X :: X !in L ==> typ_wf(env_plus_var(X, env_concat(G, E)), open_tt(T.ty0, typ_fvar(X)));
    var L' := L+env_dom(G)+env_dom(F)+env_dom(E);
    forall (X | X !in L')
    ensures typ_wf(env_plus_var(X, env_concat3(G, F, E)), open_tt(T.ty0, typ_fvar(X)));
    {
      env_plus_concat(X, G, E);
      env_plus_concat3(X, G, F, E);
      env_concat3_dom(G, F, E);
      env_plus_uniq(X, env_concat3(G, F, E));
      lemma_wf_typ_weakening(open_tt(T.ty0, typ_fvar(X)), E, F, env_plus_var(X, G));
    }
  }
}

ghost method lemma_wf_typ_weaken_head(T: typ, E: env, F: env)
  requires typ_wf(E, T);
  requires env_uniq(env_concat(F, E));
  ensures typ_wf(env_concat(F, E), T);
{
  env_concat3_empty(F, E);
  env_concat_empty(E);
  lemma_wf_typ_weakening(T, E, F, Env([]));
}

ghost method lemma_wf_typ_strengthening(E: env, F: env, x: int, U: typ, T: typ)
  requires typ_wf(env_concat3(F, Env([bd_typ(x, U)]), E), T);
  ensures typ_wf(env_concat(F, E), T);
  decreases typ_size(T);
{
  if (T.typ_all?) {
    var L:set<int> :| forall X :: X !in L ==> typ_wf(env_plus_var(X, env_concat3(F, Env([bd_typ(x, U)]), E)), open_tt(T.ty0, typ_fvar(X)));
    var L' := L;
    forall (X | X !in L')
    ensures typ_wf(env_plus_var(X, env_concat(F, E)), open_tt(T.ty0, typ_fvar(X)));
    {
      env_plus_concat3(X, F, Env([bd_typ(x, U)]), E);
      env_plus_concat(X, F, E);
      lemma_wf_typ_strengthening(E, env_plus_var(X, F), x, U, open_tt(T.ty0, typ_fvar(X)));
    }
  }
}

function subst_bd(Z: int, P: typ, bd: binding): binding
  ensures bd.bd_var? ==> subst_bd(Z, P, bd)==bd;
  ensures bd_dom(bd)==bd_dom(subst_bd(Z, P, bd));
{
  match bd
  case bd_var(X) => bd_var(X)
  case bd_typ(x, T) => bd_typ(x, subst_tt(Z, P, T))
}
function subst_bds(Z: int, P: typ, bds: seq<binding>): seq<binding>
  ensures forall X :: bd_var(X) in bds ==> bd_var(X) in subst_bds(Z, P, bds);
  ensures bds_dom(bds)==bds_dom(subst_bds(Z, P, bds));
{
  if (|bds|==0) then [] else
  [subst_bd(Z, P, bds[0])]+subst_bds(Z, P, bds[1..])
}
function subst_env(Z: int, P: typ, E: env): env
  ensures forall X :: env_has_var(X, E) ==> env_has_var(X, subst_env(Z, P, E));
  ensures env_dom(E)==env_dom(subst_env(Z, P, E));
{
  Env(subst_bds(Z, P, E.bds))
}
ghost method bds_uniq_subst(Z: int, P: typ, bds: seq<binding>)
  requires bds_uniq(bds);
  ensures bds_uniq(subst_bds(Z, P, bds));
{
}
ghost method env_uniq_subst(Z: int, P: typ, E: env)
  requires env_uniq(E);
  ensures env_uniq(subst_env(Z, P, E));
{
  bds_uniq_subst(Z, P, E.bds);
}
ghost method bds_subst_uniq(Z: int, P: typ, bds: seq<binding>)
  requires bds_uniq(subst_bds(Z, P, bds));
  ensures bds_uniq(bds);
{
  var sbds := subst_bds(Z, P, bds);
  if (|sbds|==0) {
  } else {
    var sbds' := sbds[1..];
    var bds' := bds[1..];
    bds_subst_uniq(Z, P, bds');
    assert bds_dom(sbds')==bds_dom(bds');
  }
}
ghost method env_subst_uniq(Z: int, P: typ, E: env)
  requires env_uniq(subst_env(Z, P, E));
  ensures env_uniq(E);
{
  bds_subst_uniq(Z, P, E.bds);
}

ghost method lemma_wf_typ_subst_tb(F: env, E: env, Z: int, P: typ, T: typ)
  requires typ_wf(env_concat3(F, Env([bd_var(Z)]), E), T);
  requires typ_wf(E, P);
  requires env_uniq(env_concat(subst_env(Z, P, F), E));
  ensures typ_wf(env_concat(subst_env(Z, P, F), E), subst_tt(Z, P, T));
  decreases typ_size(T);
{
  if (T.typ_fvar?) {
    if (T.a == Z) {
      assert subst_tt(Z, P, T)==P;
      lemma_wf_typ_weaken_head(P, E, subst_env(Z, P, F));
    }
  } else if (T.typ_all?) {
    var L:set<int> :| forall X :: X !in L ==> typ_wf(env_plus_var(X, env_concat3(F, Env([bd_var(Z)]), E)), open_tt(T.ty0, typ_fvar(X)));
    var L' := L+env_dom(E)+env_dom(F)+{Z};
    forall (X | X !in L')
    ensures typ_wf(env_plus_var(X, env_concat(subst_env(Z, P, F), E)), open_tt(subst_tt(Z, P, T.ty0), typ_fvar(X)));
    {
      env_plus_concat3(X, F, Env([bd_var(Z)]), E);
      env_plus_concat(X, subst_env(Z, P, F), E);
      env_concat_dom(subst_env(Z, P, F), E);
      env_plus_uniq(X, env_concat(subst_env(Z, P, F), E));
      lemma_wf_typ_subst_tb(env_plus_var(X, F), E, Z, P, open_tt(T.ty0, typ_fvar(X)));
      lemma_typ_lc_from_wf(E, P);
      lemma_subst_tt_open_tt_var(Z, X, P, T.ty0);
    }
  }
}

ghost method lemma_wf_typ_open(E: env, U: typ, T0: typ)
  requires env_uniq(E);
  requires typ_wf(E, typ_all(T0));
  requires typ_wf(E, U);
  ensures typ_wf(E, open_tt(T0, U));
{
  var L:set<int> :| forall X :: X !in L ==> typ_wf(env_plus_var(X, E), open_tt(T0, typ_fvar(X)));
  var L' := L+fv_tt(T0);
  var X := notin(L');
  lemma_subst_tt_intro(X, T0, U);
  env_concat_empty(E);
  env_concat3_empty(Env([bd_var(X)]), E);
  lemma_wf_typ_subst_tb(Env([]), E, X, U, open_tt(T0, typ_fvar(X)));
}