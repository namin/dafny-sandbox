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
  case exp_tabs(e1) => if (exists L:seq<int>, T1 :: forall X :: X !in L ==> typing(env_plus_var(X, E), open_te(e1, typ_fvar(X)))==Some(open_tt(T1, typ_fvar(X)))) then
    var L:seq<int>, T1 :| forall X :: X !in L ==> typing(env_plus_var(X, E), open_te(e1, typ_fvar(X)))==Some(open_tt(T1, typ_fvar(X)));
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