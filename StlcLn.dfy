// The Simply Typed Lambda-Calculus
// Locally nameless representation with cofinite quantification
// http://www.cis.upenn.edu/~plclub/popl08-tutorial/code/index.html#stlc
// http://www.chargueraud.org/softs/ln/
// https://github.com/namin/coq-sandbox/blob/master/STLC.v

datatype atom = a(i: nat);
function max(s: seq<atom>, start: int): int
  ensures max(s, start)>=start;
  ensures forall x:nat :: a(x) in s ==> x<=max(s, start);
{
  if (s == []) then start
  else if (s[0].i <= start) then max(s[1..], start)
  else max(s[1..], s[0].i)
}
function fresh_from(ids: seq<atom>): atom
  ensures fresh_from(ids) !in ids;
  ensures fresh_from(ids).i>0;
{
  a(max(ids, 0)+1)
}

datatype typ = typ_base | typ_arrow(t1: typ, t2: typ);

datatype exp = bvar(n: nat) | fvar(x: atom) | abs(body: exp) | app(f: exp, arg: exp);

function subst(z: atom, u: exp, e: exp): exp
  decreases e;
{
  match e
  case bvar(i) => bvar(i)
  case fvar(x) => if x==z then u else fvar(x)
  case abs(e1) => abs(subst(z, u, e1))
  case app(e1, e2) => app(subst(z, u, e1), subst(z, u, e2))
}

ghost method example_subst1(Y: atom, Z: atom)
  requires Y!=Z;
  ensures subst(Y, fvar(Z), abs(app(bvar(0), fvar(Y)))) == abs(app(bvar(0), fvar(Z)));
{
  assert subst(Y, fvar(Z), app(bvar(0), fvar(Y))) == app(bvar(0), fvar(Z));
}

ghost method lemma_subst_eq_var(x: atom, u: exp)
  ensures subst(x, u, fvar(x)) == u;
{
}

ghost method lemma_subst_neq_var(x: atom, y: atom, u: exp)
  requires y != x;
  ensures subst(x, u, fvar(y)) == fvar(y);
{
}

function fv(e: exp) : seq<atom>
  decreases e;
{
  match e
  case bvar(i) => []
  case fvar(x) => [x]
  case abs(e1) => fv(e1)
  case app(e1, e2) => fv(e1) + fv(e2)
}

ghost method lemma_subst_fresh(x: atom, e: exp, u: exp)
  requires x !in fv(e);
  ensures subst(x, u, e) == e;
{
}

ghost method lemma_subst_notin_fv(x: atom, y: atom, u: exp, e: exp)
  requires x !in fv(e);
  requires x !in fv(u);
  ensures x !in fv(subst(y, u, e));
{
}

function size(e: exp): nat
  decreases e;
  ensures e.app? ==> size(e) > size(e.f);
  ensures e.app? ==> size(e) > size(e.arg);
  ensures e.abs? ==> size(e) > size(e.body);
{
  match e
  case bvar(i) => 1
  case fvar(x) => 1
  case abs(e1) => 1 + size(e1)
  case app(e1, e2) => 1 + size(e1) + size(e2)
}

function open_rec(k: nat, u: exp, e: exp): exp
  ensures u.fvar? ==> size(e) == size(open_rec(k, u, e));
  decreases e;
{
  match e
  case bvar(i) => if k==i then u else bvar(i)
  case fvar(x) => fvar(x)
  case abs(e1) => abs(open_rec(k+1, u, e1))
  case app(e1, e2) => app(open_rec(k, u, e1), open_rec(k, u, e2))
}

function open(e: exp, u: exp): exp
  ensures u.fvar? ==> size(e) == size(open(e, u));
{
  open_rec(0, u, e)
}

ghost method example_open(Y: atom)
  ensures open(app(abs(app(bvar(1), bvar(0))), bvar(0)), fvar(Y)) == app(abs(app(fvar(Y), bvar(0))), fvar(Y));
{
  calc == {
    open(app(abs(app(bvar(1), bvar(0))), bvar(0)), fvar(Y));
    open_rec(0, fvar(Y), app(abs(app(bvar(1), bvar(0))), bvar(0)));
    app(open_rec(0, fvar(Y), abs(app(bvar(1), bvar(0)))), open_rec(0, fvar(Y), bvar(0)));
    app(abs(open_rec(1, fvar(Y), app(bvar(1), bvar(0)))), open_rec(0, fvar(Y), bvar(0)));
    app(abs(app(fvar(Y), bvar(0))), fvar(Y));
  }
}

predicate lc(e: exp)
  ensures lc(e) ==> !e.bvar?;
  decreases size(e);
{
  e.fvar? ||
  (e.abs? && forall x :: x !in fv(e) ==> lc(open(e.body, fvar(x)))) ||
  (e.app? && lc(e.f) && lc(e.arg))
}

ghost method lemma_open_rec_lc_core(e: exp, j: nat, v: exp, i: nat, u: exp)
  requires i != j;
  requires open_rec(j, v, e) == open_rec(i, u, open_rec(j, v, e));
  ensures e == open_rec(i, u, e);
{
  if (e.abs?) {
    lemma_open_rec_lc_core(e.body, j+1, v, i+1, u);
  }
}

ghost method lemma_open_rec_lc(k: nat, u: exp, e: exp)
  requires lc(e);
  ensures e == open_rec(k, u, e);
  decreases size(e);
{
  if (e.abs?) {
    assert open_rec(k, u, e) == abs(open_rec(k+1, u, e.body));
    var x := fresh_from(fv(e));
    lemma_open_rec_lc(k+1, u, open(e.body, fvar(x)));
    lemma_open_rec_lc_core(e.body, 0, fvar(x), k+1, u);
  }
}

ghost method lemma_subst_open_rec(e1: exp, e2: exp, u: exp, x: atom, k: nat)
  requires lc(u);
  ensures subst(x, u, open_rec(k, e2, e1)) == open_rec(k, subst(x, u, e2), subst(x, u, e1));
{
  if (e1.fvar?) {
    if (e1.x==x) {
      lemma_open_rec_lc(k, subst(x, u, e2), u);
    }
  }
}

ghost method lemma_subst_open_var(x: atom, y: atom, u: exp, e: exp)
  requires y != x;
  requires lc(u);
  ensures open(subst(x, u, e), fvar(y)) == subst(x, u, open(e, fvar(y)));
{
  lemma_subst_open_rec(e, fvar(y), u, x, 0);
}

ghost method lemma_subst_intro_core(x: atom, u: exp, e: exp, k: nat)
  requires x !in fv(e);
  ensures open_rec(k, u, e) == subst(x, u, open_rec(k, fvar(x), e));
{
}

ghost method lemma_subst_intro(x: atom, u: exp, e: exp)
  requires x !in fv(e);
  ensures open(e, u) == subst(x, u, open(e, fvar(x)));
{
  if (e.abs?) {
    lemma_subst_intro_core(x, u, e.body, 1);
  } else if (e.app?) {
    lemma_subst_intro(x, u, e.f);
    lemma_subst_intro(x, u, e.arg);
  }
}

predicate lc_c(e: exp)
  decreases size(e);
{
  e.fvar? ||
  (e.abs? && exists L:seq<atom> :: forall x :: x !in L ==> lc_c(open(e.body, fvar(x)))) ||
  (e.app? && lc_c(e.f) && lc_c(e.arg))
}

ghost method lemma_open_rec_lc_c(k: nat, u: exp, e: exp)
  requires lc_c(e);
  ensures e == open_rec(k, u, e);
  decreases size(e);
{
  if (e.abs?) {
    assert open_rec(k, u, e) == abs(open_rec(k+1, u, e.body));
    var L:seq<atom> :| forall x :: x !in L ==> lc_c(open(e.body, fvar(x)));
    var x := fresh_from(L);
    lemma_open_rec_lc_c(k+1, u, open(e.body, fvar(x)));
    lemma_open_rec_lc_core(e.body, 0, fvar(x), k+1, u);
  }
}

ghost method lemma_subst_open_rec_c(e1: exp, e2: exp, u: exp, x: atom, k: nat)
  requires lc_c(u);
  ensures subst(x, u, open_rec(k, e2, e1)) == open_rec(k, subst(x, u, e2), subst(x, u, e1));
{
  if (e1.fvar?) {
    if (e1.x==x) {
      lemma_open_rec_lc_c(k, subst(x, u, e2), u);
    }
  }
}

ghost method lemma_subst_open_var_c(x: atom, y: atom, u: exp, e: exp)
  requires y != x;
  requires lc_c(u);
  ensures open(subst(x, u, e), fvar(y)) == subst(x, u, open(e, fvar(y)));
{
  lemma_subst_open_rec_c(e, fvar(y), u, x, 0);
}

ghost method lemma_subst_lc_c(x: atom, u: exp, e: exp)
  requires lc_c(e);
  requires lc_c(u);
  requires lc_c(subst(x, u, e));
{
}

datatype env = Env(vars: seq<atom>, typs: seq<typ>);
function empty_env(): env
  ensures empty_env()==Env([], []);
{
  Env([], [])
}

predicate wf_env(E: env)
{
  uniq(E.vars) && |E.vars| == |E.typs|
}

predicate uniq(vars: seq<atom>)
{
  forall i:nat, j: nat :: i<|vars| && j<|vars| ==> vars[i]==vars[j] ==> i==j
}

predicate binds(a: atom, t: typ, E: env)
{
  exists i:nat :: i<|E.vars| && i<|E.typs| && E.vars[i]==a && E.typs[i]==t
}

ghost method helper_binds_uniq(E: env, x: atom, s: typ, t: typ)
  requires wf_env(E);
  requires binds(x, t, E);
  requires binds(x, s, E);
  ensures t==s;
{
}

function extends(a: atom, t: typ, E: env): env
{
  Env([a]+E.vars, [t]+E.typs)
}

function concat(E1: env, E2: env): env
{
  Env(E1.vars+E2.vars, E1.typs+E2.typs)
}

function fresh_in_env(E: env): atom
{
  fresh_from(E.vars)
}

ghost method helper_binds_mid(E: env, F: env, x: atom, t: typ)
  requires wf_env(F);
  ensures binds(x, t, concat(F, extends(x, t, E)));
{
  var E' := concat(F, extends(x, t, E));
  var i := |F.vars|;
  assert i<|E'.vars| && i<|E'.typs| && E'.vars[i]==x && E'.typs[i]==t;
}

ghost method helper_binds_concat(E: env, F: env, G: env, a: atom, t: typ)
  requires wf_env(E);
  requires wf_env(F);
  requires wf_env(G);
  requires wf_env(concat(G, E));
  requires wf_env(concat(G, concat(F, E)));
  requires binds(a, t, concat(G, E));
  ensures binds(a, t, concat(G, concat(F, E)));
{
  var E' := concat(G, E);
  assert binds(a, t, E');
  assert exists i:nat :: i<|E'.vars| && i<|E'.typs| && E'.vars[i]==a && E'.typs[i]==t;
  var i:nat :| i<|E'.vars| && i<|E'.typs| && E'.vars[i]==a && E'.typs[i]==t;
  var E'' := concat(G, concat(F, E));
  if (i < |G.vars|) {
    assert i<|E''.vars| && i<|E''.typs| && E''.vars[i]==a && E''.typs[i]==t;
  } else {
    var j := i+|F.vars|;
    assert j<|E''.vars| && j<|E''.typs| && E''.vars[j]==a && E''.typs[j]==t;
  }
}

ghost method helper_wf_extends(a: atom, t: typ, E: env)
  requires a !in E.vars;
  requires wf_env(E);
  ensures wf_env(extends(a, t, E));
{
}

ghost method helper_wf_extends3(a: atom, t: typ, E: env, F: env, G: env)
  requires wf_env(E);
  requires wf_env(F);
  requires wf_env(G);
  requires wf_env(concat(G, E));
  requires wf_env(concat(G, concat(F, E)));
  ensures wf_env(extends(a, t, G));
  requires wf_env(concat(extends(a, t, G), E));
  requires wf_env(concat(extends(a, t, G), concat(F, E)));
{
}

ghost method helper_env_plus_assoc(a: atom, t: typ, E: env, G: env)
  ensures concat(extends(a, t, G), E) == extends(a, t, concat(G, E));
{
  calc == {
    concat(extends(a, t, G), E).vars;
    extends(a, t, G).vars+E.vars;
    [a]+G.vars+E.vars;
  }
  calc == {
    extends(a, t, concat(G, E)).vars;
    [a]+concat(G, E).vars;
    [a]+G.vars+E.vars;
  }
  calc == {
    concat(extends(a, t, G), E).typs;
    extends(a, t, G).typs+E.typs;
    [t]+G.typs+E.typs;
  }
  calc == {
    extends(a, t, concat(G, E)).typs;
    [t]+concat(G, E).typs;
    [t]+G.typs+E.typs;
  }
}

ghost method helper_nil_concat<A>(s: seq<A>)
  ensures []+s==s;
{
}

ghost method helper_env_nil_concat(E: env)
  ensures concat(empty_env(), E) == E;
{
  calc == {
    concat(empty_env(), E);
    concat(Env([], []), E);
    Env([]+E.vars, []+E.typs);
    { helper_nil_concat(E.vars); }
    Env(E.vars, []+E.typs);
    { helper_nil_concat(E.typs); }
    Env(E.vars, E.typs);
    E;
  }
}

predicate typing_c(E: env, e: exp, t: typ)
  decreases size(e);
{
  (e.fvar? && wf_env(E) && binds(e.x, t, E)) ||
  (e.abs? && t.typ_arrow? && exists L:seq<atom> :: forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2)) ||
  (e.app? && exists t1 :: typing_c(E, e.f, typ_arrow(t1, t)) && typing_c(E, e.arg, t1))
}

ghost method helper_abs_typing_c_L(E: env, e: exp, t: typ) returns (L:seq<atom>)
  requires e.abs?;
  requires typing_c(E, e, t);
  ensures t.typ_arrow?;
  ensures forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
{
  assert exists L:seq<atom> :: forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  var L_:seq<atom> :| forall x :: x !in L_ ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  L := L_;
}

ghost method helper_exists_abs_typing_c(L: seq<atom>, E: env, e: exp, t: typ)
  requires e.abs?;
  requires t.typ_arrow?;
  requires forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  ensures exists L:seq<atom> :: forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  ensures typing_c(E, e, t);
{
}

ghost method lemma_typing_weakening_strengthened(E: env, F: env, G: env, e: exp, t: typ)
  requires wf_env(E);
  requires wf_env(F);
  requires wf_env(G);
  requires wf_env(concat(G, E));
  requires wf_env(concat(G, concat(F, E)));
  requires typing_c(concat(G, E), e, t);
  ensures typing_c(concat(G, concat(F, E)), e, t);
  decreases size(e);
{
  var E' := concat(G, E);
  var E'' := concat(G, concat(F, E));
  if (e.fvar?) {
    assert binds(e.x, t, E');
    helper_binds_concat(E, F, G, e.x, t);
    assert binds(e.x, t, E'');
    assert typing_c(E'', e, t);
  } else if (e.abs?) {
    var L' := helper_abs_typing_c_L(E', e, t);
    var L'':seq<atom> := L'+E''.vars;
    forall (x | x !in L'')
    ensures typing_c(extends(x, t.t1, E''), open(e.body, fvar(x)), t.t2);
    {
      assert x !in L';
      assert typing_c(extends(x, t.t1, E'), open(e.body, fvar(x)), t.t2);
      helper_env_plus_assoc(x, t.t1, E, G);
      lemma_typing_weakening_strengthened(E, F, extends(x, t.t1, G), open(e.body, fvar(x)), t.t2);
      helper_env_plus_assoc(x, t.t1, concat(F, E), G);
    }
    assert forall x :: x !in L'' ==> typing_c(extends(x, t.t1, E''), open(e.body, fvar(x)), t.t2);
    helper_exists_abs_typing_c(L'', E'', e, t);
  } else {
  }
}

ghost method lemma_typing_c_weakening(E: env, F: env, e: exp, t: typ)
  requires wf_env(E);
  requires wf_env(F);
  requires wf_env(concat(F, E));
  requires typing_c(E, e, t);
  ensures typing_c(concat(F, E), e, t);
{
  helper_env_nil_concat(E);
  lemma_typing_weakening_strengthened(E, F, empty_env(), e, t);
  helper_env_nil_concat(concat(F, E));
}

ghost method lemma_typing_subst_var_case(E: env, F: env, u: exp, s: typ, t: typ, z: atom, x: atom)
  requires wf_env(E);
  requires wf_env(F);
  requires wf_env(concat(F, E));
  requires wf_env(concat(F, extends(z, s, E)));
  requires binds(x, t, concat(F, extends(z, s, E)));
  requires typing_c(E, u, s);
  ensures typing_c(concat(F, E), subst(z, u, fvar(x)), t);
{
  if (x == z) {
    assert subst(z, u, fvar(x)) == u;
    helper_binds_mid(E, F, z, s);
    helper_binds_uniq(concat(F, extends(z, s, E)), x, s, t);
    assert t == s;
    lemma_typing_c_weakening(E, F, u, s);
    assert typing_c(concat(F, E), subst(z, u, fvar(x)), t);
  } else {
  }
}

ghost method lemma_typing_c_to_lc_c(E: env, e: exp, t: typ)
  requires typing_c(E, e, t);
  ensures lc_c(e);
  decreases size(e);
{
  if (e.abs?) {
    var L := helper_abs_typing_c_L(E, e, t);
    forall (x | x !in L)
    ensures lc_c(open(e.body, fvar(x)));
    {
      lemma_typing_c_to_lc_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
    }
  } else if (e.app?) {
    assert exists t1 :: typing_c(E, e.f, typ_arrow(t1, t)) && typing_c(E, e.arg, t1);
    var t1 :| typing_c(E, e.f, typ_arrow(t1, t)) && typing_c(E, e.arg, t1);
    lemma_typing_c_to_lc_c(E, e.f, typ_arrow(t1, t));
    lemma_typing_c_to_lc_c(E, e.arg, t1);
  }
}

/*
WIP: Rethink the representation of environment to make this easier.
ghost method lemma_typing_c_subst(E: env, F: env, e: exp, u: exp, s: typ, t: typ, z: atom)
  requires wf_env(E);
  requires wf_env(F);
  requires wf_env(concat(F, E));
  requires wf_env(concat(F, extends(z, s, E)));
  requires typing_c(concat(F, extends(z, s, E)), e, t);
  requires typing_c(E, u, s);
  ensures typing_c(concat(F, E), subst(z, u, e), t);
  decreases size(e);
{
  var E' := concat(F, extends(z, s, E));
  var E'' := concat(F, E);
  if (e.fvar?) {
    lemma_typing_subst_var_case(E, F, u, s, t, z, e.x);
  } else if (e.abs?) {
    lemma_typing_c_to_lc_c(E, u, s);
    var L' := helper_abs_typing_c_L(E', e, t);
    var L'' := L'+F.vars+E.vars+[z];
    forall (x | x !in L'')
    {
      assert typing_c(extends(x, t.t1, E'), open(e.body, fvar(x)), t.t2);
      lemma_subst_open_var_c(z, x, u, e);
      lemma_typing_c_subst(E, extends(x, t.t1, F), open(e.body, fvar(x)), u, s, t.t2, z);
    }
    assume typing_c(concat(F, E), subst(z, u, e), t);
  } else if (e.app?) {
    assume typing_c(concat(F, E), subst(z, u, e), t);
  }
}
*/