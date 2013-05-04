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

datatype pair<A, B> = P(fst: A, snd: B);
datatype option<A> = None | Some(get: A);

ghost method example_append_assoc<A>(s0: seq<A>, s1: seq<A>, s2: seq<A>, s3: seq<A>)
  ensures s0+(s1+s2)+s3 == s0+s1+s2+s3;
{
}

ghost method example_simpl_env(x: atom, y: atom, t1: typ, t2: typ, E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>)
  ensures ([P(x, t1)]+[])+([P(y,t2)]+[]+E)+F == [P(x,t1)]+[P(y,t2)]+E+F;
{
}

predicate binds(a: atom, t: typ, E: seq<pair<atom,typ>>)
  ensures binds(a, t, E) <==> P(a, t) in E;
{
  P(a, t) in E
}

ghost method example_binds(x: atom, t: typ, E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>)
  ensures binds(x, t, E+[P(x,t)]+F);
{
}

ghost method helper_binds_concat(E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, G: seq<pair<atom,typ>>, a: atom, t: typ)
  requires binds(a, t, G+E);
  ensures binds(a, t, G+F+E);
{
}

function lookup(a: atom, E: seq<pair<atom,typ>>): option<typ>
{
  if (E==[]) then None else if E[0].fst==a then Some(E[0].snd) else lookup(a, E[1..])
}

ghost method helper_no_lookup_no_binds(x: atom, E: seq<pair<atom,typ>>)
  requires lookup(x, E).None?;
  ensures forall t :: !binds(x, t, E);
{
}

function dom(E: seq<pair<atom,typ>>): seq<atom>
  ensures forall x :: x in dom(E) <==> lookup(x, E).Some?;
  ensures forall x :: x !in dom(E) <==> lookup(x, E).None?;
  ensures |E|>0 ==> forall x :: x in dom(E[1..]) ==> x in dom(E);
  ensures |E|==|dom(E)|;
  decreases |E|;
{
  if (E==[]) then [] else [E[0].fst]+dom(E[1..])
}

ghost method example_dom(x: atom, t: typ)
  ensures dom([P(x, t)]) == [x];
{
  calc == {
    dom([P(x, t)]);
    [P(x, t).fst]+dom([]);
    [x];
  }
}

predicate uniq(E: seq<pair<atom,typ>>)
{
  forall x, t1, t2 :: binds(x, t1, E) && binds(x, t2, E) ==> t1==t2
}

ghost method example_uniq(x: atom, y: atom, tx: typ, ty: typ)
  requires x != y;
  ensures uniq([P(x, tx), P(y, ty)]);
{
}

ghost method helper_uniq_extends(x: atom, t: typ, E: seq<pair<atom,typ>>)
  requires x !in dom(E);
  requires uniq(E);
  ensures uniq(extends(x, t, E));
{
  var E' := extends(x, t, E);
  forall (y, t1, t2 | binds(y, t1, E') && binds(y, t2, E'))
  ensures t1==t2;
  {
    if (x==y) {
      helper_no_lookup_no_binds(x, E);
      assert forall t :: !binds(x, t, E);
      assert t1==t;
      assert t1==t2;
    } else {
      assert binds(y, t1, E);
      assert binds(y, t2, E);
      assert t1==t2;
    }
  }
}

ghost method helper_uniq_parts(E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, G: seq<pair<atom,typ>>)
  requires uniq(G+F+E);
  ensures uniq(G+E);
{
  var E' := G+E;
  var E'' := G+F+E;
  forall (y, t1, t2 | binds(y, t1, E') && binds(y, t2, E'))
  ensures t1==t2;
  {
    assert binds(y, t1, E'');
    assert binds(y, t2, E'');
  }
}

function extends(a: atom, t: typ, E: seq<pair<atom,typ>>): seq<pair<atom,typ>>
  ensures extends(a, t, E)==[P(a, t)]+E;
{
  [P(a, t)]+E
}

ghost method helper_env_plus_assoc(a: atom, t: typ, E: seq<pair<atom,typ>>, G: seq<pair<atom,typ>>)
  ensures extends(a, t, G)+E == extends(a, t, G+E);
{
}

ghost method helper_env_plus_assoc2(a: atom, t: typ, E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, G: seq<pair<atom,typ>>)
  ensures extends(a, t, G+F+E) == extends(a, t, G)+F+E;
{
}

predicate typing_c(E: seq<pair<atom,typ>>, e: exp, t: typ)
  decreases size(e);
{
  (e.fvar? && uniq(E) && binds(e.x, t, E)) ||
  (e.abs? && t.typ_arrow? && exists L:seq<atom> :: forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2)) ||
  (e.app? && exists t1 :: typing_c(E, e.f, typ_arrow(t1, t)) && typing_c(E, e.arg, t1))
}

ghost method helper_abs_typing_c_L(E: seq<pair<atom,typ>>, e: exp, t: typ) returns (L:seq<atom>)
  requires e.abs?;
  requires typing_c(E, e, t);
  ensures t.typ_arrow?;
  ensures forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
{
  assert exists L:seq<atom> :: forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  var L_:seq<atom> :| forall x :: x !in L_ ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  L := L_;
}

ghost method helper_exists_abs_typing_c(L: seq<atom>, E: seq<pair<atom,typ>>, e: exp, t: typ)
  requires e.abs?;
  requires t.typ_arrow?;
  requires forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  ensures exists L:seq<atom> :: forall x :: x !in L ==> typing_c(extends(x, t.t1, E), open(e.body, fvar(x)), t.t2);
  ensures typing_c(E, e, t);
{
}

ghost method lemma_typing_c_weakening_strengthened(E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, G: seq<pair<atom,typ>>, e: exp, t: typ)
  requires typing_c(G+E, e, t);
  requires uniq(G+F+E);
  ensures typing_c(G+F+E, e, t);
  decreases size(e);
{
  var E' := G+E;
  var E'' := G+F+E;
  if (e.fvar?) {
    assert binds(e.x, t, E');
    helper_binds_concat(E, F, G, e.x, t);
    assert binds(e.x, t, E'');
    assert typing_c(E'', e, t);
  } else if (e.abs?) {
    var L' := helper_abs_typing_c_L(E', e, t);
    var L'':seq<atom> := L'+dom(E'');
    forall (x | x !in L'')
    ensures typing_c(extends(x, t.t1, E''), open(e.body, fvar(x)), t.t2);
    {
      assert x !in L';
      assert x !in dom(E'');
      helper_uniq_extends(x, t.t1, G+F+E);
      assert uniq(extends(x, t.t1, G+F+E));
      helper_env_plus_assoc2(x, t.t1, E, F, G);
      assert uniq(extends(x, t.t1, G)+F+E);

      assert typing_c(extends(x, t.t1, E'), open(e.body, fvar(x)), t.t2);
      helper_env_plus_assoc(x, t.t1, E, G);
      assert typing_c(extends(x, t.t1, G)+E, open(e.body, fvar(x)), t.t2);

      lemma_typing_c_weakening_strengthened(E, F, extends(x, t.t1, G), open(e.body, fvar(x)), t.t2);

      helper_env_plus_assoc(x, t.t1, F+E, G);
      assert typing_c(extends(x, t.t1, E''), open(e.body, fvar(x)), t.t2);
    }
    assert forall x :: x !in L'' ==> typing_c(extends(x, t.t1, E''), open(e.body, fvar(x)), t.t2);
    helper_exists_abs_typing_c(L'', E'', e, t);
  } else if (e.app?) {
    assert exists t1 :: typing_c(E', e.f, typ_arrow(t1, t)) && typing_c(E', e.arg, t1);
    var t1 :| typing_c(E', e.f, typ_arrow(t1, t)) && typing_c(E', e.arg, t1);
    lemma_typing_c_weakening_strengthened(E, F, G, e.f, typ_arrow(t1, t));
    lemma_typing_c_weakening_strengthened(E, F, G, e.arg, t1);
    assert typing_c(G+F+E, e, t);
  } else {
  }
}

ghost method lemma_typing_c_weakening(E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, e: exp, t: typ)
  requires typing_c(E, e, t);
  requires uniq(F+E);
  ensures typing_c(F+E, e, t);
{
  assert []+E==E;
  assert []+F+E==F+E;
  lemma_typing_c_weakening_strengthened(E, F, [], e, t);
}

ghost method lemma_typing_subst_var_case(E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, u: exp, s: typ, t: typ, z: atom, x: atom)
  requires uniq(F+[P(z, s)]+E);
  requires binds(x, t, F+[P(z, s)]+E);
  requires typing_c(E, u, s);
  ensures typing_c(F+E, subst(z, u, fvar(x)), t);
{
  if (x == z) {
    assert subst(z, u, fvar(x)) == u;
    assert binds(z, s, F+[P(z, s)]+E);
    assert t == s;
    helper_uniq_parts(E, [P(z, s)], F);
    lemma_typing_c_weakening(E, F, u, s);
    assert typing_c(F+E, subst(z, u, fvar(x)), t);
  } else {
    assert subst(z, u, fvar(x)) == fvar(x);
    assert binds(x, t, F+[P(z, s)]+E);
    assert binds(x, t, F+E);
    helper_uniq_parts(E, [P(z, s)], F);
  }
}

ghost method lemma_typing_c_to_lc_c(E: seq<pair<atom,typ>>, e: exp, t: typ)
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

ghost method lemma_typing_c_subst(E: seq<pair<atom,typ>>, F: seq<pair<atom,typ>>, e: exp, u: exp, s: typ, t: typ, z: atom)
  requires typing_c(F+[P(z,s)]+E, e, t);
  requires typing_c(E, u, s);
  ensures typing_c(F+E, subst(z, u, e), t);
  decreases size(e);
{
  var E' := F+[P(z,s)]+E;
  var E'' := F+E;
  if (e.fvar?) {
    lemma_typing_subst_var_case(E, F, u, s, t, z, e.x);
  } else if (e.abs?) {
    var L' := helper_abs_typing_c_L(E', e, t);
    var L'' := L'+[z]+dom(E');
    forall (x | x !in L'')
    ensures typing_c(extends(x, t.t1, F+E), open(subst(z, u, e.body), fvar(x)), t.t2) && x !=z;
    {
      assert x !in L';
      assert x != z;
      assert typing_c(extends(x, t.t1, E'), open(e.body, fvar(x)), t.t2);
      helper_env_plus_assoc2(x, t.t1, E, [P(z,s)], F);
      assert typing_c(extends(x, t.t1, F)+[P(z,s)]+E, open(e.body, fvar(x)), t.t2);
      lemma_typing_c_subst(E, extends(x, t.t1, F), open(e.body, fvar(x)), u, s, t.t2, z);
      assert typing_c(extends(x, t.t1, F)+E, subst(z, u, open(e.body, fvar(x))), t.t2);
      helper_env_plus_assoc(x, t.t1, E, F);
      assert typing_c(extends(x, t.t1, F+E), subst(z, u, open(e.body, fvar(x))), t.t2);
      lemma_typing_c_to_lc_c(E, u, s);
      lemma_subst_open_var_c(z, x, u, e.body);
      assert subst(z, u, open(e.body, fvar(x))) == open(subst(z, u, e.body), fvar(x));
      assert typing_c(extends(x, t.t1, F+E), open(subst(z, u, e.body), fvar(x)), t.t2);
    }
    helper_exists_abs_typing_c(L'', E'', subst(z, u, e), t);
  } else if (e.app?) {
  } else {
  }
}

ghost method lemma_typing_c_subst_simple(E: seq<pair<atom,typ>>, e: exp, u: exp, s: typ, t: typ, z: atom)
  requires typing_c(extends(z, s, E), e, t);
  requires typing_c(E, u, s);
  ensures typing_c(E, subst(z, u, e), t);
{
  assert []+[P(z,s)]+E==extends(z, s, E);
  lemma_typing_c_subst(E, [], e, u, s, t, z);
  assert []+E==E;
}

predicate value_c(e: exp)
{
  e.abs? && lc_c(e)
}

function eval_c(e: exp): option<exp>
{
  /* beta */
  if (e.app? && e.f.abs? && lc_c(e.f) && value_c(e.arg))
  then Some(open(e.f.body, e.arg))
  /* app f */
  else if (e.app? && lc_c(e.arg) && eval_c(e.f).Some?)
  then Some(app(eval_c(e.f).get, e.arg))
  /* app arg */
  else if (e.app? && value_c(e.f) && eval_c(e.arg).Some?)
  then Some(app(e.f, eval_c(e.arg).get))
  else None
}

ghost method theorem_preservation_c(E: seq<pair<atom,typ>>, e: exp, t: typ)
  requires typing_c(E, e, t);
  requires eval_c(e).Some?;
  ensures typing_c(E, eval_c(e).get, t);
{
  if (e.app? && e.f.abs? && lc_c(e.f) && value_c(e.arg)) {
    assert exists t1 :: typing_c(E, e.f, typ_arrow(t1, t)) && typing_c(E, e.arg, t1);
    var t1 :| typing_c(E, e.f, typ_arrow(t1, t)) && typing_c(E, e.arg, t1);
    var L := helper_abs_typing_c_L(E, e.f, typ_arrow(t1, t));
    var y := fresh_from(L+fv(e.f.body));
    assert typing_c(extends(y, t1, E), open(e.f.body, fvar(y)), t);
    lemma_typing_c_subst_simple(E, open(e.f.body, fvar(y)), e.arg, t1, t, y);
    assert typing_c(E, subst(y, e.arg, open(e.f.body, fvar(y))), t);
    assert y !in fv(e.f.body);
    lemma_subst_intro(y, e.arg, e.f.body);
    assert typing_c(E, open(e.f.body, e.arg), t);
    assert typing_c(E, eval_c(e).get, t);
  }
}
