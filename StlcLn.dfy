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

datatype typ = typ_base | typ_arrow(typ, typ);

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
  (e.abs? && forall L:seq<atom>, x :: x !in L ==> lc_c(open(e.body, fvar(x)))) ||
  (e.app? && lc_c(e.f) && lc_c(e.arg))
}

ghost method lemma_open_rec_lc_c(k: nat, u: exp, e: exp)
  requires lc_c(e);
  ensures e == open_rec(k, u, e);
  decreases size(e);
{
  if (e.abs?) {
    assert open_rec(k, u, e) == abs(open_rec(k+1, u, e.body));
    var x := fresh_from(fv(e));
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
