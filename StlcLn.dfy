// The Simply Typed Lambda-Calculus
// Locally nameless representation with cofinite quantification
// http://www.cis.upenn.edu/~plclub/popl08-tutorial/code/index.html#stlc
// http://www.chargueraud.org/softs/ln/
// https://github.com/namin/coq-sandbox/blob/master/STLC.v

datatype atom = a(i: nat);

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

function fv(e: exp) : set<atom>
  decreases e;
{
  match e
  case bvar(i) => {}
  case fvar(x) => {x}
  case abs(e1) => fv(e1)
  case app(e1, e2) => fv(e1) + fv(e2)
}

ghost method lemma_subst_fresh(x: atom, e: exp, u: exp)
  requires !(x in fv(e));
  ensures subst(x, u, e) == e;
{
}

function open_rec(k: nat, u: exp, e: exp): exp
  decreases e;
{
  match e
  case bvar(i) => if k==i then u else bvar(i)
  case fvar(x) => fvar(x)
  case abs(e1) => abs(open_rec(k+1, u, e1))
  case app(e1, e2) => app(open_rec(k, u, e1), open_rec(k, u, e2))
}

function open(e: exp, u: exp): exp
{
  open_rec(0, u, e)
}

function open_rec_a(k: nat, a: atom, e: exp): exp
  decreases e;
  ensures size(e) == size(open_rec_a(k, a, e));
  ensures open_rec_a(k, a, e) == open_rec(k, fvar(a), e);
{
  match e
  case bvar(i) => if k==i then fvar(a) else bvar(i)
  case fvar(x) => fvar(x)
  case abs(e1) => abs(open_rec_a(k+1, a, e1))
  case app(e1, e2) => app(open_rec_a(k, a, e1), open_rec_a(k, a, e2))
}

function open_a(e: exp, a: atom): exp
  ensures size(e) == size(open_a(e, a));
  ensures open_a(e, a) == open(e, fvar(a));
{
  open_rec_a(0, a, e)
}

ghost method example_open(Y: atom)
  ensures open(app(abs(app(bvar(1), bvar(0))), bvar(0)), fvar(Y)) ==
               app(abs(app(fvar(Y), bvar(0))), fvar(Y));
{
  assert open_rec(1, fvar(Y), bvar(1)) == fvar(Y);
  assert open_rec(1, fvar(Y), bvar(0)) == bvar(0);
  assert open_rec(0, fvar(Y), abs(app(bvar(1), bvar(0)))) ==
                              abs(app(fvar(Y), bvar(0)));
  assert open_rec(0, fvar(Y), bvar(0)) == fvar(Y);
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

copredicate lc_fvar(e: exp)
  requires e.fvar?;
{
  true
}
copredicate lc_abs(e: exp, L: seq<atom>)
  requires e.abs?;
{
  forall x :: x !in L ==> lc(open_a(e.body, x), L)
}
copredicate lc_app(e: exp, L: seq<atom>)
  requires e.app?;
{
  lc(e.f, L) && lc(e.arg, L)
}
copredicate lc(e: exp, L: seq<atom>)
{
  (e.fvar? && lc_fvar(e)) ||
  (e.abs? && lc_abs(e, L)) ||
  (e.app? && lc_app(e, L))
}

ghost method lemma_open_rec_lc_core(e: exp, j: nat, v: exp, i: nat, u: exp)
  requires i != j;
  requires open_rec(j, v, e) == open_rec(i, u, open_rec(j, v, e));
  ensures e == open_rec(i, u, e);
  decreases e;
{
  if (e.abs?) {
    lemma_open_rec_lc_core(e.body, j+1, v, i+1, u);
  }
}

ghost method notin(L: seq<atom>) returns (r: atom)
  ensures r !in L;
  decreases L;
{
  var sup:nat := 0;
  var i: nat := 0;
  while (i < |L|)
    invariant 0 <= i <= |L|;
    invariant forall j :: 0 <= j < i ==> L[j].i <= sup;
  {
      if (L[i].i > sup) {
        sup := L[i].i;
      }
      i := i + 1;
    }
  r := a(sup+1);
}

ghost method lemma_open_rec_lc(k: nat, u: exp, e: exp, L: seq<atom>)
  requires lc(e, L);
  ensures e == open_rec(k, u, e);
  decreases size(e);
{
  if (e.abs?) {
    var x := notin(L);
    assert lc_abs(e, L);
    assert lc(open_a(e.body, x), L);
    lemma_open_rec_lc(k+1, u, open_a(e.body, x), L);
    assert open_rec(0, fvar(x), e.body) == open_rec(k+1, u, open_rec(0, fvar(x), e.body));
    lemma_open_rec_lc_core(e.body, 0, fvar(x), k+1, u);
    assert e.body == open_rec(k+1, u, e.body);
    assert e.body == open_rec(k+1, u, e.body);
  }
}

ghost method lemma_subst_open_rec(e1: exp, e2: exp, u: exp, x: atom, k: nat, L: seq<atom>)
  requires lc(u, L);
  ensures subst(x, u, open_rec(k, e2, e1)) == open_rec(k, subst(x, u, e2), subst(x, u, e1));
{
  if (e1.fvar? && e1.x==x) {
    lemma_open_rec_lc(k, subst(x, u, e2), u, L);
  }
  if (e1.abs?) {
    lemma_subst_open_rec(e1.body, e2, u, x, k+1, L);
  }
}

ghost method lemma_subst_open_var(x: atom, y: atom, u: exp, e: exp, L: seq<atom>)
  requires y != x;
  requires lc(u, L);
  ensures open(subst(x, u, e), fvar(y)) == subst(x, u, open(e, fvar(y)));
{
  lemma_subst_open_rec(e, fvar(y), u, x, 0, L);
}

ghost method lemma_subst_lc(x: atom, u: exp, e: exp)
  requires lc(e, [x]);
  requires lc(u, [x]);
  ensures lc(subst(x, u, e), [x]);
  decreases size(e);
{
  if (e.abs?) {
    var L := [x];
    assert lc_abs(e, L);
    parallel (y | y !in L)
      ensures lc(open(subst(x, u, e.body), fvar(y)), L);
    {
      lemma_subst_lc(x, u, open_a(e.body, y));
      assert open_a(e.body, y) == open(e.body, fvar(y));
      assert lc(open(e.body, fvar(y)), L);
      assert lc(subst(x, u, open(e.body, fvar(y))), L);
      lemma_subst_open_var(x, y, u, e.body, L);
      assert lc(open(subst(x, u, e.body), fvar(y)), L);
    }
    assert lc_abs(subst(x, u, e), L);
    assert lc(subst(x, u, e), L);
  }
}
