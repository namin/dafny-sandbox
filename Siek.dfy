// Type Safety in Three Easy Lemmas
// in Dafny
// adapted from Jeremy Siek's blog post:
// http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html

// types       T ::= Int | Bool | T -> T
datatype ty = TInt | TBool | TArrow(a: ty, b: ty);
// variables   x,y, z
// integers    n
// operators   o ::= + | - | =
datatype op = Plus | Minus | Eq;
// booleans    b ::= true | false
// constants   c ::= n | b
datatype const = Num(n: int) | Bool(b: bool);
// expressions e ::= c | o(e,e) | x | fun f(x:T) e | e(e)
datatype code = Code(funName: int, paramName: int, paramType: ty, body: exp);
datatype exp = Const(c: const) | BinOp(o: op, e1: exp, e2: exp) | Var(x: int) | Fun(code: code) | App(f: exp, arg: exp);

// Dynamic Semantics

datatype result<A> = Result(get: A) | Stuck | TimeOut;

datatype pmap<A,B> = Extend(k: A, v: B, rest: pmap<A,B>) | Empty;
function lookup<A,B>(k: A, L: pmap<A,B>): result<B>
  decreases L;
{
  match L
  case Empty => Stuck
  case Extend(k', v', L') => if (k'==k) then Result(v') else lookup(k, L')
}

// values v ::= c | <f(x:T)e,env>
datatype closure = Closure(code: code, env: pmap<int,value>);
datatype value = ConstVal(const: const) | ClosureVal(clo: closure);

function toInt(v: value): result<int>
{
  if (v.ConstVal? && v.const.Num?) then Result(v.const.n) else Stuck
}
function toBool(v: value): result<bool>
{
  if (v.ConstVal? && v.const.Bool?) then Result(v.const.b) else Stuck
}
function toClosure(v: value): result<closure>
{
  if (v.ClosureVal?) then Result(v.clo) else Stuck
}

function num(n: int): value
{
  ConstVal(Num(n))
}
function boolean(b: bool): value
{
  ConstVal(Bool(b))
}

function evop(o: op, v1: value, v2: value): result<value>
  ensures o.Plus? || o.Minus? || o.Eq?;
{
  var n1 := toInt(v1);
  var n2 := toInt(v2);
  if (n1.Result? && n2.Result?) then
  Result(if (o.Plus?) then num(n1.get+n2.get)
  else if (o.Minus?) then num(n1.get-n2.get)
  else boolean(n1.get==n2.get))
  else Stuck
}

function chain<A>(v1: result<A>, v2: result<A>): result<A>
  requires !v1.Result? || !v2.Result?;
{
  if (v1.Result?) then v2 else v1
}

function evf(e: exp, env: pmap<int,value>, k: nat): result<value>
  decreases k;
{
  if (k==0) then TimeOut else
  if (e.Var?) then lookup(e.x, env) else
  if (e.Const?) then Result(ConstVal(e.c)) else
  if (e.Fun?) then Result(ClosureVal(Closure(e.code, env))) else
  if (e.BinOp?) then
     var v1 := evf(e.e1, env, k-1);
     var v2 := evf(e.e2, env, k-1);
     if (v1.Result? && v2.Result?) then
     evop(e.o, v1.get, v2.get) else
     chain(v1, v2) else
  if (e.App?) then
     var vf    := evf(e.f, env, k-1);
     var varg  := evf(e.arg, env, k-1);
     if (vf.Result? && varg.Result?) then
       var clo := toClosure(vf.get);
       if (clo.Result?) then
       var f := clo.get;
       evf(f.code.body, Extend(f.code.paramName, varg.get, Extend(f.code.funName, vf.get, f.env)), k-1) else
       Stuck else
     chain(vf, varg) else
  Stuck
}

predicate evals(e: exp, c: const)
{
  exists n:nat :: evf(e, Empty, n) == Result(ConstVal(c))
}
predicate diverges(e: exp)
{
  forall n:nat :: evf(e, Empty, n) == TimeOut
}

// Type System

datatype option<A> = Some(get: A) | None;

function typeof(c: const): option<ty>
  ensures c.Num? ==> typeof(c).Some? && typeof(c).get.TInt?;
  ensures c.Bool? ==> typeof(c).Some? && typeof(c).get.TBool?;
  ensures typeof(c).Some? ==> !typeof(c).get.TArrow?;
{
  match c
  case Num(n) => Some(TInt)
  case Bool(b) => Some(TBool)
}

function typebinop(o: op, t1: ty, t2: ty): option<ty>
{
  if (t1.TInt? && t2.TInt?) then typebinop'(o) else None
}

function typebinop'(o: op): option<ty>
{
  match o
  case Plus => Some(TInt)
  case Minus => Some(TInt)
  case Eq => Some(TBool)
}

predicate typing(e: exp, G: pmap<int,ty>, T: ty)
  decreases e;
{
  match e
  case Var(x) =>
    var Tr := lookup(x, G);
    Tr.Result? && Tr.get==T
  case Const(c) => typeof(c) == Some(T)
  case Fun(c) =>
    T.TArrow? && c.paramType==T.a &&
    typing(c.body, Extend(c.paramName, T.a, Extend(c.funName, T, G)), T.b)
  case App(e1, e2) =>
    exists T1 ::
    typing(e1, G, TArrow(T1, T)) &&
    typing(e2, G, T1)
  case BinOp(o, e1, e2) =>
    typing(e1, G, TInt) &&
    typing(e2, G, TInt) &&
    typebinop(o, TInt, TInt) == Some(T)
}

// Well-typed values, results, environments

predicate wf_value(v: value, T: ty)
  decreases v;
{
  match v
  case ConstVal(c) =>
    typeof(c) == Some(T)
  case ClosureVal(f) =>
    T.TArrow? &&
    f.code.paramType==T.a &&
    exists G :: wf_env(G, f.env) &&
    typing(f.code.body, Extend(f.code.paramName, T.a, Extend(f.code.funName, T, G)), T.b)
}

ghost method wf_value_inversion_const(v: value, T: ty)
  requires wf_value(v, T);
  requires T.TInt? || T.TBool?;
  ensures v.ConstVal?;
{
}

ghost method wf_value_inversion_fun(v: value, T: ty) returns (G: pmap<int,ty>)
  requires wf_value(v, T);
  requires T.TArrow?;
  ensures v.ClosureVal?;
  ensures wf_env(G, v.clo.env) &&
          typing(v.clo.code.body, Extend(v.clo.code.paramName, T.a, Extend(v.clo.code.funName, T, G)), T.b);
{
  var G_ :|
  wf_env(G_, v.clo.env) &&
  typing(v.clo.code.body, Extend(v.clo.code.paramName, T.a, Extend(v.clo.code.funName, T, G_)), T.b);
  G := G_;
}

predicate wf_result(r: result<value>)
{
  match r
  case Result(v) => exists T :: wf_value(v, T)
  case TimeOut => true
  case Stuck => false
}

predicate wf_env(G: pmap<int, ty>, env: pmap<int,value>)
  decreases env;
{
  match env
  case Empty => G.Empty?
  case Extend(k, v, env') => G.Extend? && G.k==k && wf_value(v, G.v) && wf_env(G.rest, env')
}

// Type Safety in Three Easy Lemmas

ghost method lemma1_safe_evop(o: op, v1: value, T1: ty, v2: value, T2: ty)
  requires typebinop(o, T1, T2).Some?;
  requires wf_value(v1, T1) && wf_value(v2, T2);
  ensures evop(o, v1, v2).Result?;
{
}

ghost method lemma2_safe_lookup(G: pmap<int, ty>, env: pmap<int,value>, x: int)
  requires wf_env(G, env);
  requires lookup(x, G).Result?;
  ensures lookup(x, env).Result? && wf_value(lookup(x, env).get, lookup(x, G).get);
  decreases env;
{
  match env {
  case Empty =>
  case Extend(k, v, env') =>
    if (k!=x) {
      lemma2_safe_lookup(G.rest, env', x);
    }
  }
}

ghost method lemma3_safe_evf(G: pmap<int, ty>, env: pmap<int,value>, T: ty, e: exp, k: nat)
  requires typing(e, G, T);
  requires wf_env(G, env);
  ensures evf(e, env, k).Result? || evf(e, env, k).TimeOut?;
  ensures !evf(e, env, k).Stuck?;
  ensures evf(e, env, k).Result? ==> wf_value(evf(e, env, k).get, T);
  decreases k;
{
  if (k==0) {
  } else if (e.Var?) {
    lemma2_safe_lookup(G, env, e.x);
  } else if (e.Const?) {
  } else if (e.Fun?) {
  } else if (e.BinOp?) {
    lemma3_safe_evf(G, env, TInt, e.e1, k-1);
    lemma3_safe_evf(G, env, TInt, e.e2, k-1);
    var v1 := evf(e.e1, env, k-1);
    var v2 := evf(e.e2, env, k-1);
    if (v1.Result? && v2.Result?) {
      lemma1_safe_evop(e.o, v1.get, TInt, v2.get, TInt);
    } else {
      assert v1.TimeOut? || v2.TimeOut?;
    }
  } else if (e.App?) {
    var T1 :|
    typing(e.f, G, TArrow(T1, T)) &&
    typing(e.arg, G, T1);

    lemma3_safe_evf(G, env, TArrow(T1, T), e.f, k-1);
    lemma3_safe_evf(G, env, T1, e.arg, k-1);
    var fo := evf(e.f, env, k-1);
    var arg := evf(e.arg, env, k-1);
    if (fo.Result? && arg.Result?) {
      var Gf := wf_value_inversion_fun(fo.get, TArrow(T1, T));
      assert fo.get.ClosureVal?;
      var f := fo.get.clo;
      var G' := Extend(f.code.paramName, T1, Extend(f.code.funName, TArrow(T1, T), Gf));
      var env' := Extend(f.code.paramName, arg.get, Extend(f.code.funName, fo.get, f.env));
      assert wf_env(G', env');
      lemma3_safe_evf(G', env', T, f.code.body, k-1);
    } else {
      assert fo.TimeOut? || arg.TimeOut?;
    }
  } else {}
}

ghost method theorem_type_safety(e: exp, T: ty)
  requires typing(e, Empty, T);
  requires T.TInt? || T.TBool?;
  ensures (exists c :: evals(e, c)) || diverges(e);
{
  if (!diverges(e)) {
    var k':nat :| !evf(e, Empty, k').TimeOut?;
    lemma3_safe_evf(Empty, Empty, T, e, k');
    var v := evf(e, Empty, k');
    assert v.Result?;
    wf_value_inversion_const(v.get, T);
    assert v.get.ConstVal?;
    assert evals(e, v.get.const);
  }
}