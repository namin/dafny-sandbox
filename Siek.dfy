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

datatype pair<A,B> = P(fst: A, snd: B);
datatype pmap<A,B> = M(m: seq<pair<A,B>>);
function empty<A,B>(): pmap<A,B>
{
  M([])
}
function extend<A,B>(k: A, v: B, L: pmap<A,B>): pmap<A,B>
{
  M([P(k,v)]+L.m)
}
function lookup<A,B>(k: A, L: pmap<A,B>): result<B>
  decreases L.m;
{
  if (L.m==[]) then Stuck() else
  if (L.m[0].fst==k) then Result(L.m[0].snd) else
  lookup(k, M(L.m[1..]))
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
     Stuck else
  if (e.App?) then
     var vf    := evf(e.f, env, k-1);
     var varg  := evf(e.arg, env, k-1);
     if (vf.Result? && varg.Result?) then
       var clo := toClosure(vf.get);
       if (clo.Result?) then
       var f := clo.get;
       evf(f.code.body, extend(f.code.paramName, varg.get, extend(f.code.funName, vf.get, f.env)), k-1) else
       Stuck else
     Stuck else
  Stuck
}

predicate evals(e: exp, c: const)
{
  exists n:nat :: evf(e, empty(), n) == Result(ConstVal(c))
}
predicate diverges(e: exp)
{
  forall n:nat :: evf(e, empty(), n) == TimeOut
}

// Type System

datatype option<A> = Some(get: A) | None;

function typeof(c: const): option<ty>
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
    typing(c.body, extend(c.paramName, T.a, extend(c.funName, T, G)), T.b)
  case App(e1, e2) =>
    exists T1 ::
    typing(e1, G, TArrow(T1, T)) &&
    typing(e2, G, T)
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
    exists G :: wf_env(G, f.env) &&
    typing(f.code.body, extend(f.code.paramName, f.code.paramType, extend(f.code.funName, T, G)), T)
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
  |G.m|==|env.m| &&
  forall i:nat :: 0<i<|env.m| ==> env.m[i].fst==G.m[i].fst && wf_value(env.m[i].snd, G.m[i].snd)
}

// Type Safety in Three Easy Lemmas

ghost method lemma1_safe_evop(o: op, v1: value, T1: ty, v2: value, T2: ty, R: ty)
  requires typebinop(o, T1, T2)==Some(R);
  requires wf_value(v1, T1) && wf_value(v2, T2);
  ensures evop(o, v1, v2).Result?;
{
}
