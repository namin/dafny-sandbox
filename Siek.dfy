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

function lookup<A,B>(k: A, L: map<A,B>): result<B>
{
  if (k in L) then Result(L[k]) else Stuck()
}

// values v ::= c | <f(x:T)e,env>
datatype closure = Closure(code: code, env: map<int,value>);
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

function evf(e: exp, env: map<int,value>, k: nat): result<value>
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
       evf(f.code.body, f.env[f.code.paramName:=varg.get][f.code.funName:=vf.get], k-1) else
       Stuck else
     Stuck else
  Stuck
}

predicate evals(e: exp, c: const)
{
  exists n:nat :: evf(e, map[], n) == Result(ConstVal(c))
}
predicate diverges(e: exp)
{
  forall n:nat :: evf(e, map[], n) == TimeOut
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
  requires t1.TInt? && t2.TInt?;
{
  match o
  case Plus => Some(TInt)
  case Minus => Some(TInt)
  case Eq => Some(TBool)
}

predicate typing(e: exp, G: map<int,ty>, T: ty)
  decreases e;
{
  match e
  case Var(x) =>
    var Tr := lookup(x, G);
    Tr.Result? && Tr.get==T
  case Const(c) => typeof(c) == Some(T)
  case Fun(c) =>
    T.TArrow? && c.paramType==T.a &&
    typing(c.body, G[c.paramName:=T.a][c.funName:=T], T.b)
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

copredicate wf_value(v: value, T: ty)
{
  match v
  case ConstVal(c) =>
    typeof(c) == Some(T)
  case ClosureVal(f) =>
    exists G :: wf_env(G, f.env) &&
    typing(f.code.body, G[f.code.paramName:=f.code.paramType][f.code.funName:=T], T)
}

copredicate wf_result(r: result<value>)
{
  match r
  case Result(v) => exists T :: wf_value(v, T)
  case TimeOut => true
  case Stuck => false
}

predicate wf_env(G: map<int, ty>, env: map<int,value>)
{
  // TODO: not well-founded!
  //forall x :: x in env ==> x in G && wf_value(env[x], G[x])
  true
}