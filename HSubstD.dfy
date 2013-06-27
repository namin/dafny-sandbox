// Based on
// Hereditary Substitutions for Simple Types, Formalized
// http://hal.inria.fr/docs/00/52/06/06/PDF/msfp10.pdf

datatype option<T> = None | Some(get: T);
datatype Ty = Base | Arrow(a: Ty, b: Ty);
datatype Con = C(get: seq<Ty>);
datatype Var = V(n: nat);
datatype Nf = NfLam(T: Ty, body: Nf) |
              NfNe(ne: Ne);
datatype Ne = NeSp(v: Var, s: Sp);
datatype Sp = SpEpsilon(T: Ty) |
              SpCons(t1: Nf, t23: Sp);

function ty_nf(con: Con, f: Nf): option<Ty>
  decreases f;
{
  match f
  case NfLam(T, body) =>
    var tyb := ty_nf(C([T]+con.get), body);
	if (tyb.Some?) then
	Some(Arrow(T, tyb.get))
	else None
  case NfNe(ne) => Some(Base)
}

function tya_sp(con: Con, s: Sp): option<Ty>
{
  match s
  case SpEpsilon(T) => Some(T)
  case SpCons(t1, t23) =>
    var ty1 := ty_nf(con, t1);
	var ty2 := tya_sp(con, t23);
	if (ty1.Some? && ty2.Some?) then
	Some(Arrow(ty1.get, ty2.get))
	else None
}

function tyb_sp(con: Con, s: Sp): option<Ty>
{
  match s
  case SpEpsilon(T) => Some(T)
  case SpCons(t1, t23) => tyb_sp(con, t23)
}

function typ_var(con: Con, v: Var): option<Ty>
{
  if (v.n<|con.get|) then
  Some(con.get[v.n])
  else None
}

function typ_nf(con: Con, f: Nf): option<Ty>
  decreases f;
{
  match f
  case NfLam(T, body) =>
    var tyb := typ_nf(C([T]+con.get), body);
	if (tyb.Some?) then
	Some(Arrow(T, tyb.get))
	else None
  case NfNe(e) =>
    if (typ_ne(con, e)==Some(Base)) then
	Some(Base)
	else None
}

function typ_ne(con: Con, e: Ne): option<Ty>
  decreases e;
{
  match e
  case NeSp(v, s) =>
    var tyv := typ_var(con, v);
	var tya := tya_sp(con, s) ;
    var tyb := tyb_sp(con, s);
	if (tyv.Some? && tya.Some? && tyb.Some? && tyv.get==tya.get) then
	tya
	else None
}

predicate fn_nf(x: Var, f: Nf)
  decreases f;
{
  match f
  case NfLam(T, body) => fn_nf(V(x.n+1), body)
  case NfNe(e) => fn_ne(x, e)
}
predicate fn_ne(x: Var, e: Ne)
  decreases e;
{
  x.n==e.v.n || fn_sp(x, e.s)
}
predicate fn_sp(x: Var, s: Sp)
  decreases s;
{
  match s
  case SpEpsilon(T) => false
  case SpCons(t1, t23) => fn_nf(x, t1) || fn_sp(x, t23)
}

function wkn(xn: nat, yn: nat): nat
{
  if (yn-xn>=0) then yn+1 else yn
}
function wkv(x: Var, y: Var): Var
{
  V(wkn(x.n, y.n))
}
function wk_nf(x: Var, f: Nf): Nf
  decreases f;
{
  match f
  case NfLam(T, body) => NfLam(T, wk_nf(V(x.n+1), body))
  case NfNe(e) => NfNe(wk_ne(x, e))
}
function wk_ne(x: Var, e: Ne): Ne
  decreases e;
{
  NeSp(wkv(x, e.v), wk_sp(x, e.s))
}
function wk_sp(x: Var, s: Sp): Sp
  decreases s;
{
  match s
  case SpEpsilon(T) => SpEpsilon(T)
  case SpCons(t1, t23) => SpCons(wk_nf(x, t1), wk_sp(x, t23))
}

function app_sp(s: Sp, f: Nf): Sp
{
  match s
  case SpEpsilon(ty) =>
    SpCons(f, SpEpsilon(ty))
  case SpCons(t1, t23) =>
    SpCons(t1, app_sp(t23, f))
}

function nvar(con: Con, T: Ty, v: Var): option<Nf>
  decreases T, 1;
{
  ne2nf(con, T, NeSp(v, SpEpsilon(T)))
}
function ne2nf(con: Con, T: Ty, e: Ne): option<Nf>
  decreases T, 0;
{
  if (T.Base?) then Some(NfNe(e))
  else
    var con' := C([T.a]+con.get);
	var tyv := typ_var(con, e.v);
	if (tyv.Some?) then
	var x' := V(e.v.n+1);
	var vz := V(0);
	var r := nvar(con', T.a, vz);
	if (r.Some?) then
	var a := app_sp(wk_sp(vz, e.s), r.get);
	var r' := ne2nf(con', T.b, NeSp(x', a));
	if (r'.Some?) then
    Some(NfLam(T.a, r'.get))
	else None
	else None
	else None
}

function subst_nf(con: Con, T: Ty, t: Nf/*T*/, x: Var/*T*/, u: Nf/*T*/): option<Nf>
  decreases T, t;
{
  match t
  case NfLam(tya, body) =>
    if (T.Arrow? && tya==T.a) then
    var con' := C([tya]+con.get);
	var x' := V(x.n+1);
	var vz := V(0);
    var r := subst_nf(con', T.b, body, x', wk_nf(vz, u));
	if (r.Some?) then
	Some(NfLam(tya, r.get))
	else None
	else None
  case NfNe(e) =>
    match e
	case NeSp(y, ts) =>
	  var r := subst_sp(con, T, T, Base, ts, x, u);
	  if (r.None?) then None
	  else if (x==y) then if (T.Arrow?) then app_nf_sp(con, T, Base, u, r.get) else None
	  else Some(NfNe(NeSp(y, r.get)))
}

function subst_sp(con: Con, T: Ty, A: Ty, B: Ty, s: Sp/*A,B*/, x: Var/*T*/, u: Nf/*T*/): option<Sp/*A,B*/>
  decreases T, s;
{
  match s
  case SpEpsilon(ty) => Some(SpEpsilon(ty))
  case SpCons(t, ts) =>
    if (A.Arrow?) then
    var rt := subst_nf(con, A.a, t, x, u);
	var rts := subst_sp(con, T, A.b, B, ts, x, u);
	if (rt.None? || rts.None?) then None else
	Some(SpCons(rt.get, rts.get))
	else None
}

function app_nf_sp(con: Con, T: Ty, B: Ty, f: Nf/*T*/, s: Sp/*T,B*/): option<Nf>
  decreases T, s;
{
  match s
  case SpEpsilon(ty) => Some(f)
  case SpCons(u, us) =>
    if (T.Arrow?) then
    var r := napp(con, T.a, f, u);
	if (r.Some?) then
	app_nf_sp(con, T, B, r.get, us)
	else None
	else None
}

function napp(con: Con, T: Ty, f: Nf, u: Nf): option<Nf>
  decreases T, u;
{
  if (T.Arrow? && f.NfLam?) then
  subst_nf(con, T.b, f.body, V(0), u)
  else None
}