// Based on
// Hereditary Substitutions for Simple Types, Formalized
// http://hal.inria.fr/docs/00/52/06/06/PDF/msfp10.pdf

datatype option<T> = None | Some(get: T);
datatype Ty = Base | Arrow(a: Ty, b: Ty);
datatype Con = C(get: seq<Ty>);
datatype Var = V(con: Con, ty: Ty, n: nat);
datatype Nf = NfLam(con_lam: Con, tya: Ty, tyb: Ty, body: Nf) |
              NfNe(con_ne: Con, ne: Ne);
datatype Ne = NeSp(con: Con, ty_var: Ty, ty: Ty, v: Var, s: Sp);
datatype Sp = SpEpsilon(con_epsilon: Con, ty_epsilon: Ty) |
              SpCons(con: Con, ty1: Ty, ty2: Ty, ty3: Ty, t1: Nf, t23: Sp);

function con_nf(f: Nf): Con
{
  match f
  case NfLam(con, tya, tyb, body) => con
  case NfNe(con, ne) => con
}

function con_sp(s: Sp): Con
{
  match s
  case SpEpsilon(con, ty) => con
  case SpCons(con, ty1, ty2, ty3, t1, t23) => con
}

function ty_nf(f: Nf): Ty
{
  match f
  case NfLam(con, tya, tyb, body) => Arrow(tya, tyb)
  case NfNe(con, ne) => Base
}

function tya_sp(s: Sp): Ty
{
  match s
  case SpEpsilon(con, ty) => ty
  case SpCons(con, ty1, ty2, ty3, t1, t23) => Arrow(ty1, ty2)
}

function tyb_sp(s: Sp): Ty
{
  match s
  case SpEpsilon(con, ty) => ty
  case SpCons(con, ty1, ty2, ty3, t1, t23) => ty3
}

predicate valid_var(v: Var)
{
  v.n<|v.con.get| && v.con.get[v.n]==v.ty
}

predicate valid_nf(f: Nf)
{
  match f
  case NfLam(con, tya, tyb, body) =>
    con_nf(body).get==[tya]+con.get && ty_nf(body)==tyb && valid_nf(body)
  case NfNe(con, e) =>
    e.ty==Base && e.con==con && valid_ne(e)
}

predicate valid_ne(e: Ne)
{
  match e
  case NeSp(con, ty_var, ty, v, s) =>
    v.con==con && con_sp(s)==con && v.ty==tya_sp(s) && ty==tyb_sp(s) && valid_var(v) && valid_sp(s)
}

predicate valid_sp(s: Sp)
{
  match s
  case SpEpsilon(con, ty) => true
  case SpCons(con, ty1, ty2, ty3, t1, t23) =>
    con==con_nf(t1) && con==con_sp(t23) && ty1==ty_nf(t1) && ty2==tya_sp(t23) && ty3==tyb_sp(t23) && valid_nf(t1) && valid_sp(t23)
}

function con_del(con: Con, v: Var): Con
  requires valid_var(v) && v.con==con;
  decreases con.get;
  ensures |con_del(con, v).get|+1==|con.get|;
  ensures forall i:nat :: i<v.n ==> con.get[i]==con_del(con, v).get[i];
  ensures forall i:nat :: v.n<i && i<|con.get|-1 ==> con.get[i+1]==con_del(con, v).get[i];
{
  if (v.n==0) then C(con.get[1..])
  else C([con.get[0]]+con_del(C(con.get[1..]), V(C(con.get[1..]), v.ty, v.n-1)).get)
}

predicate fn_nf(x: Var, f: Nf)
  decreases f;
{
  match f
  case NfLam(con, tya, tyb, body) => fn_nf(V(C([tya]+x.con.get), x.ty, x.n+1), body)
  case NfNe(con, e) => fn_ne(x, e)
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
  case SpEpsilon(con, ty) => false
  case SpCons(con, ty1, ty2, ty3, t1, t23) => fn_nf(x, t1) || fn_sp(x, t23)
}

function wkn(xn: nat, yn: nat): nat
{
  if (yn-xn>=0) then yn+1 else yn
}
function wkv(x: Var, y: Var): Var
{
  V(x.con, y.ty, wkn(x.n, y.n))
}
function wk_nf(x: Var, f: Nf): Nf
  decreases f;
{
  match f
  case NfLam(con, tya, tyb, body) => NfLam(x.con, tya, tyb, wk_nf(V(C([tya]+x.con.get), x.ty, x.n+1), body))
  case NfNe(con, e) => NfNe(x.con, wk_ne(x, e))
}
function wk_ne(x: Var, e: Ne): Ne
  decreases e;
{
  NeSp(x.con, e.ty_var, e.ty, wkv(x, e.v), wk_sp(x, e.s))
}
function wk_sp(x: Var, s: Sp): Sp
  decreases s;
{
  match s
  case SpEpsilon(con, ty) => SpEpsilon(x.con, ty)
  case SpCons(con, ty1, ty2, ty3, t1, t23) => SpCons(x.con, ty1, ty2, ty3, wk_nf(x, t1), wk_sp(x, t23))
}

ghost method lemma_wkv_valid(x: Var, y: Var, out: Var)
  requires wkv(x, y)==out;
  requires valid_var(x) && valid_var(y) && y.con==con_del(x.con, x) && y.n!=x.n;
  ensures out.con==x.con && out.ty==y.ty && valid_var(out);
{
}

ghost method lemma_wk_nf_valid(x: Var, f: Nf, out: Nf)
  requires wk_nf(x, f)==out;
  requires valid_var(x) && valid_nf(f) && con_nf(f)==con_del(x.con, x) && !fn_nf(x, f);
  ensures con_nf(out)==x.con && ty_nf(out)==ty_nf(f) && valid_nf(out);
  decreases f;
{
  match f {
  case NfLam(con, tya, tyb, body) =>
    var x' := V(C([tya]+x.con.get), x.ty, x.n+1);
    calc == {
	  con_nf(body).get;
	  [tya]+con_nf(f).get;
	  [tya]+con_del(x.con, x).get;
	  con_del(C([tya]+x.con.get), V(C([tya]+x.con.get), x.ty, x.n+1)).get;
	  con_del(x'.con, x').get;
	}
	assert con_nf(body).get==con_del(x'.con, x').get;
	lemma_wk_nf_valid(x', body, out.body);
  case NfNe(con, e) =>
    lemma_wk_ne_valid(x, e, out.ne);
  }
}

ghost method lemma_wk_ne_valid(x: Var, e: Ne, out: Ne)
  requires wk_ne(x, e)==out;
  requires valid_var(x) && valid_ne(e) && e.con==con_del(x.con, x) && !fn_ne(x, e);
  ensures wk_ne(x, e).con==x.con && wk_ne(x, e).ty==e.ty && valid_ne(wk_ne(x, e));
  decreases e;
{
  lemma_wkv_valid(x, e.v, out.v);
  lemma_wk_sp_valid(x, e.s, out.s);
}

ghost method lemma_wk_sp_valid(x: Var, s: Sp, out: Sp)
  requires wk_sp(x, s)==out;
  requires valid_var(x) && valid_sp(s) && con_sp(s)==con_del(x.con, x) && !fn_sp(x, s);
  ensures con_sp(out)==x.con && tya_sp(out)==tya_sp(s) && tyb_sp(out)==tyb_sp(s) && valid_sp(out);
  decreases s;
{
  match s {
  case SpEpsilon(con, ty) =>
  case SpCons(con, ty1, ty2, ty3, t1, t23) =>
	lemma_wk_nf_valid(x, t1, out.t1);
	lemma_wk_sp_valid(x, t23, out.t23);
  }
}

function app_sp(s: Sp, f: Nf): option<Sp>
{
  match s
  case SpEpsilon(con, ty) =>
    if (tyb_sp(s).Arrow?) then
    Some(SpCons(con, ty.a, ty.b, ty.b, f, SpEpsilon(con, ty)))
	else None
  case SpCons(con, ty1, ty2, ty3, t1, t23) =>
    var r := app_sp(t23, f);
	if (r.Some? && tyb_sp(s).Arrow?)
    then Some(SpCons(con, ty1, ty2, ty3.b, t1, r.get))
	else None
}

ghost method lemma_app_sp_valid(s: Sp, f: Nf, out: option<Sp>)
  requires valid_sp(s) && valid_nf(f);
  requires con_sp(s)==con_nf(f);
  requires tyb_sp(s).Arrow? && tyb_sp(s).a==ty_nf(f);
  requires app_sp(s, f)==out;
  ensures out.Some?;
  ensures con_sp(s)==con_sp(out.get) && tya_sp(s)==tya_sp(out.get) && tyb_sp(s).b==tyb_sp(out.get);
{
  if (s.SpCons?) {
    if (out.None?) {
	  lemma_app_sp_valid(s.t23, f, None);
	  assert false;
	} else {
      lemma_app_sp_valid(s.t23, f, Some(out.get.t23));
	}
  }
}

function nvar(v: Var): option<Nf>
  decreases v.ty, 1;
{
  ne2nf(NeSp(v.con, v.ty, v.ty, v, SpEpsilon(v.con, v.ty)))
}
function ne2nf(e: Ne): option<Nf>
  decreases e.ty, 0;
{
  if (e.ty.Base?) then Some(NfNe(e.con, e))
  else
    var con' := C([e.ty.a]+e.con.get);
	var x' := V(con', e.v.ty, e.v.n+1);
	var vz := V(con', e.ty.a, 0);
	var r := nvar(vz);
	if (r.Some?) then
	var a := app_sp(wk_sp(vz, e.s), r.get);
	if (a.Some?) then
	var r' := ne2nf(NeSp(con', e.ty_var, e.ty.b, x', a.get));
	if (r'.Some?) then
    Some(NfLam(e.con, e.ty.a, e.ty.b, r'.get))
	else None
	else None
	else None
}

function subst_nf(t: Nf, x: Var, u: Nf): option<Nf>
  decreases x.ty, t;
{
  match t
  case NfLam(con, tya, tyb, body) =>
    var con' := C([tya]+con.get);
	var x' := V(con', x.ty, x.n+1);
	var vz := V(con', tya, 0);
    var r := subst_nf(body, x', wk_nf(vz, u));
	if (r.Some?) then Some(NfLam(con, tya, tyb, r.get)) else None
  case NfNe(con, e) =>
    match e
	case NeSp(con_, ty_var, ty, y, ts) =>
	  var r := subst_sp(ts, x, u);
	  if (r.None?) then None
	  else if (x==y) then if (ty_nf(t)==ty_nf(u) && ty_nf(u).Arrow?) then app_nf_sp(u, r.get) else None
	  else Some(NfNe(con, NeSp(con, ty_var, ty, y, r.get)))
}

function subst_sp(s: Sp, x: Var, u: Nf): option<Sp>
  decreases x.ty, s;
{
  match s
  case SpEpsilon(con, ty) => Some(SpEpsilon(con, ty))
  case SpCons(con, ty1, ty2, ty3, t, ts) =>
    var rt := subst_nf(t, x, u);
	var rts := subst_sp(ts, x, u);
	if (rt.None? || rts.None?) then None else Some(SpCons(con, ty1, ty2, ty3, rt.get, rts.get))
}

function app_nf_sp(f: Nf, s: Sp): option<Nf>
  decreases ty_nf(f), s;
{
  match s
  case SpEpsilon(con, ty) => Some(f)
  case SpCons(con, ty1, ty2, ty3, u, us) =>
    var r := napp(f, u);
	if (r.Some? && f.NfLam? && ty_nf(r.get)==ty_nf(f)) then app_nf_sp(r.get, us) else None
}

function napp(f: Nf, u: Nf): option<Nf>
  decreases ty_nf(f), u;
{
  if (f.NfLam?) then
  subst_nf(f.body, V(con_nf(f.body), f.tya, 0), u)
  else None
}