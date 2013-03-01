// References: Typing Mutable References
// http://www.cis.upenn.edu/~bcpierce/sf/References.html

// ---------
// Utilities
// ---------

// ### Pair ###
datatype pair<A, B> = P(fst: A, snd: B);

// ### Option ###
datatype option<A> = None | Some(get: A);

// ------
// Syntax
// ------

// Types
datatype ty = TNat | TUnit| TArrow(paramT: ty, returnT: ty) | TRef(cellT: ty);

// Terms
datatype tm = tvar(id: nat) | tapp(f: tm, arg: tm) | tabs(x: nat, T: ty, body: tm) |
              tnat(n: nat) | tsucc(pn: tm) | tpred(sn: tm) | tmult(n1: tm, n2: tm) | tif0(c: tm, a: tm, b: tm) |
              tunit | tref(v: tm) | tderef(cell: tm) | tassign(lhs: tm, rhs: tm) | tloc(l: nat);

// Derived Terms
// Side Effects and Sequencing
function tseq(t1: tm, t2: tm): tm
{
  tapp(tabs(0, TUnit, t2), t1)
}

// ---------------------
// Operational Semantics
// ---------------------

// Values
function value(t: tm): bool
{
  t.tabs? || t.tnat? || t.tunit? || t.tloc?
}

// Substitution
function subst(x: nat, s: tm, t: tm): tm
{
  match t
  case tvar(x') => if x==x' then s else t
  case tabs(x', T, t1) => tabs(x', T, if x==x' then t1 else subst(x, s, t1))
  case tapp(t1, t2) => tapp(subst(x, s, t1), subst(x, s, t2))
  case tnat(n) => t
  case tsucc(pn) => tsucc(subst(x, s, pn))
  case tpred(sn) => tpred(subst(x, s, sn))
  case tmult(n1, n2) => tmult(subst(x, s, n1), subst(x, s, n2))
  case tif0(c, a, b) => tif0(subst(x, s, c), subst(x, s, a), subst(x, s, b))
  case tunit => t
  case tref(v) => tref(subst(x, s, v))
  case tderef(cell) => tderef(subst(x, s, cell))
  case tassign(lhs, rhs) => tassign(subst(x, s, lhs), subst(x, s, rhs))
  case tloc(l) => t
}

// Stores
datatype store<A> = Store(m: seq<A>);

function store_lookup<A>(n: nat, st: store<A>): A
  requires n < |st.m|;
{
  st.m[n]
}

function store_extend<A>(st: store<A>, t: A): store<A>
  ensures |st.m|+1 == |store_extend(st, t).m|;
  ensures forall n:nat :: n < |st.m| ==> store_lookup(n, st) == store_lookup(n, store_extend(st, t));
  ensures store_lookup(|st.m|, store_extend(st, t)) == t;
{
  Store(st.m + [t])
}

function store_replace<A>(n: nat, t: A, st: store<A>): store<A>
{
  if (n >= |st.m|) then st else Store(st.m[0..n] + [t] + st.m[n+1..])
}

ghost method lemma_store_replace_nil<A>(n: nat, t: A)
  ensures store_replace(n, t, Store([])) == Store([]);
{
}
ghost method lemma_store_length_replace<A>(n: nat, t: A, st: store<A>)
  ensures |store_replace(n, t, st).m| == |st.m|;
{
}
ghost method lemma_store_lookup_replace_neq<A>(n1: nat, n2: nat, t: A, st: store<A>)
  requires n1 < |st.m| && n2 < |st.m|;
  requires n1 != n2;
  ensures store_lookup(n1, store_replace(n2, t, st)) == store_lookup(n1, st);
{
}

// Reduction
function step(t: tm, st: store<tm>): option<pair<tm, store<tm>>>
{
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) then Some(P(subst(t.f.x, t.arg, t.f.body), st))
  /* App1 */       else if (t.tapp? && step(t.f,st).Some?) then Some(P(tapp(step(t.f,st).get.fst, t.arg), step(t.f,st).get.snd))
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg,st).Some?) then Some(P(tapp(t.f, step(t.arg,st).get.fst),step(t.arg,st).get.snd))
  /* SuccNat */    else if (t.tsucc? && t.pn.tnat?) then Some(P(tnat(t.pn.n+1),st))
  /* Succ */       else if (t.tsucc? && step(t.pn,st).Some?) then Some(P(tsucc(step(t.pn,st).get.fst),step(t.pn,st).get.snd))
  /* PredNat */    else if (t.tpred? && t.sn.tnat?) then Some(P(tnat(if (t.sn.n==0) then 0 else t.sn.n-1),st))
  /* Pred */       else if (t.tpred? && step(t.sn,st).Some?) then Some(P(tpred(step(t.sn,st).get.fst),step(t.sn,st).get.snd))
  /* MultNats */   else if (t.tmult? && t.n1.tnat? && t.n2.tnat?) then Some(P(tnat(t.n1.n*t.n2.n),st))
  /* Mult1 */      else if (t.tmult? && step(t.n1, st).Some?) then Some(P(tmult(step(t.n1, st).get.fst, t.n2), step(t.n1, st).get.snd))
  /* Mult2 */      else if (t.tmult? && value(t.n1) && step(t.n2, st).Some?) then Some(P(tmult(t.n1, step(t.n2, st).get.fst), step(t.n2, st).get.snd))
  /* If0 */        else if (t.tif0? && step(t.c, st).Some?) then Some(P(tif0(step(t.c, st).get.fst, t.a, t.b), step(t.c, st).get.snd))
  /* If0_Zero */   else if (t.tif0? && t.c.tnat? && t.c.n==0) then Some(P(t.a, st))
  /* If0_NonZero */else if (t.tif0? && t.c.tnat? && t.c.n!=0) then Some(P(t.b, st))
  /* RefValue */   else if (t.tref? && value(t.v)) then Some(P(tloc(|st.m|), store_extend(st, t.v)))
  /* Ref */        else if (t.tref? && step(t.v, st).Some?) then Some(P(tref(step(t.v, st).get.fst), step(t.v, st).get.snd))
  /* DerefLoc */   else if (t.tderef? && t.cell.tloc? && t.cell.l < |st.m|) then Some(P(store_lookup(t.cell.l, st), st))
  /* Deref */      else if (t.tderef? && step(t.cell, st).Some?) then Some(P(tderef(step(t.cell, st).get.fst), step(t.cell, st).get.snd))
  /* Assign */     else if (t.tassign? && t.lhs.tloc? && value(t.rhs) && t.lhs.l < |st.m|) then Some(P(tunit, store_replace(t.lhs.l, t.rhs, st)))
  /* Assign1 */    else if (t.tassign? && step(t.lhs, st).Some?) then Some(P(tassign(step(t.lhs, st).get.fst, t.rhs), step(t.lhs, st).get.snd))
  /* Assign2 */    else if (t.tassign? && value(t.lhs) && step(t.rhs, st).Some?) then Some(P(tassign(t.lhs, step(t.rhs, st).get.fst), step(t.rhs, st).get.snd))
                   else None
}

predicate mstep(t: tm, s: store<tm>, t': tm, s': store<tm>, n: nat)
  decreases n;
{
  if (n==0) then t == t' && s == s'
  else step(t, s).Some? && mstep(step(t, s).get.fst, step(t, s).get.snd, t', s', n-1)
}

// Properties of multistep

ghost method lemma_mstep_trans(t1: tm, s1: store<tm>, t2: tm, s2: store<tm>, t3: tm, s3: store<tm>, n12: nat, n23: nat)
  requires mstep(t1, s1, t2, s2, n12);
  requires mstep(t2, s2, t3, s3, n23);
  ensures mstep(t1, s1, t3, s3, n12+n23);
  decreases n12+n23;
{
  if (n12>0) {
    lemma_mstep_trans(step(t1, s1).get.fst, step(t1, s1).get.snd, t2, s2, t3, s3, n12-1, n23);
  } else if (n23>0) {
    lemma_mstep_trans(step(t1, s1).get.fst, step(t1, s1).get.snd, step(t2, s2).get.fst, step(t2, s2).get.snd, t3, s3, n12, n23-1);
  }
}

ghost method lemma_mstep_trans'(t1: tm, s1: store<tm>, t2: tm, s2: store<tm>, t3: tm, s3: store<tm>, n12: nat, n13: nat)
  requires n12 <= n13;
  requires mstep(t1, s1, t2, s2, n12);
  requires mstep(t1, s1, t3, s3, n13);
  ensures mstep(t2, s2, t3, s3, n13-n12);
  decreases n12;
{
  if (n12>0 && n13>0) {
    lemma_mstep_trans'(step(t1, s1).get.fst, step(t1, s1).get.snd, t2, s2, t3, s3, n12-1, n13-1);
  }
}

// ------
// Typing
// ------

// Contexts
datatype context = Context(m: seq<pair<int,ty>>);
function context_extend(ctx: context, x: nat, T: ty): context
{
  Context([P(x, T)]+ctx.m)
}
function context_lookup(ctx: context, x: nat): option<ty>
  decreases |ctx.m|;
{
  if (|ctx.m|==0) then None
  else if (ctx.m[0].fst==x) then Some(ctx.m[0].snd)
  else context_lookup(Context(ctx.m[1..]), x)
}

// Store Typings
// store<ty>

function has_type(G: context, ST: store<ty>, t: tm): option<ty>
  decreases t;
{
  match t
  /* Var */        case tvar(x) => context_lookup(G, x)
  /* Abs */        case tabs(x, T11, t12) =>
                     var optT12 := has_type(context_extend(G, x, T11), ST, t12);
                     if (optT12.Some?) then Some(TArrow(T11, optT12.get)) else None
  /* App */        case tapp(t1, t2) =>
                     var optT1 := has_type(G, ST, t1);
                     var optT2 := has_type(G, ST, t2);
                     if (optT1.Some? && optT2.Some? && optT1.get.TArrow? && optT1.get.paramT==optT2.get)
                     then Some(optT1.get.returnT)
                     else None
  /* Nat */        case tnat(n) => Some(TNat)
  /* Succ */       case tsucc(t1) => if (has_type(G, ST, t1) == Some(TNat)) then Some(TNat) else None
  /* Pred */       case tpred(t1) => if (has_type(G, ST, t1) == Some(TNat)) then Some(TNat) else None
  /* TMult */      case tmult(t1, t2) => if (has_type(G, ST, t1) == Some(TNat) && has_type(G, ST, t2) == Some(TNat)) then Some(TNat) else None
  /* If0 */        case tif0(t1, t2, t3) =>
                     var optT1 := has_type(G, ST, t1);
                     var optT2 := has_type(G, ST, t2);
                     var optT3 := has_type(G, ST, t3);
                     if (optT1.Some? && optT2.Some? && optT3.Some? && optT1.get.TNat? && optT2.get == optT3.get)
                     then Some(optT2.get)
                     else None
  /* Unit */       case tunit => Some(TUnit)
  /* Loc */        case tloc(l) => if (l < |ST.m|) then Some(TRef(store_lookup(l, ST))) else None
  /* Ref */        case tref(t1) =>
                     var optT1 := has_type(G, ST, t1);
                     if (optT1.Some?) then Some(TRef(optT1.get)) else None
  /* Deref */      case tderef(t1) =>
                     var optT1 := has_type(G, ST, t1);
                     if (optT1.Some? && optT1.get.TRef?) then Some(optT1.get.cellT) else None
  /* Assign */     case tassign(t1, t2) =>
                     var optT1 := has_type(G, ST, t1);
                     var optT2 := has_type(G, ST, t2);
                     if (optT1.Some? && optT2.Some? && optT1.get.TRef? && optT1.get.cellT == optT2.get) then Some(TUnit) else None
}

// ----------
// Properties
// ----------

// Well-Typed Stores
predicate store_well_typed(ST: store<ty>, st: store<tm>)
{
  |ST.m| == |st.m| &&
  (forall l:nat :: l < |st.m| ==> has_type(Context([]), ST, store_lookup(l, st)) == Some(store_lookup(l, ST)))
}

predicate store_extends<A>(st': store<A>, st: store<A>)
{
  |st.m|<=|st'.m| && forall l:nat :: l < |st.m| ==> st.m[l]==st'.m[l]
}

ghost method lemma_store_extends_lookup<A>(l: nat, st: store, st': store)
  requires l < |st.m|;
  requires store_extends(st', st);
  ensures store_lookup(l, st') == store_lookup(l, st);
{
}
ghost method lemma_length_extends(l: nat, st: store, st': store)
  requires l < |st.m|;
  requires store_extends(st', st);
  ensures l < |st'.m|;
{
}
ghost method lemma_store_extend_extends<A>(st: store<A>, t: A)
  ensures store_extends(store_extend(st, t), st);
{
}
ghost method lemma_store_invariance(G: context, ST: store<ty>, ST': store<ty>, t: tm, T: ty)
  requires store_extends(ST', ST);
  requires has_type(G, ST, t) == Some(T);
  ensures has_type(G, ST', t) == Some(T);
  decreases t;
{
  if (t.tabs?) {
    lemma_store_invariance(context_extend(G, t.x, t.T), ST, ST', t.body, T.returnT);
  } else if (t.tapp?) {
    var Tf :| has_type(G, ST, t.f) == Some(Tf);
    var Targ :| has_type(G, ST, t.arg) == Some(Targ);
    lemma_store_invariance(G, ST, ST', t.f, Tf);
    lemma_store_invariance(G, ST, ST', t.arg, Targ);
  } else if (t.tif0?) {
    lemma_store_invariance(G, ST, ST', t.c, TNat);
    lemma_store_invariance(G, ST, ST', t.a, T);
    lemma_store_invariance(G, ST, ST', t.b, T);
  } else if (t.tref?) {
    var Tv :| has_type(G, ST, t.v) == Some(Tv);
    lemma_store_invariance(G, ST, ST', t.v, Tv);
  } else if (t.tderef?) {
    var Tcell :| has_type(G, ST, t.cell) == Some(Tcell);
    lemma_store_invariance(G, ST, ST', t.cell, Tcell);
  } else if (t.tassign?) {
    var Tlhs :| has_type(G, ST, t.lhs) == Some(Tlhs);
    var Trhs :| has_type(G, ST, t.rhs) == Some(Trhs);
    lemma_store_invariance(G, ST, ST', t.lhs, Tlhs);
    lemma_store_invariance(G, ST, ST', t.rhs, Trhs);
  } else {
  }
}
ghost method lemma_store_extends_well_typed(ST: store<ty>, st: store<tm>, t: tm, T: ty)
  requires store_well_typed(ST, st);
  requires has_type(Context([]), ST, t) == Some(T);
  requires value(t);
  ensures store_well_typed(store_extend(ST, T), store_extend(st, t));
{
  assert |store_extend(ST, T).m| == |store_extend(st, t).m|;
  var ST' := store_extend(ST, T);
  var st' := store_extend(st, t);
  assert |st'.m| == |st.m|+1;
  parallel (l:nat | l < |st'.m|) ensures has_type(Context([]), ST', store_lookup(l, st')) == Some(store_lookup(l, ST'));
  {
    if (l == |st.m|) {
      assert store_lookup(l, st') == t;
      assert store_lookup(l, ST') == T;
      lemma_store_invariance(Context([]), ST, ST', t, T);
      assert has_type(Context([]), ST', store_lookup(l, st')) == Some(store_lookup(l, ST'));
    } else {
      assert l < |st.m|;
      assert has_type(Context([]), ST, store_lookup(l, st)) == Some(store_lookup(l, ST));
      assert store_lookup(l, st') == store_lookup(l, st);
      assert store_lookup(l, ST') == store_lookup(l, ST);
      lemma_store_invariance(Context([]), ST, ST', store_lookup(l, st), store_lookup(l, ST));
      assert has_type(Context([]), ST', store_lookup(l, st')) == Some(store_lookup(l, ST'));
    }
  }
}

// Preservation 
predicate preservation(ST: store<ty>, t: tm, t': tm, T: ty, st: store<tm>, st': store<tm>)
{
  (has_type(Context([]), ST, t)==Some(T) && store_well_typed(ST, st) && step(t, st) == Some(P(t', st'))) ==>
  (exists ST' :: store_extends(ST', ST) && has_type(Context([]), ST', t')==Some(T) && store_well_typed(ST', st'))
}

// Substitution Lemma

predicate appears_free_in(x: nat, t: tm)
{
  /* var */    (t.tvar? && t.id==x) ||
  /* app1 */   (t.tapp? && appears_free_in(x, t.f)) ||
  /* app2 */   (t.tapp? && appears_free_in(x, t.arg)) ||
  /* abs */    (t.tabs? && t.x!=x && appears_free_in(x, t.body)) ||
  /* succ */   (t.tsucc? && appears_free_in(x, t.pn)) ||
  /* pred */   (t.tpred? && appears_free_in(x, t.sn)) ||
  /* mult1 */  (t.tmult? && appears_free_in(x, t.n1)) ||
  /* mult2 */  (t.tmult? && appears_free_in(x, t.n2)) ||
  /* if0_1 */  (t.tif0? && appears_free_in(x, t.c)) ||
  /* if0_2 */  (t.tif0? && appears_free_in(x, t.a)) ||
  /* if0_3 */  (t.tif0? && appears_free_in(x, t.b)) ||
  /* ref */    (t.tref? && appears_free_in(x, t.v)) ||
  /* deref */  (t.tderef? && appears_free_in(x, t.cell)) ||
  /* assign1 */(t.tassign? && appears_free_in(x, t.lhs)) ||
  /* assign2 */(t.tassign? && appears_free_in(x, t.rhs))
}
predicate closed(t: tm)
{
  forall x: nat :: !appears_free_in(x, t)
}

ghost method lemma_free_in_context(x: nat, t: tm, G: context, ST: store<ty>)
  requires appears_free_in(x, t);
  requires has_type(G, ST, t).Some?;
  ensures context_lookup(G, x).Some?;
  ensures has_type(G, ST, t).Some?;
{
  if (t.tabs?) {
    assert t.x != x;
    lemma_free_in_context(x, t.body, context_extend(G, t.x, t.T), ST);
  }
}
ghost method corollary_typable_empty__closed(ST: store<ty>, t: tm)
  requires has_type(Context([]), ST, t).Some?;
  ensures closed(t);
{
  parallel (x: nat)
    ensures !appears_free_in(x, t);
  {
    if (appears_free_in(x, t)) {
      lemma_free_in_context(x, t, Context([]), ST);
      assert context_lookup(Context([]), x).Some?;
      assert false;
    }
    assert !appears_free_in(x, t);
  }
}
ghost method lemma_context_invariance(G: context, G': context, ST: store<ty>, t: tm, T: ty)
  requires has_type(G, ST, t) == Some(T);
  requires forall x:nat :: appears_free_in(x, t) ==> context_lookup(G, x) == context_lookup(G', x);
  ensures has_type(G', ST, t) == Some(T);
  decreases t;
{
  if (t.tabs?) {
    lemma_context_invariance(context_extend(G, t.x, t.T), context_extend(G', t.x, t.T), ST, t.body, T.returnT);
  } else if (t.tapp?) {
    var Tf :| has_type(G, ST, t.f) == Some(Tf);
    var Targ :| has_type(G, ST, t.arg) == Some(Targ);
    lemma_context_invariance(G, G', ST, t.f, Tf);
    lemma_context_invariance(G, G', ST, t.arg, Targ);
  } else if (t.tif0?) {
    lemma_context_invariance(G, G', ST, t.c, TNat);
    lemma_context_invariance(G, G', ST, t.a, T);
    lemma_context_invariance(G, G', ST, t.b, T);
  } else if (t.tref?) {
    var Tv :| has_type(G, ST, t.v) == Some(Tv);
    lemma_context_invariance(G, G', ST, t.v, Tv);
  } else if (t.tderef?) {
    var Tcell :| has_type(G, ST, t.cell) == Some(Tcell);
    lemma_context_invariance(G, G', ST, t.cell, Tcell);
  } else if (t.tassign?) {
    var Tlhs :| has_type(G, ST, t.lhs) == Some(Tlhs);
    var Trhs :| has_type(G, ST, t.rhs) == Some(Trhs);
    lemma_context_invariance(G, G', ST, t.lhs, Tlhs);
    lemma_context_invariance(G, G', ST, t.rhs, Trhs);
  } else {
  }
}
ghost method lemma_substitution_preserves_typing(G: context, ST: store<ty>, x: nat, s: tm, S: ty, t: tm, T: ty)
  requires has_type(Context([]), ST, s) == Some(S);
  requires has_type(context_extend(G, x, S), ST, t) == Some(T);
  ensures has_type(G, ST, subst(x, s, t)) == Some(T);
  decreases t;
{
  if (t.tvar?) {
    if (t.id==x) {
      corollary_typable_empty__closed(ST, s);
      lemma_context_invariance(Context([]), G, ST, s, S);
    }
  } else if (t.tabs?) {
    if (t.x==x) {
      lemma_context_invariance(context_extend(G, x, S), G, ST, t, T);
    } else {
      var c_px := context_extend(context_extend(G, x, S), t.x, t.T);
      var c_xp := context_extend(context_extend(G, t.x, t.T), x, S);
      var c_p := context_extend(G, t.x, t.T);
      lemma_context_invariance(c_px, c_xp, ST, t.body, T.returnT);
      lemma_substitution_preserves_typing(c_p, ST, x, s, S, t.body, T.returnT);
    }
  } else if (t.tapp?) {
    var Tf :| has_type(context_extend(G, x, S), ST, t.f) == Some(Tf);
    var Targ :| has_type(context_extend(G, x, S), ST, t.arg) == Some(Targ);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.f, Tf);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.arg, Targ);
  } else if (t.tif0?) {
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.c, TNat);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.a, T);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.b, T);
  } else if (t.tref?) {
    var Tv :| has_type(context_extend(G, x, S), ST, t.v) == Some(Tv);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.v, Tv);
  } else if (t.tderef?) {
    var Tcell :| has_type(context_extend(G, x, S), ST, t.cell) == Some(Tcell);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.cell, Tcell);
  } else if (t.tassign?) {
    var Tlhs :| has_type(context_extend(G, x, S), ST, t.lhs) == Some(Tlhs);
    var Trhs :| has_type(context_extend(G, x, S), ST, t.rhs) == Some(Trhs);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.lhs, Tlhs);
    lemma_substitution_preserves_typing(G, ST, x, s, S, t.rhs, Trhs);
  } else {
  }
}

// Assignment Preserves Store Typing
ghost method lemma_assign_pres_store_typing(ST: store<ty>, st: store<tm>, l: nat, t: tm)
  requires l < |st.m|;
  requires store_well_typed(ST, st);
  requires has_type(Context([]), ST, t) == Some(store_lookup(l, ST));
  ensures store_well_typed(ST, store_replace(l, t, st));
{
  assert |ST.m| == |st.m|;
  assert |ST.m| == |store_replace(l, t, st).m|;
}

ghost method theorem_preservation(ST: store<ty>, t: tm, t': tm, T: ty, st: store<tm>, st': store<tm>) returns (ST': store<ty>)
  requires has_type(Context([]), ST, t)==Some(T);
  requires store_well_typed(ST, st);
  requires step(t, st) == Some(P(t', st'));
  ensures store_extends(ST', ST);
  ensures has_type(Context([]), ST', t')==Some(T);
  ensures store_well_typed(ST', st');
{
  ST' := ST;
  /* AppAbs */     if (t.tapp? && t.f.tabs? && value(t.arg)) {
    assert t' == subst(t.f.x, t.arg, t.f.body);
    assert st' == st;
    var Tf :| has_type(Context([]), ST, t.f) == Some(Tf);
    lemma_substitution_preserves_typing(Context([]), ST, t.f.x, t.arg, Tf.paramT, t.f.body, Tf.returnT);
  }
  /* App1 */       else if (t.tapp? && step(t.f,st).Some?) {
    var Tf :| has_type(Context([]), ST, t.f) == Some(Tf);
    ST' := theorem_preservation(ST, t.f, step(t.f, st).get.fst, Tf, st, step(t.f, st).get.snd);
    var Targ :| has_type(Context([]), ST, t.arg) == Some(Targ);
    lemma_store_invariance(Context([]), ST, ST', t.arg, Targ);
  }
  /* App2 */       else if (t.tapp? && value(t.f) && step(t.arg,st).Some?) {
    var Targ :| has_type(Context([]), ST, t.arg) == Some(Targ);
    ST' := theorem_preservation(ST, t.arg, step(t.arg, st).get.fst, Targ, st, step(t.arg, st).get.snd);
    var Tf :| has_type(Context([]), ST, t.f) == Some(Tf);
    lemma_store_invariance(Context([]), ST, ST', t.f, Tf);
  }
  /* SuccNat */    else if (t.tsucc? && t.pn.tnat?) {}//then Some(P(tnat(t.pn.n+1),st))
  /* Succ */       else if (t.tsucc? && step(t.pn,st).Some?) {
    ST' := theorem_preservation(ST, t.pn, step(t.pn, st).get.fst, TNat, st, step(t.pn, st).get.snd);
  }
  /* PredNat */    else if (t.tpred? && t.sn.tnat?) {}//then Some(P(tnat(if (t.sn.n==0) then 0 else t.sn.n-1),st))
  /* Pred */       else if (t.tpred? && step(t.sn,st).Some?) {
    ST' := theorem_preservation(ST, t.sn, step(t.sn, st).get.fst, TNat, st, step(t.sn, st).get.snd);
  }
  /* MultNats */   else if (t.tmult? && t.n1.tnat? && t.n2.tnat?) {}//then Some(P(tnat(t.n1.n*t.n2.n),st))
  /* Mult1 */      else if (t.tmult? && step(t.n1, st).Some?) {
    ST' := theorem_preservation(ST, t.n1, step(t.n1, st).get.fst, TNat, st, step(t.n1, st).get.snd);
    lemma_store_invariance(Context([]), ST, ST', t.n2, TNat);
  }
  /* Mult2 */      else if (t.tmult? && value(t.n1) && step(t.n2, st).Some?) {
    ST' := theorem_preservation(ST, t.n2, step(t.n2, st).get.fst, TNat, st, step(t.n2, st).get.snd);
    lemma_store_invariance(Context([]), ST, ST', t.n1, TNat);
  }
  /* If0 */        else if (t.tif0? && step(t.c, st).Some?) {
    ST' := theorem_preservation(ST, t.c, step(t.c, st).get.fst, TNat, st, step(t.c, st).get.snd);
    lemma_store_invariance(Context([]), ST, ST', t.a, T);
    lemma_store_invariance(Context([]), ST, ST', t.b, T);
  }
  /* If0_Zero */   else if (t.tif0? && t.c.tnat? && t.c.n==0) {}//then Some(P(t.a, st))
  /* If0_NonZero */else if (t.tif0? && t.c.tnat? && t.c.n!=0) {}//then Some(P(t.b, st))
  /* RefValue */   else if (t.tref? && value(t.v)) {
    assert t' == tloc(|st.m|);
    assert st' == store_extend(st, t.v);
    var Tv :| has_type(Context([]), ST, t.v) == Some(Tv);
    ST' := store_extend(ST, Tv);
    lemma_store_invariance(Context([]), ST, ST', t.v, Tv);
    lemma_store_extends_well_typed(ST, st, t.v, Tv);
  }
  /* Ref */        else if (t.tref? && step(t.v, st).Some?) {
    var Tv :| has_type(Context([]), ST, t.v) == Some(Tv);
    ST' := theorem_preservation(ST, t.v, step(t.v, st).get.fst, Tv, st, step(t.v, st).get.snd);
  }
  /* DerefLoc */   else if (t.tderef? && t.cell.tloc? && t.cell.l < |st.m|) {}//then Some(P(store_lookup(t.cell.l, st), st))
  /* Deref */      else if (t.tderef? && step(t.cell, st).Some?) {
    var Tcell :| has_type(Context([]), ST, t.cell) == Some(Tcell);
    ST' := theorem_preservation(ST, t.cell, step(t.cell, st).get.fst, Tcell, st, step(t.cell, st).get.snd);
  }
  /* Assign */     else if (t.tassign? && t.lhs.tloc? && value(t.rhs) && t.lhs.l < |st.m|) {}//then Some(P(tunit, store_replace(t.lhs.l, t.rhs, st)))
  /* Assign1 */    else if (t.tassign? && step(t.lhs, st).Some?) {
    var Tlhs :| has_type(Context([]), ST, t.lhs) == Some(Tlhs);
    ST' := theorem_preservation(ST, t.lhs, step(t.lhs, st).get.fst, Tlhs, st, step(t.lhs, st).get.snd);
    var Trhs :| has_type(Context([]), ST, t.rhs) == Some(Trhs);
    lemma_store_invariance(Context([]), ST, ST', t.rhs, Trhs);
  }
  /* Assign2 */    else if (t.tassign? && value(t.lhs) && step(t.rhs, st).Some?) {
    var Trhs :| has_type(Context([]), ST, t.rhs) == Some(Trhs);
    ST' := theorem_preservation(ST, t.rhs, step(t.rhs, st).get.fst, Trhs, st, step(t.rhs, st).get.snd);
    var Tlhs :| has_type(Context([]), ST, t.lhs) == Some(Tlhs);
    lemma_store_invariance(Context([]), ST, ST', t.lhs, Tlhs);
  }
                   else {}
}

// Progress
ghost method theorem_progress(ST: store<ty>, t: tm, st: store<tm>)
  requires has_type(Context([]), ST, t).Some?;
  requires store_well_typed(ST, st);
  ensures value(t) || step(t, st).Some?;
{
}

// Type Soundness
predicate normal_form(t: tm, st: store<tm>)
{
  step(t, st).None?
}

predicate stuck(t: tm, st: store<tm>)
{
  normal_form(t, st) && !value(t)
}

ghost method corollary_soundness(ST: store<ty>, t: tm, t': tm, st: store<tm>, st': store<tm>, T: ty, n: nat)
  requires store_well_typed(ST, st);
  requires has_type(Context([]), ST, t) == Some(T);
  requires mstep(t, st, t', st', n);
  ensures !stuck(t', st');
  decreases n;
{
  theorem_progress(ST, t, st);
  if (t == t' && st == st') {
  } else {
   var ST' := theorem_preservation(ST, t, step(t, st).get.fst, T, st, step(t, st).get.snd);
   corollary_soundness(ST', step(t, st).get.fst, t', step(t, st).get.snd, st', T, n-1);
  }
}