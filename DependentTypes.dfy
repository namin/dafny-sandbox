// A solution to the CS2520R Fall 2024 assignment
// https://plti.metareflection.club/assignments.html
// on implementing a given semantic model of dependent types,
// designed to be (mostly) syntax-directed
// and to support (tediously) expressing and type-checking
// commutativity of addition.
// Disclaimer: ChatGPT helped develop this code,
// over a few messy sessions (which I can dig up upon request).
// HOWTO:
// Verify and run this code with:
// dafny /compile:3 /main:tests /out:my_output DependentTypes.dfy

datatype Expr =
    Var(string)                      // Variable reference
  | Type                             // The type of types (star)
  | Pi(string, Expr, Expr)           // Dependent function types (Pi types)
  | Lambda(string, Expr, Expr)       // Function introduction (lambda abstraction)
  | App(Expr, Expr)                  // Function elimination (application)
  | Nat                              // The natural number type
  | Zero                             // Natural number 0
  | Succ(Expr)                       // Successor of a natural number
  | ElimNat(Expr, Expr, Expr, Expr)  // Natural number elimination

datatype option<A> = None | Some(get: A)

// Function to compute free variables in an expression
function freeVars(e: Expr): set<string>
{
    match e
    case Var(x) => {x}
    case Type => {}
    case Pi(x, t1, t2) => freeVars(t1) + (freeVars(t2) - {x})
    case Lambda(x, t, body) => freeVars(t) + (freeVars(body) - {x})
    case App(e1, e2) => freeVars(e1) + freeVars(e2)
    case Nat => {}
    case Zero => {}
    case Succ(n) => freeVars(n)
    case ElimNat(e1, e2, e3, e4) => freeVars(e1) + freeVars(e2) + freeVars(e3) + freeVars(e4)
}

function freshVarIter(existingVars: set<string>, base: string, fuel: nat): string
    decreases fuel
{
    if fuel == 0 then
        base + "_fallback" // Return a fallback if fuel runs out
    else if base in existingVars then
        freshVarIter(existingVars, base + "'", fuel - 1)
    else
        base
}

function freshVar(existingVars: set<string>, base: string): string
{
    freshVarIter(existingVars, base, 1000)
}

function renameVar(e: Expr, oldName: string, newName: string): Expr
{
    match e
    case Var(y) =>
        if y == oldName then Var(newName) else e

    case Type => e

    case Pi(x, t1, t2) =>
        if x == oldName then
            Pi(x, renameVar(t1, oldName, newName), t2)
        else
            Pi(x, renameVar(t1, oldName, newName), renameVar(t2, oldName, newName))

    case Lambda(x, t, body) =>
        if x == oldName then
            Lambda(x, renameVar(t, oldName, newName), body)
        else
            Lambda(x, renameVar(t, oldName, newName), renameVar(body, oldName, newName))

    case App(e1, e2) =>
        App(renameVar(e1, oldName, newName), renameVar(e2, oldName, newName))

    case Nat => e
    case Zero => e
    case Succ(n) => Succ(renameVar(n, oldName, newName))

    case ElimNat(e1, e2, e3, e4) =>
        ElimNat(renameVar(e1, oldName, newName), renameVar(e2, oldName, newName), renameVar(e3, oldName, newName), renameVar(e4, oldName, newName))
}


lemma renamingPreservesSize(e: Expr, oldName: string, newName: string)
    ensures size(renameVar(e, oldName, newName)) == size(e)
    decreases size(e)
{
    match e
    case Var(_) => {}
    case Type => {}
    case Pi(_, t1, t2) =>
        renamingPreservesSize(t1, oldName, newName);
        renamingPreservesSize(t2, oldName, newName);
    case Lambda(_, t, body) =>
        renamingPreservesSize(t, oldName, newName);
        renamingPreservesSize(body, oldName, newName);
    case App(e1, e2) =>
        renamingPreservesSize(e1, oldName, newName);
        renamingPreservesSize(e2, oldName, newName);
    case Nat => {}
    case Zero => {}
    case Succ(n) =>
        renamingPreservesSize(n, oldName, newName);
    case ElimNat(e1, e2, e3, e4) =>
        renamingPreservesSize(e1, oldName, newName);
        renamingPreservesSize(e2, oldName, newName);
        renamingPreservesSize(e3, oldName, newName);
        renamingPreservesSize(e4, oldName, newName);
}

method subst(e1: Expr, x: string, e2: Expr) returns (res: Expr)
    decreases size(e1)
{
    match e1
    case Var(y) =>
        if y == x {
            res := e2;
        } else {
            res := e1;
        }

    case Type =>
        res := e1;

    case Pi(y, t1, t2) =>
        if x == y {
            res := e1;
        } else if y in freeVars(e2) {
            var fresh_y := freshVar(freeVars(t1) + freeVars(t2) + freeVars(e2), y);
            // Prove renaming doesn't change size
            renamingPreservesSize(t2, y, fresh_y);
            var subst_t1 := subst(t1, x, e2);
            var subst_t2 := subst(renameVar(t2, y, fresh_y), x, e2);
            res := Pi(fresh_y, subst_t1, subst_t2);
        } else {
            var subst_t1 := subst(t1, x, e2);
            var subst_t2 := subst(t2, x, e2);
            res := Pi(y, subst_t1, subst_t2);
        }

    case Lambda(y, t, body) =>
        if x == y {
            res := e1;
        } else if y in freeVars(e2) {
            var fresh_y := freshVar(freeVars(t) + freeVars(body) + freeVars(e2), y);
            // Prove renaming doesn't change size
            renamingPreservesSize(body, y, fresh_y);
            var subst_t := subst(t, x, e2);
            var subst_body := subst(renameVar(body, y, fresh_y), x, e2);
            res := Lambda(fresh_y, subst_t, subst_body);
        } else {
            var subst_t := subst(t, x, e2);
            var subst_body := subst(body, x, e2);
            res := Lambda(y, subst_t, subst_body);
        }

    case App(e3, e4) =>
        var subst_e3 := subst(e3, x, e2);
        var subst_e4 := subst(e4, x, e2);
        res := App(subst_e3, subst_e4);

    case Nat =>
        res := e1;

    case Zero =>
        res := e1;

    case Succ(n) =>
        var subst_n := subst(n, x, e2);
        res := Succ(subst_n);

    case ElimNat(e3, e4, e5, e6) =>
        var subst_e3 := subst(e3, x, e2);
        var subst_e4 := subst(e4, x, e2);
        var subst_e5 := subst(e5, x, e2);
        var subst_e6 := subst(e6, x, e2);
        res := ElimNat(subst_e3, subst_e4, subst_e5, subst_e6);
}

// Single-step reduction returning an option
method reduce(e: Expr) returns (res: option<Expr>)
    decreases size(e)
{
    match e
    case App(Lambda(x, _, body), e2) =>
        var subst_body := subst(body, x, e2);
        res := Some(subst_body);  // Beta reduction

    // Reduction for ElimNat at Zero and Succ
    case ElimNat(_, e1, _, Zero) =>
        res := Some(e1);

    case ElimNat(m, e1, e2, Succ(n)) =>
        var elim := ElimNat(m, e1, e2, n);
        res := Some(App(App(e2, n), elim));

    // Reduction inside Pi-types (domain or codomain)
    case Pi(x, t1, t2) => {
        var reduce_t1 := reduce(t1);
        match reduce_t1
        case Some(t1_r) =>
            res := Some(Pi(x, t1_r, t2));
        case None =>
            var reduce_t2 := reduce(t2);
            match reduce_t2
            case Some(t2_r) =>
                res := Some(Pi(x, t1, t2_r));
            case None =>
                res := None;
    }

    // Reduction inside Lambda (type or body)
    case Lambda(x, t, body) => {
        var reduce_t := reduce(t);
        match reduce_t
        case Some(t_r) =>
            res := Some(Lambda(x, t_r, body));
        case None =>
            var reduce_body := reduce(body);
            match reduce_body
            case Some(body_r) =>
                res := Some(Lambda(x, t, body_r));
            case None =>
                res := None;
    }

    // Reduction inside applications
    case App(e1, e2) => {
        var reduce_e1 := reduce(e1);
        match reduce_e1
        case Some(e1_r) =>
            res := Some(App(e1_r, e2));
        case None =>
            var reduce_e2 := reduce(e2);
            match reduce_e2
            case Some(e2_r) =>
                res := Some(App(e1, e2_r));
            case None =>
                res := None;
    }

    // Reduction inside ElimNat
    case ElimNat(e1, e2, e3, e4) => {
        var reduce_e1 := reduce(e1);
        match reduce_e1
        case Some(e1_r) =>
            res := Some(ElimNat(e1_r, e2, e3, e4));
        case None =>
            var reduce_e2 := reduce(e2);
            match reduce_e2
            case Some(e2_r) =>
                res := Some(ElimNat(e1, e2_r, e3, e4));
            case None =>
                var reduce_e3 := reduce(e3);
                match reduce_e3
                case Some(e3_r) =>
                    res := Some(ElimNat(e1, e2, e3_r, e4));
                case None =>
                    var reduce_e4 := reduce(e4);
                    match reduce_e4
                    case Some(e4_r) =>
                        res := Some(ElimNat(e1, e2, e3, e4_r));
                    case None =>
                        res := None;
    }

    // Reduction inside Succ
    case Succ(n) => {
        var reduce_n := reduce(n);
        match reduce_n
        case Some(n_r) =>
            res := Some(Succ(n_r));
        case None =>
            res := None;
    }

    // No reduction possible
    case _ =>
        res := None;
}

// Multi-step reduction with fuel limit
method multiStepReduce(e: Expr, fuel: nat) returns (res: Expr)
    decreases fuel
{
    if fuel == 0 {
        print "Warning: Fuel exhausted!\n";
        res := e;
    } else {
        var reduce_res := reduce(e);
        match reduce_res
        case None =>
            res := e;
        case Some(e_r) =>
            res := multiStepReduce(e_r, fuel - 1);
    }
}

// Function to compute the size of an expression (number of nodes in the AST)
function size(e: Expr): nat
{
    match e
    case Var(_) => 1
    case Type => 1
    case Pi(_, t1, t2) => 1 + size(t1) + size(t2)
    case Lambda(_, t, body) => 1 + size(t) + size(body)
    case App(e1, e2) => 1 + size(e1) + size(e2)
    case Nat => 1
    case Zero => 1
    case Succ(n) => 1 + size(n)
    case ElimNat(e1, e2, e3, e4) => 1 + size(e1) + size(e2) + size(e3) + size(e4)
}

// Helper method to canonicalize bound names in both expressions simultaneously
method freshCanonicalizeSimulataneously(e1: Expr, e2: Expr, existingVars: set<string>) returns (norm1: Expr, norm2: Expr)
    decreases size(e1) + size(e2)
{
    match (e1, e2)
    case (Var(x1), Var(x2)) =>
        // If both are free variables, check if they're the same
        norm1, norm2 := e1, e2;

    case (Type, Type) =>
        norm1, norm2 := e1, e2;

    case (Pi(x1, t1a, t1b), Pi(x2, t2a, t2b)) =>
        var freshX := freshVar(existingVars + {x1} + {x2} + freeVars(t1a) + freeVars(t2a), x1);
        var norm_t1a, norm_t2a := freshCanonicalizeSimulataneously(t1a, t2a, existingVars);

        renamingPreservesSize(t1b, x1, freshX);
        renamingPreservesSize(t2b, x2, freshX);

        var norm_t1b, norm_t2b := freshCanonicalizeSimulataneously(renameVar(t1b, x1, freshX), renameVar(t2b, x2, freshX), existingVars + {freshX});
        norm1 := Pi(freshX, norm_t1a, norm_t1b);
        norm2 := Pi(freshX, norm_t2a, norm_t2b);

    case (Lambda(x1, t1a, t1b), Lambda(x2, t2a, t2b)) =>
        var freshX := freshVar(existingVars + {x1} + {x2} + freeVars(t1a) + freeVars(t2a), x1);
        var norm_t1a, norm_t2a := freshCanonicalizeSimulataneously(t1a, t2a, existingVars);

        renamingPreservesSize(t1b, x1, freshX);
        renamingPreservesSize(t2b, x2, freshX);

        var norm_t1b, norm_t2b := freshCanonicalizeSimulataneously(renameVar(t1b, x1, freshX), renameVar(t2b, x2, freshX), existingVars + {freshX});
        norm1 := Lambda(freshX, norm_t1a, norm_t1b);
        norm2 := Lambda(freshX, norm_t2a, norm_t2b);

    case (App(e1a, e1b), App(e2a, e2b)) =>
        var norm_e1a, norm_e2a := freshCanonicalizeSimulataneously(e1a, e2a, existingVars);
        var norm_e1b, norm_e2b := freshCanonicalizeSimulataneously(e1b, e2b, existingVars);
        norm1 := App(norm_e1a, norm_e1b);
        norm2 := App(norm_e2a, norm_e2b);

    case (Nat, Nat) =>
        norm1, norm2 := e1, e2;

    case (Zero, Zero) =>
        norm1, norm2 := e1, e2;

    case (Succ(n1), Succ(n2)) =>
        var norm_n1, norm_n2 := freshCanonicalizeSimulataneously(n1, n2, existingVars);
        norm1 := Succ(norm_n1);
        norm2 := Succ(norm_n2);

    case (ElimNat(e1a, e1b, e1c, e1d), ElimNat(e2a, e2b, e2c, e2d)) =>
        var norm_e1a, norm_e2a := freshCanonicalizeSimulataneously(e1a, e2a, existingVars);
        var norm_e1b, norm_e2b := freshCanonicalizeSimulataneously(e1b, e2b, existingVars);
        var norm_e1c, norm_e2c := freshCanonicalizeSimulataneously(e1c, e2c, existingVars);
        var norm_e1d, norm_e2d := freshCanonicalizeSimulataneously(e1d, e2d, existingVars);
        norm1 := ElimNat(norm_e1a, norm_e1b, norm_e1c, norm_e1d);
        norm2 := ElimNat(norm_e2a, norm_e2b, norm_e2c, norm_e2d);

    case (_, _) =>
        norm1, norm2 := e1, e2;  // Default case, in case expressions differ
}

method alphaEquivalent(t1: Expr, t2: Expr) returns (res: bool)
    decreases size(t1) + size(t2)
{
    var combinedFreeVars := freeVars(t1) + freeVars(t2);

    var canonicalT1, canonicalT2 := freshCanonicalizeSimulataneously(t1, t2, combinedFreeVars);

    res := canonicalT1 == canonicalT2;
}


// Normalization as multi-step reduction with an arbitrary large fuel
method normalize(e: Expr) returns (res: Expr)
{
    res := multiStepReduce(e, 10000);
}

// Compare types, normalized and up to alpha-equivalence.
method equalTypes(t1: Expr, t2: Expr) returns (res: bool)
{
    var norm_t1 := normalize(t1);
    var norm_t2 := normalize(t2);
    res := alphaEquivalent(norm_t1, norm_t2);
}

// Infer the type of an expression, syntax-directed.
method inferType(Gamma: map<string, Expr>, e: Expr) returns (res: option<Expr>)
    decreases e
{
    match e
    case Var(x) =>
        if x in Gamma {
            res := Some(Gamma[x]);
        } else {
            res := None;
        }

    case Type =>
        res := Some(Type);

    case Pi(x, t1, t2) => {
        var ot1 := inferType(Gamma, t1);
        match ot1
        case Some(t1_type) =>
            var eq_t1 := equalTypes(t1_type, Type);
            if eq_t1 {
                var nt1 := t1;//normalize(t1);
                var Gamma_extended := Gamma[x := nt1];
                var ot2 := inferType(Gamma_extended, t2);
                match ot2
                case Some(t2_type) =>
                    var eq_t2 := equalTypes(t2_type, Type);
                    if eq_t2 {
                        res := Some(Type);
                    } else {
                        res := None;
                    }
                case None => res := None;
            } else {
                res := None;
            }
        case None => res := None;
    }

    case Lambda(x, t, body) => {
        var ot := inferType(Gamma, t);
        match ot
        case Some(t_type) =>
            var eq_t := equalTypes(t_type, Type);
            if eq_t {
                var nt := t;//normalize(t);
                var Gamma_extended := Gamma[x := nt];
                var obody := inferType(Gamma_extended, body);
                match obody
                case Some(body_type) =>
                    res := Some(Pi(x, t, body_type));
                case None => res := None;
            } else {
                res := None;
            }
        case None => res := None;
    }

    case App(e1, e2) => {
        var ot1 := inferType(Gamma, e1);
        match ot1
        case Some(t1) => {
            var nt1 := normalize(t1);
            match nt1
            case Pi(x, t1, t2) => {
                var ot2 := inferType(Gamma, e2);
                match ot2
                case Some(t1_actual) =>
                    var eq2 := equalTypes(t1, t1_actual);
                    if eq2 {
                        var subst_t2 := subst(t2, x, e2);
                        res := Some(subst_t2);
                    } else {
                        print "DEBUG (app case): arg doesn't have the expected type:\n";
                        print t1_actual;
                        print "\nvs\n";
                        print t1;
                        var nt1 := normalize(t1);
                        print nt1;
                        print "\n";
                        res := None;
                    }
                case None => {
                    print "DEBUG (app case): arg doesn't have an inferred type.\n";
                    print e2;
                    print "\n";
                    print ot2;
                    print "\n";
                    res := None;
                }
            }
            case _ => {
                print "DEBUG (app case): fun has an inferred type, but it's not a Pi.\n";
                print e1;
                print "\n";
                print nt1;
                print "\n";
                res := None;
            }
        }
        case _ => {
            print "DEBUG (app case): fun doesn't have an inferred type.\n";
            print e1;
            print "\n";
            print ot1;
            print "\n";
            res := None;
        }
    }

    case Nat =>
        res := Some(Type);

    case Zero =>
        res := Some(Nat);

    case Succ(n) => {
        var on := inferType(Gamma, n);
        match on
        case Some(n_type) =>
            var eq_nat := equalTypes(n_type, Nat);
            if eq_nat {
                res := Some(Nat);
            } else {
                res := None;
            }
        case None => res := None;
    }

    case ElimNat(m, e1, e2, e3) => {
        var om := inferType(Gamma, m);
        match om
        case Some(m_type) =>
            var eq_m := equalTypes(m_type, Pi("n", Nat, Type));
            if eq_m {
                var m_Zero := App(m, Zero);
                var oe1 := inferType(Gamma, e1);
                match oe1
                case Some(e1_type) =>
                    var eq1 := equalTypes(e1_type, m_Zero);
                    if eq1 {
                        var oe2 := inferType(Gamma, e2);
                        match oe2
                        case Some(e2_type) =>
                            var eq_e2 := equalTypes(e2_type, Pi("n", Nat, Pi("IH", App(m, Var("n")), App(m, Succ(Var("n"))))));
                            if eq_e2 {
                                var oe3 := inferType(Gamma, e3);
                                match oe3
                                case Some(e3_type) =>
                                    var eq_e3 := equalTypes(e3_type, Nat);
                                    if eq_e3 {
                                        res := Some(App(m, e3));
                                    } else {
                                        print "DEBUG: e3 doesn't have the expected type Nat:\n";
                                        print e3_type;
                                        print "\n";
                                        res := None;
                                    }
                                case None => {
                                    print "DEBUG: e3 doesn't have an inferred type.\n";
                                    res := None;
                                }
                            } else {
                                print "DEBUG: e2 doesn't have the expected type:\n";
                                print e2_type;
                                print "\n";
                                res := None;
                            }
                        case None => {
                            print "DEBUG: e2 doesn't have an inferred type.\n";
                            res := None;
                        }
                    } else {
                        print "DEBUG: e1 doesn't have the expected type:\n";
                        print e1_type;
                        print "\nvs\n";
                        var expected_e1_type := normalize(App(m, Zero));
                        print App(m, Zero);
                        print "\n";
                        print expected_e1_type;
                        print "\n";
                        res := None;
                    }
                case None => {
                    print "DEBUG: e1 doesn't have an inferred type.\n";
                    res := None;
                }
            } else {
                print "DEBUG: motive doesn't have the expected type:\n";
                print m_type;
                print "\n";
                res := None;
            }
        case None => {
            print "DEBUG: motive doesn't have an inferred type.\n";
            res := None;
        }
    }
}

// Check that an expression has an expected type.
method checkType(Gamma: map<string, Expr>, e: Expr, expected: Expr) returns (res: bool)
{
    var ot := inferType(Gamma, e);
    match ot
    case Some(inferred) => res := equalTypes(inferred, expected);
    case None => res := false;
}

method print_res(s: string, o: option<Expr>)
{
    print s;
    print "\n";
    match o {
        case Some(e) =>
            print e;
            print "\nNormalized:\n";
            var en := normalize(e);
            print en;
        case None =>
            print "(none)";
    }
    print "\n";
}

method tests() {
    var ok := true;

    print "Alpha-equivalence sanity checks";
    ok := alphaEquivalent(
        Lambda("x", Type, Lambda("y", Type, Var("y"))),
        Lambda("y", Type, Lambda("x", Type, Var("x")))
    );
    print ".";
    expect ok;
    ok := alphaEquivalent(
        Lambda("x", Type, Lambda("y", Type, Var("x"))),
        Lambda("y", Type, Lambda("x", Type, Var("y")))
    );
    print ".\n";
    expect ok;

    print "### Example 1: Polymorphic Identity Function\n";
    // id = λ(A: Type). λ(x: A). x
    var id := Lambda("A", Type, Lambda("x", Var("A"), Var("x")));

    // id's type: (A: Type) -> A -> A
    var id_type := Pi("A", Type, Pi("x", Var("A"), Var("A")));

    // Type check identity function
    var id_type_check := inferType(map[], id);
    print_res("Polymorphic Identity Function Type Check:", id_type_check);
    ok := checkType(map[], id, id_type);
    expect ok;

    print "\n### Example 2: Successor Function\n";
    // succ = λ(n: Nat). Succ(n)
    var succ_fn := Lambda("n", Nat, Succ(Var("n")));

    // succ's type: Nat -> Nat
    var succ_type := Pi("n", Nat, Nat);

    // Type check the successor function
    var succ_type_check := inferType(map[], succ_fn);
    print_res("Successor Function Type Check:", succ_type_check);
    ok := checkType(map[], succ_fn, succ_type);
    expect ok;

    print "\n### Example 3: Natural Number Elimination (add_one)\n";
    // Add one to a number using elimNat
    var add_one := Lambda("x", Nat, ElimNat(
        Lambda("n", Nat, Nat),  // Motive: Nat -> Nat
        Zero,                   // Base case: 0 -> 0
        Lambda("n", Nat, Lambda("IH", Nat, Succ(Var("IH")))), // Inductive case: n -> Succ(IH)
        Var("x")                // Target
    ));

    // add_one's type: Nat -> Nat
    var add_one_type := Pi("n", Nat, Nat);

    // Type check the add_one function
    var add_one_type_check := inferType(map[], add_one);
    print_res("Add One Function Type Check:", add_one_type_check);
    ok := checkType(map[], add_one, add_one_type);
    expect ok;

    print "\n### Example 4: Application of Identity Function\n";
    var app_id := App(App(id, Nat), Zero);

    // Type check the application
    var app_id_type_check := inferType(map[], app_id);
    print_res("Application of Identity Function Type Check:", app_id_type_check);
    ok := checkType(map[], app_id, Nat);
    expect ok;

    // Normalize the expression
    var app_id_normalized := normalize(app_id);
    print "Application of Identity Function Normalized: ";
    print app_id_normalized;
    print "\n";
    expect app_id_normalized == Zero;

    print "\n### Example 5: Recursive Addition Function\n";
    // Define the addition function using ElimNat
    var add := Lambda("x", Nat, Lambda("y", Nat, ElimNat(
        Lambda("n", Nat, Nat),   // Motive: Nat -> Nat
        Var("y"),                // Base case: x + 0 = x
        Lambda("n", Nat, Lambda("IH", Nat, Succ(Var("IH")))), // Inductive case: x + suc(n) = suc(x + n)
        Var("x")                 // Target: perform the addition on x
    )));

    // add's type: Nat -> Nat -> Nat
    var add_type := Pi("x", Nat, Pi("y", Nat, Nat));

    // Type check the addition function
    var add_type_check := inferType(map[], add);
    print_res("Addition Function Type Check:", add_type_check);
    ok := checkType(map[], add, add_type);
    expect ok;

    // Test addition (2 + 3) = 5
    var two := Succ(Succ(Zero));  // 2
    var three := Succ(Succ(Succ(Zero)));  // 3
    var add_two_three := App(App(add, two), three);  // add(2, 3)

    // Type check the addition application
    var add_two_three_type_check := inferType(map[], add_two_three);
    print_res("Addition of 2 and 3 Type Check:", add_two_three_type_check);
    ok := checkType(map[], add_two_three, Nat);
    expect ok;

    // Normalize the addition expression (expect 5)
    var add_two_three_normalized := normalize(add_two_three);
    print "Addition of 2 and 3 Normalized: ";
    print add_two_three_normalized;
    print "\n";
    expect add_two_three_normalized == Succ(Succ(Succ(Succ(Succ(Zero)))));  // Expect 5

    print "\n### Example 6: Plus commutative\n";

    var Gamma := map[];

    //Same : (A : ⋆) → A → A → ⋆
    var Same_type := Pi("A", Type, Pi("a", Var("A"), Pi("b", Var("A"), Type)));
    //Same A a b = (P : A → ⋆) → P a → P b
    var Same := Lambda("A", Type, Lambda("a", Var("A"), Lambda("b", Var("A"),
            Pi("P", Pi("_", Var("A"), Type), Pi("_", App(Var("P"), Var("a")), App(Var("P"), Var("b")))))));
    var Same_type_check := inferType(Gamma, Same);
    print_res("Same Type Check:", Same_type_check);
    ok := checkType(Gamma, Same, Same_type);
    expect ok;

    //refl : (A : ⋆) → (x : A) → Same A x x
    var refl_type := Pi("A", Type, Pi("x", Var("A"), App(App(App(Same, Var("A")), Var("x")), Var("x"))));
    //refl = λ A x P z → z
    var refl := Lambda("A", Type, Lambda("x", Var("A"),
        Lambda("P", Pi("_", Var("A"), Type), Lambda("z", App(Var("P"), Var("x")), Var("z")))));
    var refl_type_check := inferType(Gamma, refl);
    print_res("refl Type Check:", refl_type_check);
    ok := checkType(Gamma, refl, refl_type);
    expect ok;

    //sym : (A : ⋆) → (x y : A) → Same A x y → Same A y x
    var sym_type := Pi("A", Type,
                    Pi("x", Var("A"), Pi("y", Var("A"),
                    Pi("z", App(App(App(Same, Var("A")), Var("x")), Var("y")),
                    App(App(App(Same, Var("A")), Var("y")), Var("x"))))));
    //sym = λ A x y z P → z (λ z₁ → (x₁ : P z₁) → P x) (λ x₁ → x₁)
    var sym := Lambda("A", Type, Lambda("x", Var("A"), Lambda("y", Var("A"),
            Lambda("z", App(App(App(Same, Var("A")), Var("x")), Var("y")),
            Lambda("P", Pi("_", Var("A"), Type),
            App(App(Var("z"), Lambda("z1", Var("A"), Pi("x1", App(Var("P"), Var("z1")), App(Var("P"), Var("x"))))),
                Lambda("x1", App(Var("P"), Var("x")), Var("x1"))))))));
    var sym_type_check := inferType(Gamma, sym);
    print_res("sym Type Check:", sym_type_check);
    ok := checkType(Gamma, sym, sym_type);
    expect ok;

    //trans : (A : ⋆) → (x y z : A) → Same A x y → Same A y z → Same A x z
    var trans_type := Pi("A", Type,
                        Pi("x", Var("A"),
                        Pi("y", Var("A"),
                        Pi("z", Var("A"),
                        Pi("pxy", App(App(App(Same, Var("A")), Var("x")), Var("y")),
                        Pi("pyz", App(App(App(Same, Var("A")), Var("y")), Var("z")),
                        App(App(App(Same, Var("A")), Var("x")), Var("z"))))))));
    //trans A x y z pxy pyz P px = pyz P (pxy P px)
    var trans := Lambda("A", Type,
                Lambda("x", Var("A"),
                Lambda("y", Var("A"),
                Lambda("z", Var("A"),
                Lambda("pxy", App(App(App(Same, Var("A")), Var("x")), Var("y")),
                Lambda("pyz", App(App(App(Same, Var("A")), Var("y")), Var("z")),
                Lambda("P", Pi("_", Var("A"), Type),
                Lambda("px", App(Var("P"), Var("x")),
                    App(App(Var("pyz"), Var("P")), App(App(Var("pxy"), Var("P")), Var("px")))
                ))))))));
    var trans_type_check := inferType(map[], trans);
    print_res("trans Type Check:", trans_type_check);
    ok := checkType(map[], trans, trans_type);
    expect ok;

    //same_under_suc : (x y : ℕ) → Same ℕ x y → Same ℕ (suc x) (suc y)
    var same_under_suc_type := Pi("x", Nat,
                                Pi("y", Nat,
                                Pi("z", App(App(App(Same, Nat), Var("x")), Var("y")),
                                App(App(App(Same, Nat), Succ(Var("x"))), Succ(Var("y"))))));
    //same_under_suc = λ x y z P → z (λ z₁ → P (suc z₁))
    var same_under_suc := Lambda("x", Nat,
                        Lambda("y", Nat,
                        Lambda("z", App(App(App(Same, Nat), Var("x")), Var("y")),
                        Lambda("P", Pi("_", Nat, Type),
                        App(Var("z"), Lambda("z1", Nat, App(Var("P"), Succ(Var("z1")))))))));
    var same_under_suc_type_check := inferType(map[], same_under_suc);
    print_res("same_under_suc Type Check:", same_under_suc_type_check);
    ok := checkType(map[], same_under_suc, same_under_suc_type);
    expect ok;

    //plus_right_zero : (x : ℕ) → Same ℕ x (x + 0)
    var plus_right_zero_type := Pi("x", Nat, App(App(App(Same, Nat), Var("x")), App(App(add, Var("x")), Zero)));
    //plus_right_zero x = natElim (λ x → Same ℕ x (x + 0))
    //                            (λ P x → x)
    //                            (λ n x₁ P → x₁ (λ z → P (suc z)))
    //                            x
    var motive := Lambda("n", Nat, App(App(App(Same, Nat), Var("n")), App(App(add, Var("n")), Zero)));
    var motive_type_check := inferType(Gamma, motive);
    print_res("Motive Type Check:", motive_type_check);
    var base_case := Lambda("P", Pi("_", Nat, Type), Lambda("x", App(Var("P"), Zero), Var("x")));
    var base_case_type_check := inferType(Gamma, base_case);
    print_res("Base Case Type Check:", base_case_type_check);
    var inductive_case := Lambda("n", Nat,
                        Lambda("IH", App(App(App(Same, Nat), Var("n")), App(App(add, Var("n")), Zero)),
                            Lambda("P", Pi("_", Nat, Type),
                            App(Var("IH"), Lambda("z", Nat, App(Var("P"), Succ(Var("z"))))))));
    var inductive_case_type_check := inferType(Gamma, inductive_case);
    print_res("Inductive Case Type Check:", inductive_case_type_check);
    var plus_right_zero := Lambda("x", Nat,
        ElimNat(motive,  // Motive
                base_case,  // Base case
                inductive_case,  // Inductive case
                Var("x")));
    var plus_right_zero_type_check := inferType(Gamma, plus_right_zero);
    print_res("plus_right_zero Type Check:", plus_right_zero_type_check);
    ok := checkType(Gamma, plus_right_zero, plus_right_zero_type);
    expect ok;

    //plus_right_suc : (x y : ℕ) → Same ℕ (suc (x + y)) (x + suc y)
    //plus_right_suc x y = natElim (λ x → Same ℕ  (suc (x + y)) (x + suc y))
    //                             (λ P z → z)
    //                             (λ n z P → z (λ z₁ → P (suc z₁)))

    var plus_right_suc_motive := Lambda("x", Nat,
        App(App(App(Same, Nat), Succ(App(App(add, Var("x")), Var("y")))), App(App(add, Var("x")), Succ(Var("y")))));
    var plus_right_suc_base_case := Lambda("P", Pi("_", Nat, Type), Lambda("z",
        App(Var("P"), Succ(Var("y"))),
        Var("z")));
    var plus_right_suc_inductive_case := Lambda("n", Nat,
        Lambda("IH", App(App(App(Same, Nat), Succ(App(App(add, Var("n")), Var("y")))), App(App(add, Var("n")), Succ(Var("y")))),
        Lambda("P", Pi("_", Nat, Type),
        App(Var("IH"), Lambda("z", Nat, App(Var("P"), Succ(Var("z"))))))));
    var plus_right_suc := Lambda("x", Nat,
        Lambda("y", Nat,
        ElimNat(plus_right_suc_motive, plus_right_suc_base_case, plus_right_suc_inductive_case, Var("x"))));

    var plus_right_suc_motive_type_check := inferType(map["y":=Nat], plus_right_suc_motive);
    print_res("plus_right_suc Motive Type Check:", plus_right_suc_motive_type_check);

    var plus_right_suc_base_case_type_check := inferType(map["y":=Nat], plus_right_suc_base_case);
    print_res("plus_right_suc Base Case Type Check:", plus_right_suc_base_case_type_check);

    var plus_right_suc_inductive_case_type_check := inferType(map["y":=Nat], plus_right_suc_inductive_case);
    print_res("plus_right_suc Inductive Case Type Check:", plus_right_suc_inductive_case_type_check);

    var plus_right_suc_type_check := inferType(map[], plus_right_suc);
    print_res("plus_right_suc Type Check:", plus_right_suc_type_check);

    //plus_comm : (x y : ℕ) → Same ℕ (x + y) (y + x)
    var plus_comm_type := Pi("x", Nat, Pi("y", Nat, App(App(App(Same, Nat), App(App(add, Var("x")), Var("y"))), App(App(add, Var("y")), Var("x")))));
    //plus_comm x y = natElim (λ x → Same ℕ (x + y) (y + x))
    //                        (plus_right_zero y)
    //                        (λ n p → trans ℕ (suc (n + y))
    //                                         (suc (y + n))
    //                                         (y + suc n)
    //                                         (same_under_suc (n + y) (y + n) p)
    //                                         (plus_right_suc y n))
    /*
    plus_comm : (x y : ℕ) → Same ℕ (x + y) (y + x)
    plus_comm x y = natElim (λ (x : ℕ) → Same ℕ (x + y) (y + x))
                            (plus_right_zero y)
                            (λ (n : ℕ) (p : Same ℕ (n + y) (y + n)) →
                            trans ℕ (suc (n + y))
                                    (suc (y + n))
                                    (y + suc n)
                                    (same_under_suc (n + y) (y + n) p)
                                    (plus_right_suc y n))
                            x
    */
    var plus_comm_motive := Lambda("x", Nat, App(App(App(Same, Nat), App(App(add, Var("x")), Var("y"))), App(App(add, Var("y")), Var("x"))));
    var plus_comm_base_case := App(plus_right_zero, Var("y"));
    var plus_comm_inductive_case := Lambda("n", Nat,
        Lambda("p", App(App(App(Same, Nat), App(App(add, Var("n")), Var("y"))), App(App(add, Var("y")), Var("n"))),
        App(App(App(App(App(App(
            trans, Nat),  // Type for trans function
            Succ(App(App(add, Var("n")), Var("y")))),  // first expression succ(n + y)
            Succ(App(App(add, Var("y")), Var("n")))),  // second expression succ(y + n)
            App(App(add, Var("y")), Succ(Var("n")))),  // third expression y + succ(n)
            App(App(App(same_under_suc, App(App(add, Var("n")), Var("y"))), App(App(add, Var("y")), Var("n"))), Var("p"))),
            App(App(plus_right_suc, Var("y")), Var("n")))));
    var plus_comm := Lambda("x", Nat,
        Lambda("y", Nat,
        ElimNat(plus_comm_motive, plus_comm_base_case, plus_comm_inductive_case, Var("x"))));
    var plus_comm_motive_type_check := inferType(map["y":=Nat], plus_comm_motive);
    print_res("plus_comm Motive Type Check:", plus_comm_motive_type_check);

    var plus_comm_base_case_type_check := inferType(map["y":=Nat], plus_comm_base_case);
    print_res("plus_comm Base Case Type Check:", plus_comm_base_case_type_check);

    var plus_comm_inductive_case_type_check := inferType(map["y":=Nat], plus_comm_inductive_case);
    print_res("plus_comm Inductive Case Type Check:", plus_comm_inductive_case_type_check);

    var plus_comm_type_check := inferType(map[], plus_comm);
    print_res("plus_comm Type Check:", plus_comm_type_check);
    ok := checkType(Gamma, plus_comm, plus_comm_type);
    expect ok;
}


