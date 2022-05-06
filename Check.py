from Core import *
"""
Typechecker for MLTT.

===== Core Components =====
Π   Pi types
λ   Functions
@   Application
Σ   Sigma types
(,) Pairs             (, (x => ty2) tm1 tm2)
fst First projection
snd Second projection

0   Empty
1   Unit
2   Bool
... intro and elim rules

Nat Natural numbers
... recursion

U   Universe (Currently spartan McBride style)

===== HOTT Syntax =====
The (*tys, *left, *right, *eqs) cuple stands for a identity telescope.

("Id", ("Bind", *vars, ty), *tys, *left, *right, *eqs, l, r)

("ap", ("Bind", *vars, tm), *tys, *left, *right, *eqs)
"""

def tele(tylreqs):
    l = len(tylreqs)//4
    return tylreqs[:l], tylreqs[l:2*l], tylreqs[2*l:3*l], tylreqs[3*l:]

def fun(a, b):
    return ("Π", a, ("Bind", "_", b))

def pr(a, b):
    return ("Σ", a, ("Bind", "_", b))

def refl(tm):
    return ("ap", ("Bind", tm))

def Id(ty, tm1, tm2):
    return ("Id", ("Bind", ty), tm1, tm2)

def isContr(A):
    return subst(("Σ", ("Var", "isContr_A"), ("Bind", "_x",
        ("Π", ("Var", "isContr_A"), ("Bind", "_y",
            Id(("Var", "isContr_A"), ("Var", "_x"), ("Var", "_y")))))),
        {"isContr_A" : A})

def OneOneCorr(A, B):
    vA = ("Var", "Corr_A")
    vB = ("Var", "Corr_B")
    return subst(("Σ", fun(vA, fun(vB, ("U",))), ("Bind", "_R",
        pr(
            ("Π", vA, ("Bind", "_a", isContr(("Σ", vB, ("Bind", "_b", ("@", ("@", ("Var", "_R"), ("Var", "_a")), ("Var", "_b"))))))),
            ("Π", vB, ("Bind", "_b", isContr(("Σ", vA, ("Bind", "_a", ("@", ("@", ("Var", "_R"), ("Var", "_a")), ("Var", "_b")))))))
        ))),
        {"Corr_A" : A, "Corr_B" : B})

def rewrite(tm):
    match tm:
        case ("@", ("λ", _, ("Bind", x, body)), arg):
            return subst(body, {x:arg})
        case ("fst", (",", _, tm1, _)):
            return tm1
        case ("snd", (",", _, _, tm2)):
            return tm2
        case ("Id", ("Bind", *vars, ty), *scope, lhs, rhs):
            tys, left, right, eqs = tele(scope)
            fv = freevar(ty)  # First try to redact the last free variable.
            if len(vars) > 0 and vars[-1] not in fv:
                return ("Id", ("Bind", *vars[:-1], ty),
                    *tys[:-1],
                    *left[:-1],
                    *right[:-1],
                    *eqs[:-1],
                    lhs, rhs)
            match ty:  # Next proceed by cases.
                case ("Var", v):
                    return  # TODO We need to wait until we get the up and downs ready.
                case ("Σ", dom, ("Bind", x, cod)):
                    return ("Σ",
                        ("Id", ("Bind", *vars, dom),
                            *scope, ("fst", lhs), ("fst", rhs)),
                        ("Bind", x,
                            ("Id", ("Bind", *vars, x, cod),
                                *tys,    dom,
                                *left,   ("fst", lhs),
                                *right,  ("fst", rhs),
                                *eqs,    ("Var", x),
                                ("snd", lhs), ("snd", rhs))))
        case ("ap", ("Bind", *vars, tm), *scope):
            tys, left, right, eqs = tele(scope)
            pass

def normalize_(tm):
    touched = False
    tmr = []
    for sub in tm:
        if isinstance(sub, tuple):
            subr, t = normalize_(sub)
            tmr.append(subr)
            touched = touched or t
        else:
            tmr.append(sub)
    tm = tuple(tmr)

    tmr = rewrite(tm)
    if tmr is None:
        if touched:
            return normalize_(tm)[0], True
        return tm, False
    return normalize_(tmr)[0], True

def normalize(tm):
    return normalize_(tm)[0]

def conv(tm1, tm2, ty):
    # Checks whether tm1 <=> tm2.
    if tm1 == tm2: return
    match ty := normalize(ty):
        case ("U",):
            match tm1 := normalize(tm1), tm2 := normalize(tm2):
                case ("Π", dom1, ("Bind", x1, cod1)),\
                    ("Π", dom2, ("Bind", x2, cod2)):
                    conv(dom1, dom2, ("U",))
                    conv(cod1, subst(cod2,{x2:("Var",x1)}), ("U",))
                case ("Σ", dom1, ("Bind", x1, cod1)),\
                    ("Σ", dom2, ("Bind", x2, cod2)):
                    conv(dom1, dom2, ("U",))
                    conv(cod1, subst(cod2,{x2:("Var",x1)}), ("U",))
                case _:
                    raise ValueError("Type mismatch.", pretty(tm1), pretty(tm2))
        case ("Π", _, ("Bind", x, cod)):
            conv(normalize(("@",tm1,("Var",x))),
                normalize(("@",tm2,("Var",x))), cod)
        case ("Σ", dom, ("Bind", x, cod)):
            nfsttm1 = normalize(("fst", tm1))
            conv(nfsttm1,
                normalize(("fst", tm2)), dom)
            conv(normalize(("snd", tm1)),
                normalize(("snd", tm2)), subst(cod, {x:nfsttm1}))
        case ("cons", ("0" | "1")):
            return
        case _:
            raise ValueError("Unexpected type: " + pretty(ty))

def ensureΠΣ(con, ty):
    """
    Ensures that the type is a function type or a dependent pair.
    Returns (dom, x, cod).
    """
    match ty := normalize(ty):
        case (c, dom, ("Bind", x, cod)) if c == con:
            return dom, x, cod
        case _:
            raise ValueError(f"Not a {con} type.", pretty(ty))

# Global constants.
constants = dict()
constants["0"] = ("U",)
constants["absurd"] = ("Π", ("0",), ("Bind", "_",
    ("Π", ("U",), ("Bind", "T", ("Var", "T")))))
constants["1"] = ("U",)
constants["*"] = ("con", "1")

def infer(ctx, tm):
    match tm:
        case ("Var", x):
            return ctx[x]
        case ("Bind", *_):
            raise ValueError("Unexpected Bind.")
        case (("Π" | "Σ"), dom, ("Bind", x, body)):
            tydom = infer(ctx, dom)
            conv(tydom, ("U",), ("U",))
            temp = ctx[x] if x in ctx else None
            ctx[x] = dom
            ty = infer(ctx, body)
            conv(ty, ("U",), ("U",))
            if temp is not None:
                ctx[x] = temp
            else:
                del ctx[x]
            return ("U",)
        case ("λ", dom, ("Bind", x, body)):
            tydom = infer(ctx, dom)
            conv(tydom, ("U",), ("U",))
            temp = ctx[x] if x in ctx else None
            ctx[x] = dom
            ty = infer(ctx, body)
            if temp is not None:
                ctx[x] = temp
            else:
                del ctx[x]
            return ("Π", dom, ("Bind", x, ty))
        case ("@", fun, arg):
            funty = infer(ctx, fun)
            dom, x, cod = ensureΠΣ("Π", funty)
            argty = infer(ctx, arg)
            conv(argty, dom, ("U",))
            return subst(cod, {x:arg})
        case (",", ("Bind", x, tyx2), tm1, tm2):
            ty1 = infer(ctx, tm1)
            ty2 = infer(ctx, tm2)
            temp = ctx[x] if x in ctx else None
            ctx[x] = ty1
            tytyx2 = infer(ctx, tyx2)
            conv(tytyx2, ("U",), ("U",))
            if temp is not None:
                ctx[x] = temp
            else:
                del ctx[x]
            conv(ty2, subst(tyx2, {x:tm1}), ("U",))
            return ("Σ", ty1, ("Bind", x, tyx2))
        case ("fst", pair):
            pairty = infer(ctx, pair)
            dom, _, _ = ensureΠΣ("Σ", pairty)
            return dom
        case ("snd", pair):
            pairty = infer(ctx, pair)
            _, x, cod = ensureΠΣ("Σ", pairty)
            return subst(cod, {x:("fst", pair)})
        case ("con", con):
            return constants[con]
        case ("U",):
            return ("U",)
        case ("ap", ("Bind", *vars, arg), *lreqs):
            tys, left, right, eqs =\
                lreqs[0:len(vars)], lreqs[len(vars):len(vars)*2],\
                lreqs[len(vars)*2:len(vars)*3], lreqs[len(vars)*3:]
            temp_ctx = dict()
            for i,v in enumerate(vars):
                temp_ctx[v] = ctx[v] if v in ctx else None
                ctx[v] = tys[i]
            C = infer(ctx, arg)
            for v in temp_ctx:
                if temp_ctx[v] is not None:
                    ctx[v] = temp_ctx[v]
                else:
                    del ctx[v]
            for i in range(len(vars)):
                tyeqi = infer(ctx, eqs[i])
                tyexp = ("Id", tys[i], *left[:i], *right[:i], *eqs[:i], left[i], right[i])
                conv(tyeqi, tyexp, ("U",))
            return ("Id", ("Bind", *vars, C), *lreqs,
                subst(arg, {vars[i]:left[i] for i in range(len(vars))}),
                subst(arg, {vars[i]:right[i] for i in range(len(vars))}))
        case ("Id", ("Bind", *vars, arg), *lreqs, LHS, RHS):
            tys, left, right, eqs =\
                lreqs[0:len(vars)], lreqs[len(vars):len(vars)*2],\
                lreqs[len(vars)*2:len(vars)*3], lreqs[len(vars)*3:]
            temp_ctx = dict()
            for i,v in enumerate(vars):
                temp_ctx[v] = ctx[v] if v in ctx else None
                ctx[v] = tys[i]
            U = infer(ctx, arg)
            conv(U, ("U",), ("U",))
            for v in temp_ctx:
                if temp_ctx[v] is not None:
                    ctx[v] = temp_ctx[v]
                else:
                    del ctx[v]
            for i in range(len(vars)):
                tyeqi = infer(ctx, eqs[i])
                tyexp = ("Id", tys[i], *left[:i], *right[:i], *eqs[:i], left[i], right[i])
                conv(tyeqi, tyexp, ("U",))
            tLHS = infer(ctx, LHS)
            conv(tLHS, subst(arg, {vars[i]:left[i] for i in range(len(vars))}), ("U",))
            tRHS = infer(ctx, RHS)
            conv(tRHS, subst(arg, {vars[i]:right[i] for i in range(len(vars))}), ("U",))
            return ("U",)
        case _:
            raise ValueError("Unexpected term: " + pretty(tm))

if __name__ == "__main__":
    Idty = ("λ", ("U",), ("Bind", "t",
        ("λ", ("Var", "t"), ("Bind", "x",
        ("Var", "x")))))
    print(pretty(Idty))
    TId = infer({}, Idty)
    print(pretty(TId))
    IdId = ("@", ("@", Idty, TId), Idty)
    TIdId = infer({}, IdId)
    print(pretty(TIdId))
    nIdId = normalize(IdId)
    print(pretty(nIdId))

    Pointed = ("Σ", ("U",), ("Bind", "t", ("Var", "t")))
    pointed = ("λ", ("U",), ("Bind", "t",
        ("λ", ("Var", "t"), ("Bind", "x",
            (",", ("Bind", "t'", ("Var", "t'")), ("Var", "t"), ("Var", "x"))))))
    Tpointedtest = ("Π", ("U",), ("Bind", "T",
        ("Π", ("Var", "T"), ("Bind", "_", Pointed))))
    print(pretty(pointed))
    Tpointed = infer({}, pointed)
    print(pretty(Tpointed))
    print(pretty(Tpointedtest))
    conv(Tpointed, Tpointedtest, ("U",))

    # λ(T : U) (S : ∏(_:T) => U) => ∑(t : T) => S(t)
    Pair = ("λ", ("U",), ("Bind", "T",
        ("λ", ("Π", ("Var", "T"), ("Bind", "_", ("U",))), ("Bind", "S",
        ("Σ", ("Var", "T"), ("Bind", "t",
        ("@", ("Var", "S"), ("Var", "t"))))))))
    print(pretty(Pair))
    print(pretty(infer({}, Pair)))

    # ∏(T : U) (S : ∏(_:T) => U) (p : ∑(t : T) => S(t))
    #   => T
    fst = ("λ", ("U",), ("Bind", "T",
        ("λ", ("Π", ("Var", "T"), ("Bind", "_", ("U",))), ("Bind", "S",
        ("λ", ("Σ", ("Var", "T"), ("Bind", "t",
            ("@", ("Var", "S"), ("Var", "t")))), ("Bind", "p",
        ("fst", ("Var", "p"))))))))
    print(pretty(fst))
    print(pretty(infer({}, fst)))

    corr = OneOneCorr(("Var", "A"), ("Var", "A"))
    print(pretty(corr))
    print(pretty(infer({'A': ("U",)}, corr)))

    rf = refl(("Var", "a"))
    print(pretty(rf))
    print(pretty(infer({'A': ("U",), 'a': ("Var", "A")}, rf)))

    prf = (",", ("Bind", "_",
        ("Id", ("Bind", ("Var", "B")),
        ("Var", "b"), ("Var", "b"))),
        refl(("Var", "a")), refl(("Var", "b")))
    print(pretty(prf))
    typrf = infer({'A': ("U",), 'B': ("U",), 'a': ("Var", "A"), 'b': ("Var", "B")}, prf)
    print(pretty(typrf))
    conv(typrf, ("Id",
        ("Bind", ("Σ", ("Var", "A"), ("Bind", "_u",
            ("Var", "B")))),
            (",", ("Bind", "_v", ("Var", "B")), ("Var", "a"), ("Var", "b")),
            (",", ("Bind", "_w", ("Var", "B")), ("Var", "a"), ("Var", "b"))), ("U",))
