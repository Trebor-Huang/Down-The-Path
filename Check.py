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
("ap", ("Bind", *vars, tm), *tys, *left, *right, *eqs)
    Transport. *tys is a sort of telescope.
"""

def untelescope(vars, tys):
    for n, ty in enumerate(tys):
        match ty:
            case ("Bind", *varn, body):
                yield subst(body, {varn[i]:("Var", vars[i]) for i in range(n)})
            case _:
                raise Exception("Expected telescope, got {}".format(ty))

def fun(a, b):
    return ("Π", a, ("Bind", "_", b))

def pr(a, b):
    return ("Σ", a, ("Bind", "_", b))

def refl(tm):
    return ("ap", ("Bind", tm))

def Id(ty, tm1, tm2):
    return ("@", ("fst", refl(ty)), (",", ("Bind", "_", ty), tm1, tm2))

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

def normalize(tm):
    match tm:
        case ("@", fun, arg):
            match normalize(fun):
                case ("λ", _, ("Bind", x, body)):
                    return normalize(subst(body, {x:arg}))
                case nfun:
                    return ("@", nfun, normalize(arg))
        case ("fst", pair):
            match normalize(pair):
                case (",", _, tm1, _):
                    return tm1
                case n:
                    return ("fst", n)
        case ("snd", pair):
            match normalize(pair):
                case (",", _, _, tm2):
                    return tm2
                case n:
                    return ("snd", n)
        case (cons, *ts):
            return (cons, *(normalize(t) for t in ts))
        case _:
            return tm

def conv(tm1, tm2, ty):
    # Checks whether tm1 <=> tm2.
    if tm1 == tm2: return
    match normalize(ty):
        case ("U",):
            match tm1, tm2:
                case ("U",), ("U",):
                    return
                case ("Π", dom1, ("Bind", x1, cod1)),\
                    ("Π", dom2, ("Bind", x2, cod2)):
                    conv(dom1, dom2, ("U",))
                    conv(cod1, subst(cod2,{x2:("Var",x1)}), ("U",))
                case ("Σ", dom1, ("Bind", x1, cod1)),\
                    ("Σ", dom2, ("Bind", x2, cod2)):
                    conv(dom1, dom2, ("U",))
                    conv(cod1, subst(cod2,{x2:("Var",x1)}), ("U",))
                case _ if tm1 != tm2:
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
    match normalize(ty):
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
                pass
                # TODO check eqs[i] : Id_{x...(i-1) => tys[i]}^{eqs...(i-1)}(left[i],right[i])
            # TODO return Id_..C(t[left], t[right])
            pass
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
