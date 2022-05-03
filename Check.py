from Core import *
"""
Typechecker for MLTT.

===== Core Components =====
Π   Pi types
λ   Functions
@   Application
Σ   Sigma types
(,) Pairs
fst First projection  (Required to mark the other component's type.)
snd Second projection

0   Empty
1   Unit
2   Bool
.. intro and elim rules

U   Universe (Currently spartan McBride style)

is  Type prescription.
"""

def normalize(tm):
    match tm:
        case ("@", fun, arg):
            match normalize(fun):
                case ("λ", _, ("Bind", x, body)):
                    return normalize(subst(body, {x:arg}))
                case nfun:
                    return ("@", nfun, normalize(arg))
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
                    conv(cod1, subst(cod2,{x2:x1}), ("U",))
                case _:
                    raise ValueError("Type mismatch.")
        case ("Π", dom, ("Bind", x, cod)):
            conv(normalize(("@",tm1,("Var",x))),
                normalize(("@",tm2,("Var",x))), cod)
        case _:
            raise ValueError("Unexpected type: " + pretty(ty))

def ensurefun(ty):
    """
    Ensures that the type is a function type.
    Returns (dom, x, cod).
    """
    match normalize(ty):
        case ("Π", dom, ("Bind", x, cod)):
            return dom, x, cod
        case _:
            raise ValueError("Not a function type.")

# Global constants.
constants = dict()
constants["0"] = ("U",)
constants["1"] = ("U",)
constants["*"] = ("con", "1")
constants["2"] = ("U",)
constants["tt"] = ("con", "2")
constants["ff"] = ("con", "2")

def infer(ctx, tm):
    match tm:
        case ("Var", x):
            return ctx[x]
        case ("Bind", *_):
            raise ValueError("Unexpected Bind.")
        case ("Π", dom, ("Bind", x, body)):
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
            dom, x, cod = ensurefun(funty)
            argty = infer(ctx, arg)
            conv(argty, dom, ("U",))
            return subst(cod, {x:arg})
        case ("con", con):
            return constants[con]
        case ("U",):
            return ("U",)

if __name__ == "__main__":
    Id = ("λ", ("U",), ("Bind", "t",
        ("λ", ("Var", "t"), ("Bind", "x",
        ("Var", "x")))))
    print(pretty(Id))
    TId = infer({}, Id)
    print(pretty(TId))
    IdId = ("@", ("@", Id, TId), Id)
    TIdId = infer({}, IdId)
    print(pretty(TIdId))
    nIdId = normalize(IdId)
    print(pretty(nIdId))
