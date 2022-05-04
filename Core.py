"""
Core Syntax: Use Lisp style tuples.

("Var", x) : Variables.
("Bind", *xs, t) : Bind variables.

Lazy trees: A nullary function that exposes the constructor,
  and the arguments are again lazy trees.
"""
fresh = 0  # Global counter for fresh variables.

def fresh_var(name="x"):
    global fresh
    fresh += 1
    return name + "#" + str(fresh)

def subst(t, subs : dict):
    """
    Substitute variables in t with values in subs.
    """
    match t:
        case ("Var", y) if y in subs:
            return subs[y]
        case ("Var", _):
            return t
        case ("Bind", *xs, body):
            ys = [fresh_var(x) for x in xs]
            new_subs = {x:subs[x] for x in subs}
            new_subs.update({y:("Var", ys[i]) for i, y in enumerate(xs)})
            return ("Bind", *ys, subst(body, new_subs))
        case (cons, *ts):
            return (cons, *(subst(t, subs) for t in ts))
        case _:
            return t

def strip_parens(str):
    if str[0] == "(" and str[-1] == ")":
        return str[1:-1]
    return str

def pretty(t):
    """
    Pretty print a term.
    """
    match t:
        case ("Var", x):
            return x
        case ("Bind", *xs, t1):
            return "(" + " ".join(xs) + " => " + strip_parens(pretty(t1)) + ")"
        case (cons,):
            return cons
        case (cons, t):
            return "(" + cons + " " + strip_parens(pretty(t)) + ")"
        case (*ts,):
            return "(" + " ".join(map(pretty, ts)) + ")"
        case _:
            return str(t)

# def to_lazy(t):
#     """
#     Convert a term to a lazy tree.
#     """
#     match t:
#         case (cons, *ts):
#             return lambda: (cons, *(to_lazy(t) for t in ts))
#         case _:
#             return t

# def from_lazy(t):
#     """
#     Fully evaluate a lazy tree.
#     """
#     if not callable(t):
#         return t
#     match t():
#         case (cons, *ts):
#             return (cons, *(from_lazy(t) for t in ts))
#         case u:
#             return u

# def unpack(lazy):
#     if not callable(lazy):
#         return lazy
#     return lazy()

if __name__ == "__main__":
    tm = ("Lam", ("Bind", "x", ("App", ("Var", "x"), ("Var", "y"))))
    print(pretty(subst(tm, {"x": ("Var", "z")})))
    print(pretty(subst(tm, {"y": ("Var", "z")})))
