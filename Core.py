"""
Core Syntax: Use Lisp style tuples.

("Var", x) : Variables.
("Bind", *xs, t) : Bind variables.
"""
fresh = 0  # Global counter for fresh variables.

def fresh_var(name="x"):
    global fresh
    fresh += 1
    return name.split("#")[0] + "#" + str(fresh)

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

def pretty_Var(v):
    name = v.split("#")
    if len(name) == 1:
        return v
    else:
        return name[0] + name[1].translate(str.maketrans("0123456789","₀₁₂₃₄₅₆₇₈₉"))

def freevar(term):
    """
    Return a set of free variables in term.
    """
    match term:
        case ("Var", x):
            return {x}
        case ("Bind", *xs, t):
            return freevar(t) - set(xs)
        case (cons, *ts):
            return set.union(*(freevar(t) for t in ts))
        case _:
            raise ValueError("Unexpected term: " + str(term))

def alpha(t1, t2) -> bool:
    """
    Return True if t1 and t2 are alpha equivalent.
    """
    match t1, t2:
        case ("Var", x), ("Var", y):
            return x == y
        case ("Bind", *xs, t1), ("Bind", *ys, t2):
            return alpha(t1, subst(t2, {y:("Var", x) for x, y in zip(xs, ys)}))
        case (cons1, *ts1), (cons2, *ts2) if cons1 == cons2:
            return all(alpha(t1, t2) for t1, t2 in zip(ts1, ts2))
        case _:
            return t1 == t2
