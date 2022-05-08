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

# tele trisects a sequence of terms
def tele(tylreqs):
    if len(tylreqs) % 3 != 0:
        raise Exception("Malformed telescope")
    l = len(tylreqs)//3
    return tylreqs[:l], tylreqs[l:2*l], tylreqs[2*l:]
