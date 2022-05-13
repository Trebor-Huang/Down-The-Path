from Core import *
from Parser import pretty, file_parse
from contextlib import contextmanager

class Checker:
    def __init__(self, constants=None, rewrites=None):
        """
        Builtin constants are passed in as a dictionary.
        Rewrite rules are passed in as a function.
        """
        self.constants = constants or {}
        self.definitions = {}
        self.rewrites = rewrites
        self.context = {}

    @contextmanager
    def push(self, ctx:dict):
        """
        Pushes in a context of variables. The shadowed variables will be
        restored after the context is exited.
        """
        shadowed = {}
        for k, v in ctx.items():
            if k in self.context:
                shadowed[k] = self.context[k]
            self.context[k] = v
        yield
        for k in ctx:
            if k in shadowed:
                self.context[k] = shadowed[k]
            else:
                del self.context[k]

    def rewrite(self, expr):
        if self.rewrites:  # User rewrite rules
            if rexp := self.rewrites(expr) is not None:
                return rexp
        match expr:
            case ("Var", x):
                if x not in self.context:
                    if x in self.definitions:
                        return self.definitions[x]
                    elif x in self.constants:
                        return ("con", x)

    def _normalize(self, expr):  # Brutal CBV
        if not isinstance(expr, tuple):
            return None
        changed = True
        touched = False
        while True:
            while changed:
                changed = False
                rexpr = [expr[0]]
                for subexpr in expr[1:]:
                    rsubexpr = self._normalize(subexpr)
                    if rsubexpr is not None:
                        touched = True
                        changed = True
                        rexpr.append(rsubexpr)
                    else:
                        rexpr.append(subexpr)
                expr = tuple(rexpr)
            if re := self.rewrite(expr) is None:
                return expr if touched else None
            else:
                expr = re

    def normalize(self, expr):
        return self._normalize(expr) or expr

    def conversion(self, expr1, expr2, ty):
        if expr1 == expr2:
            return
        match ty := self.normalize(ty):
            case ("Π", dom, ("Bind", x, cod)):
                x = fresh(x)
                self.conversion(("@", expr1, ("Var", x)), ("@", expr2, ("Var", x)), cod)
            case ("Σ", dom, ("Bind", x, cod)):
                self.conversion(("fst", expr1), ("fst", expr2), dom)
                self.conversion(("snd", expr1), ("snd", expr2), subst(cod, {x:("fst", expr1)}))
            case ("con", ("0" | "1")):
                return
            case _: # TODO full eta is difficult.
                if self.normalize(expr1) == self.normalize(expr2):
                    return
                print(pretty(expr1), pretty(expr2))
                if input("Are they equal? ") == "n":
                    raise ValueError("Expected " + pretty(expr2) + ", got " + pretty(expr1))

    def infer(self, expr):
        match expr:
            case ("Var", x):
                if x in self.context:
                    return self.context[x]
                elif x in self.definitions:
                    return self.infer(self.definitions[x])
                elif x in self.constants:
                    return self.constants[x]
                raise ValueError("Unknown variable: " + x)
            case ("Bind", *_):
                raise ValueError("Unexpected Bind: " + pretty(expr))
            case (("Π" | "Σ"), dom, ("Bind", x, cod)):
                self.check(dom, ("U",))
                with self.push({x:dom}):
                    self.check(cod, ("U",))
                return ("U",)
            case ("λ", dom, ("Bind", x, body)):
                self.check(dom, ("U",))
                with self.push({x:dom}):
                    cod = self.infer(body)
                return ("Π", dom, ("Bind", x, cod))
            case ("@", fun, arg):
                funty = self.infer(fun)
                (_, dom, (_, x, cod)) = self.ensure_head(funty, "Π")
                self.check(arg, dom)
                return subst(cod, {x:arg})
            case (",", ("Bind", x, tybody), tm1, tm2):
                tyfst = self.infer(tm1)
                with self.push({x:tyfst}):
                    self.check(tybody, ("U",))
                self.check(tm2, subst(tybody, {x:tm1}))
                return ("Σ", tyfst, ("Bind", x, tybody))
            case ("fst", pair):
                pairty = self.infer(pair)
                (_, dom, _) = self.ensure_head(pairty, "Σ")
                return dom
            case ("snd", pair):
                pairty = self.infer(pair)
                (_, _, (_, x, cod)) = self.ensure_head(pairty, "Σ")
                return subst(cod, {x:("fst", pair)})
            case ("con", con):  # constant
                return self.constants[con]
            case ("U",):
                return ("U",)  # Type in type.
            case ("Id", ("Bind", *vars, ty),
                ("Telescope", *left),
                ("Telescope", *right),
                ("Telescope", *eqs), lhs, rhs):
                tys = self.infer_idScope(vars, left, right, eqs)
                with self.push({v:t for v, t in zip(vars, tys)}):
                    self.check(ty, ("U",))
                self.check(lhs, subst(ty, {v:l for v, l in zip(vars, left)}))
                self.check(rhs, subst(ty, {v:r for v, r in zip(vars, right)}))
            case ("ap", ("Bind", *vars, expr),
                ("Telescope", *left),
                ("Telescope", *right),
                ("Telescope", *eqs)):
                tys = self.infer_idScope(vars, left, right, eqs)
                with self.push({v:t for v, t in zip(vars, tys)}):
                    ty = self.infer(expr)
                return ("Id", ("Bind", *vars, ty),
                    ("Telescope", *left),
                    ("Telescope", *right),
                    ("Telescope", *eqs),
                    subst(ty, {v:l for v, l in zip(vars, left)}),
                    subst(ty, {v:r for v, r in zip(vars, right)}))
            case _:
                raise ValueError("Unexpected term: " + pretty(expr))

    def infer_idScope(self, vars, left, right, eqs):
        if len(vars) == len(left) == len(right) == len(eqs) == 0:
            return ()
        tys = self.infer_idScope(vars[:-1], left[:-1], right[:-1], eqs[:-1])
        with self.push({v:t for v, t in zip(vars[:-1], tys)}):
            lty = self.infer(left[-1])
            rty = self.infer(right[-1])
            self.conversion(lty, rty, ("U",))
            self.check(eqs[-1],
                ("Id", ("Bind", *vars[:-1], lty),
                    ("Telescope", *left[:-1]),
                    ("Telescope", *right[:-1]),
                    ("Telescope", *eqs[:-1]),
                    left[-1], right[-1]))
        return tys + (lty,)

    def check(self, expr, ty):
        ty1 = self.infer(expr)
        self.conversion(ty1, ty, ("U",))

    def ensure_head(self, expr, head):
        """
        Ensures that the normal form of expr has head head.
        """
        # Directly normalizing, slow.
        expr = self.normalize(expr)
        if expr[0] != head:
            raise ValueError("Expected " + head + ", got " + pretty(expr))
        return expr

if __name__ == "__main__":
    with open("test.hott", "r") as f:
        code = f.read()
    checker = Checker(constants={
        "0" : ("U",),
        "1" : ("U",),
        "*" : ("con", "1"),
        "absurd" : ("Π", ("0",), ("Bind", "_", ("Π", ("U",), ("Bind", "T", ("Var", "T")))))
    })
    for command in file_parse(code):
        match command:
            case ("\\constant", name, ty):
                checker.constants[name] = ty
            case ("\\define", name, body):
                checker.definitions[name] = body
            case ("\\infer", expr):
                print(pretty(checker.infer(expr)))
            case ("\\normalize", expr):
                print(pretty(checker.normalize(expr)))
