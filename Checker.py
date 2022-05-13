from Core import *
from Parser import parse, pretty
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
        for k, v in shadowed.items():
            self.context[k] = v

    def rewrite(self, expr):
        if self.rewrites:  # User rewrite rules
            if rexp := self.rewrites(expr) is not None:
                return rexp
        pass

    def _normalize(self, expr):  # Brutal CBV
        changed = True
        touched = False
        while True:
            while changed:
                changed = False
                rexpr = []
                for subexpr in expr:
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
            case _:
                raise ValueError("Unexpected term: " + pretty(expr))

    def check(self, expr, ty):
        ty1 = self.infer(expr)
        self.conversion(ty1, ty)

    def ensure_head(self, expr, head):
        """
        Ensures that the normal form of expr has head head.
        """
        # Directly normalizing, slow.
        expr = self.normalize(expr)
        if expr[0] != head:
            raise ValueError("Expected " + head + ", got " + pretty(expr))
        return expr
