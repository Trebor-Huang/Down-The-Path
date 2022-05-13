from functools import reduce
from Core import *
"""
head := Σ | Π | λ
sc :=  <var> "/" <term> : <term> == <term>
bind := <var> : <type>
tele := sc  separated by ";"
term := <var> | <const>
    | (<head> (<bind>)*)* => <term>     ; lowest precedence, right-associative
    | <term> <term>                     ; high precedence, left-associative
    | <term> { <var> => <term> } <term> ; middle precedence, right-associative
    | fst <term> | snd <term>           ; maximal precedence, right-associative
    | Id [ <tele> . <type> ] [ <term> , <term> ]
    | ap [ <tele> . <term> ]
type := <term>
"""  # wildcard _ doesn't bind

VAR_CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_"

examples = [
    "x",
    "Σ(A : U)(a : A) Π(b : A) => Id[ . A ][a, b]",
    "ap[.a]",
    "ap[x/eq:l==r . f x]",
    "Π(A : U)(B : Π (a : A) => U)(f : Π (a : A) => B a)(a : A) => B a",
    "f fst p q snd fst (p q)",  # f (fst p) q (snd (fst (p q)))
]

def lex(string):
    string = string.lstrip()
    while string:
        if string[0] in "(){}[].:;|,ΣΠλ=/":
            if string[0:2] in ("=>", "=="):
                yield string[0:2]
                string = string[2:]
            else:
                yield string[0]
                string = string[1:]
        else:
            k = 0
            if string[0] == "\\":
                k = 1
            while k < len(string) and string[k] in VAR_CHARS:
                k += 1
            yield string[:k]
            string = string[k:]
        string = string.lstrip()

def scope_check(string):
    if string in ("0", "1", "*", "absurd"):
        return ("con", string)
    elif string == "U":
        return ("U",)
    elif all(x in VAR_CHARS for x in string):
        return ("Var", string)

def parse0(tokens): # vars, consts, parens, Id, ap
    match tokens[0]:
        case "(":
            tokens.pop(0)
            expr, tokens = parse(tokens)
            if tokens and tokens[0] == ")":
                tokens.pop(0)
                return expr, tokens
            else:
                raise SyntaxError("Expected ')', got '%s'" % tokens[0])
        case "Id":
            tokens.pop(0)
            if tokens and tokens[0] == "[":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected '[', got '%s'" % tokens[0])
            vs, left, right, eqs, tokens = parse_tele(tokens)
            if tokens and tokens[0] == ".":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected '.', got '%s'" % tokens[0])
            type, tokens = parse(tokens)
            if tokens and tokens[0] == "]":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected ']', got '%s'" % tokens[0])
            if tokens and tokens[0] == "[":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected '[', got '%s'" % tokens[0])
            fst, tokens = parse(tokens)
            if tokens and tokens[0] == ",":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected ',', got '%s'" % tokens[0])
            snd, tokens = parse(tokens)
            if tokens and tokens[0] == "]":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected ']', got '%s'" % tokens[0])
            return ("Id", ("Bind", *vs, type), *left, *right, *eqs, fst, snd), tokens
        case "ap":
            tokens.pop(0)
            if tokens and tokens[0] == "[":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected '[', got '%s'" % tokens[0])
            vs, left, right, eqs, tokens = parse_tele(tokens)
            if tokens and tokens[0] == ".":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected '.', got '%s'" % tokens[0])
            type, tokens = parse(tokens)
            if tokens and tokens[0] == "]":
                tokens.pop(0)
            else:
                raise RuntimeError("Expected ']', got '%s'" % tokens[0])
            return ("ap", ("Bind", *vs, type), *left, *right, *eqs), tokens
        case t if r := scope_check(t):
            return r, tokens[1:]
        case _:
            raise SyntaxError("Expected '(', got '%s'" % tokens[0])

def pretty0(expr):
    match expr:
        case ("U",):
            return "U"
        case ("Var", var):
            return pretty_Var(var)
        case ("cons", const):
            return const
        case ("Id", ("Bind", *vs, type), *scope, fst, snd):
            left, right, eqs = (), (), () # tele(scope)
            return "Id[%s . %s][%s, %s]" % (
                pretty_tele(vs, left, right, eqs),
                pretty(type),
                pretty(fst),
                pretty(snd)
            )
        case ("ap", ("Bind", *vs, type), *scope):
            left, right, eqs = (), (), () # tele(scope)
            return "ap[%s . %s]" % (
                pretty_tele(vs, left, right, eqs),
                pretty(type)
            )
        case _:
            return "(%s)" % pretty(expr)

def parse1(tokens):  # fst and snd
    toks = []
    while tokens and tokens[0] in ("fst", "snd"):
        toks.append(tokens.pop(0))
    expr, tokens = parse0(tokens)
    while toks:
        expr = (toks.pop(), expr)
    return expr, tokens

def pretty1(expr):
    string = ""
    while expr[0] in ("fst", "snd"):
        string += expr[0] + " "
        expr = expr[1]
    return string + pretty0(expr)

def parse2(tokens):  # application
    exprs = []
    while tokens:
        try:
            expr, tokens = parse1(tokens)
        except SyntaxError:
            break
        exprs.append(expr)
    return reduce(lambda x, y: ("@", x, y), exprs), tokens

def pretty2(expr):
    if expr[0] == "@":
        return pretty2(expr[1]) + " " + pretty1(expr[2])
    else:
        return pretty1(expr)

def parse3(tokens):  # dependent pair
    fst, tokens = parse2(tokens)
    if tokens and tokens[0] == "{":
        tokens.pop(0)
    else:
        return fst, tokens  # !
    v = scope_check(tokens.pop(0))
    if not v or v[0] != "Var":
        raise RuntimeError("Expected variable, got '%s'" % tokens[0])
    v = v[1]
    if tokens and tokens[0] == "=>":
        tokens.pop(0)
    else:
        raise RuntimeError("Expected '=>', got '%s'" % tokens[0])
    body, tokens = parse(tokens)
    if tokens and tokens[0] == "}":
        tokens.pop(0)
    else:
        raise RuntimeError("Expected '}', got '%s'" % tokens[0])
    snd, tokens = parse2(tokens)
    return (",", ("Bind", v, body), fst, snd), tokens

def pretty3(expr):
    match expr:
        case (",", ("Bind", v, body), fst, snd):
            return "%s { %s => %s } %s" % (pretty2(fst), pretty_Var(v), pretty(body), pretty3(snd))
        case _:
            return pretty2(expr)

def parse_sc(tokens):
    v = scope_check(tokens[0])
    if not v or v[0] != "Var":
        raise SyntaxError("Expected variable, got '%s'" % tokens[0])
    tokens.pop(0)
    v = v[1]
    if tokens.pop(0) != "/":
        raise RuntimeError("Expected '/', got '%s'" % tokens[1])
    t, tokens = parse(tokens)
    if tokens and tokens[0] == ":":
        tokens.pop(0)
    else:
        raise RuntimeError("Expected ':', got '%s'" % tokens[0])
    body, tokens = parse(tokens)
    if tokens and tokens[0] == "==":
        tokens.pop(0)
    else:
        raise RuntimeError("Expected '==', got '%s'" % tokens[0])
    body2, tokens = parse(tokens)
    return v, t, body, body2, tokens

def parse_tele(tokens):
    vs = []
    left = []
    right = []
    eqs = []
    while tokens:
        try:
            v, t, l, r, tokens = parse_sc(tokens)
        except SyntaxError:
            break
        vs.append(v)
        left.append(l)
        right.append(r)
        eqs.append(t)
    return vs, left, right, eqs, tokens

def pretty_tele(var, left, right, eqs):
    return " ;".join("%s / %s : %s == %s" % (pretty_Var(v), pretty(e), pretty(l), pretty(r))
            for v, l, r, e in zip(var, left, right, eqs))

def parse_binder(tokens):
    if tokens and tokens[0] == "(":
        tokens.pop(0)
    else:
        raise SyntaxError("Expected '(', got '%s'" % tokens[0])
    v = scope_check(tokens.pop(0))
    if not v or v[0] != "Var":
        raise RuntimeError("Expected variable, got '%s'" % tokens[0])
    v = v[1]
    if tokens and tokens[0] == ":":
        tokens.pop(0)
    else:
        raise RuntimeError("Expected ':', got '%s'" % tokens[0])
    t, tokens = parse(tokens)
    if tokens and tokens[0] == ")":
        tokens.pop(0)
    else:
        raise RuntimeError("Expected ')', got '%s'" % tokens[0])
    return (v, t), tokens

def parse_binders(tokens):
    binders = []
    while tokens and tokens[0] in "ΣΠλ":
        head = tokens.pop(0)
        while tokens:
            try:
                binder, tokens = parse_binder(tokens)
            except SyntaxError:
                break
            binders.append((head, *binder))
        if tokens and tokens[0] == "=>":
            tokens.pop(0)
    return binders, tokens

def parse(tokens):  # binders
    binders, tokens = parse_binders(tokens)
    expr, tokens = parse3(tokens)
    while binders:
        hd, v, ty = binders.pop()
        expr = (hd, ty, ("Bind", v, expr))
    return expr, tokens

def pretty(expr):
    string = ""
    current = ""
    while expr[0] in "ΣΠλ":
        if expr[0] != current:
            string += expr[0] + " "
            current = expr[0]
        (_, ty, (_, v, expr)) = expr
        string += "(%s : %s) " % (pretty_Var(v), pretty(ty))
    return (string + "=> " if string else "") + pretty3(expr)

def parse_statement(tokens):
    match tokens[0]:
        case "\\constant":
            tokens.pop(0)
            v = scope_check(tokens.pop(0))
            if not v or v[0] != "Var":
                raise RuntimeError("Expected variable, got '%s'" % tokens[0])
            v = v[1]
            expr, tokens = parse(tokens)
            return ("\\constant", v, expr), tokens
        case "\\define":
            tokens.pop(0)
            v = scope_check(tokens.pop(0))
            if not v or v[0] != "Var":
                raise RuntimeError("Expected variable, got '%s'" % tokens[0])
            v = v[1]
            expr, tokens = parse(tokens)
            return ("\\define", v, expr), tokens
        case "\\infer":
            tokens.pop(0)
            expr, tokens = parse(tokens)
            return ("\\infer", expr), tokens

def file_parse(string):
    tokens = list(lex(string))
    while tokens:
        statement, tokens = parse_statement(tokens)
        yield statement

if __name__ == "__main__":
    for ex in examples:
        expr, tk = parse(list(lex(ex)))
        print(pretty(expr))
