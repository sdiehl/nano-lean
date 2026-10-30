"""Write the micro benches beside this script: python3 benches/micro/gen.py"""

import sys
from pathlib import Path

sys.set_int_max_str_digits(0)

HERE = Path(__file__).parent

NAT = """inductive Nat : Type
  | Nat.zero : Nat
  | Nat.succ : Nat -> Nat
inductive Eq.{u} (A : Sort u) (a : A) : A -> Prop
  | Eq.refl : Eq A a a
"""

ARITH = """def Nat.add : Nat -> Nat -> Nat :=
  fun (m : Nat) (n : Nat) => Nat.rec.{1} (fun (k : Nat) => Nat) m (fun (k : Nat) (ih : Nat) => Nat.succ ih) n
def Nat.mul : Nat -> Nat -> Nat :=
  fun (m : Nat) (n : Nat) => Nat.rec.{1} (fun (k : Nat) => Nat) 0 (fun (k : Nat) (ih : Nat) => Nat.add ih m) n
def Nat.pow : Nat -> Nat -> Nat :=
  fun (m : Nat) (n : Nat) => Nat.rec.{1} (fun (k : Nat) => Nat) 1 (fun (k : Nat) (ih : Nat) => Nat.mul ih m) n
"""


def eq(lhs, rhs, ty="Nat"):
    return f"Eq.{{1}} {ty} ({lhs}) ({rhs})"


def thm(name, lhs, rhs, ty="Nat"):
    return f"theorem {name} : {eq(lhs, rhs, ty)} := Eq.refl.{{1}} {ty} ({rhs})\n"


def church():
    """Beta reduction and closure application: Church numeral arithmetic normalized to s^n z."""
    out = (
        NAT
        + """axiom T : Type
axiom s : T -> T
axiom z : T
def Ch : Sort 2 := forall (A : Type), (A -> A) -> A -> A
def c2 : Ch := fun (A : Type) (f : A -> A) (x : A) => f (f x)
def c3 : Ch := fun (A : Type) (f : A -> A) (x : A) => f (f (f x))
def cadd : Ch -> Ch -> Ch := fun (m : Ch) (n : Ch) (A : Type) (f : A -> A) (x : A) => m A f (n A f x)
def cmul : Ch -> Ch -> Ch := fun (m : Ch) (n : Ch) (A : Type) (f : A -> A) => m A (n A f)
def cexp : Ch -> Ch -> Ch := fun (m : Ch) (n : Ch) (A : Type) => n (A -> A) (m A)
def c4 : Ch := cmul c2 c2
def c8 : Ch := cmul c2 c4
def c12 : Ch := cmul c3 c4
"""
    )
    out += thm(
        "exp_mul", "cexp c2 c12 T s z", "cmul (cexp c2 c4) (cexp c2 c8) T s z", "T"
    )
    out += thm(
        "exp_exp", "cexp c3 c8 T s z", "cmul (cexp c3 c4) (cexp c3 c4) T s z", "T"
    )
    out += thm(
        "add_mul",
        "cadd (cexp c2 c12) (cexp c2 c12) T s z",
        "cexp c2 (cadd c12 (fun (A : Type) (f : A -> A) => f)) T s z",
        "T",
    )
    return out


def recursor():
    """Iota reduction: unary recursion through Nat.rec on literal majors, under names the
    kernel does not accelerate."""
    out = (
        NAT
        + """def plus : Nat -> Nat -> Nat :=
  fun (m : Nat) (n : Nat) => Nat.rec.{1} (fun (k : Nat) => Nat) m (fun (k : Nat) (ih : Nat) => Nat.succ ih) n
def times : Nat -> Nat -> Nat :=
  fun (m : Nat) (n : Nat) => Nat.rec.{1} (fun (k : Nat) => Nat) 0 (fun (k : Nat) (ih : Nat) => plus ih m) n
def tri : Nat -> Nat :=
  fun (n : Nat) => Nat.rec.{1} (fun (k : Nat) => Nat) 0 (fun (k : Nat) (ih : Nat) => plus ih (Nat.succ k)) n
"""
    )
    for i, n in enumerate([30, 45, 60]):
        out += thm(f"times_{i}", f"times {n} {n}", str(n * n))
    for i, n in enumerate([60, 90, 120]):
        out += thm(f"tri_{i}", f"tri {n}", str(n * (n + 1) // 2))
    return out


def literals():
    """Big Nat literal arithmetic through the accelerated Nat.add, Nat.mul and Nat.pow."""
    out = NAT + ARITH
    k = 0
    for b in (3, 7):
        for e in (10000, 30000):
            out += thm(f"pow_{k}", f"Nat.pow {b} {e}", str(b**e))
            k += 1
    for i in range(200):
        a, b = 10**60 + 7 * i, 10**58 + 13 * i
        out += thm(
            f"mix_{i}",
            f"Nat.add (Nat.mul {a} {b}) (Nat.pow {i + 2} 40)",
            str(a * b + (i + 2) ** 40),
        )
    return out


def delta():
    """Lazy delta: two definition towers of equal and unequal height, compared at the top,
    plus equal heads whose arguments agree only after unfolding."""
    n = 1000
    out = NAT + ARITH
    for tower in "fg":
        out += f"def {tower}0 : Nat -> Nat := fun (x : Nat) => Nat.succ x\n"
        for i in range(1, n + 1):
            out += f"def {tower}{i} : Nat -> Nat := fun (x : Nat) => {tower}{i - 1} x\n"
    out += thm("same_height", f"f{n} 5", f"g{n} 5")
    out += thm("mixed_height", f"f{n} 5", f"g{n // 2} 5")
    out += thm("args_unfold", f"f{n} (Nat.add 2 2)", f"f{n} (g{n} 3)")
    out += thm("to_literal", f"f{n} (f{n} (g{n} 0))", "3")
    return out


def lets():
    """Zeta reduction and environment growth: long dependent let chains."""
    n = 2000
    body = "x0"
    chain = "let x0 : Nat := 0 in "
    for i in range(1, n + 1):
        chain += f"let x{i} : Nat := Nat.succ x{i - 1} in "
        body = f"x{i}"
    out = NAT
    out += f"theorem chain : {eq(chain + body, str(n))} := Eq.refl.{{1}} Nat {n}\n"
    dep = ""
    for i in range(1, n // 4 + 1):
        dep += f"let T{i} : Type := Nat in let y{i} : T{i} := {i} in "
    out += f"theorem typed : {eq(dep + 'y1', '1')} := Eq.refl.{{1}} Nat 1\n"
    return out


def eta():
    """Structure and function eta, with nested projections through a tower of named products."""
    depth = 8
    out = (
        NAT
        + """inductive Prod.{u, v} (A : Sort (u+1)) (B : Sort (v+1)) : Sort (max (u+1) (v+1))
  | Prod.mk : A -> B -> Prod A B
def P0 : Type := Nat
"""
    )
    for i in range(1, depth + 1):
        out += f"def P{i} : Type := Prod.{{0, 0}} P{i - 1} P{i - 1}\n"

    def rebuild(d, x):
        if d == 0:
            return x
        h = f"P{d - 1}"
        return (
            f"(Prod.mk.{{0, 0}} {h} {h} {rebuild(d - 1, f'(proj Prod 0 {x})')} "
            f"{rebuild(d - 1, f'(proj Prod 1 {x})')})"
        )

    t = f"P{depth}"
    for i in range(4):
        out += f"theorem struct_{i} : forall (p : {t}), Eq.{{1}} {t} p {rebuild(depth, 'p')} :=\n  fun (p : {t}) => Eq.refl.{{1}} {t} p\n"
    lam = "f"
    for i in range(200):
        lam = f"(fun (x{i} : Nat) => {lam} x{i})"
    out += f"theorem fun_eta : forall (f : Nat -> Nat), Eq.{{1}} (Nat -> Nat) f {lam} :=\n  fun (f : Nat -> Nat) => Eq.refl.{{1}} (Nat -> Nat) f\n"
    return out


def irrelevance():
    """Proof irrelevance: a function of many proof arguments applied to distinct proofs that
    are equal only by irrelevance."""
    proofs, args, n = 300, 40, 200
    prop = "Eq.{1} Nat 0 0"
    out = NAT + f"axiom F : {' -> '.join([prop] * args)} -> Nat\n"
    out += f"def q0 : {prop} := Eq.refl.{{1}} Nat 0\n"
    for i in range(1, proofs):
        out += f"def q{i} : {prop} := (fun (h : {prop}) => h) q{i - 1}\n"
    for i in range(n):
        lhs = " ".join(f"q{(i * 7 + j * 13) % proofs}" for j in range(args))
        rhs = " ".join(f"q{(i * 11 + j * 17 + 1) % proofs}" for j in range(args))
        out += thm(f"irr_{i}", f"F {lhs}", f"F {rhs}")
    return out


for f in (church, recursor, literals, delta, lets, eta, irrelevance):
    (HERE / f"{f.__name__}.ltc").write_text(
        "-- " + " ".join(f.__doc__.split()) + "\n" + f()
    )
