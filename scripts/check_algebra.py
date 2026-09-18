#!/usr/bin/env python3
"""Exact symbolic regression tests; NOT a substitute for Lean checking."""
from __future__ import annotations
from itertools import product
import json
from pathlib import Path
import sympy as s

checks: list[dict[str, str]] = []

def check(name: str, expr: s.Expr) -> None:
    normal = s.cancel(s.expand(expr))
    if normal != 0:
        raise AssertionError(f'{name}: nonzero residual {normal}')
    checks.append({'name': name, 'result': 'PASS (symbolic identity only)'})

def m(x, y):
    return (x[0]*(y[1]+y[2]+y[3]) + x[1]*(y[0]+y[1])
            + x[2]*(y[0]+2*y[2]) + x[3]*(y[0]+4*y[3]))

def n(x, y):
    return m(x, y)+x[0]*y[0]

def a0(x, y, z):
    return (x[0]*m(y,z)+y[0]*m(x,z)+z[0]*m(x,y))/3

def c3(x, y, z):
    return (x[1]*y[2]*z[3]+x[1]*y[3]*z[2]+x[2]*y[1]*z[3]
            +x[2]*y[3]*z[1]+x[3]*y[1]*z[2]+x[3]*y[2]*z[1])

def a(t, x, y, z):
    return a0(x,y,z)+t*c3(x,y,z)

def b4(w, x, y, z):
    return (n(w,x)*n(y,z)+n(w,y)*n(x,z)+n(w,z)*n(x,y))/3

alpha,beta,gamma,delta=s.symbols('alpha beta gamma delta', nonzero=True)
u01,u02,u03,u12,u13,u23=s.symbols('u01 u02 u03 u12 u13 u23')
quartet=((u01+alpha*beta)*(u23+gamma*delta)
         +(u02+alpha*gamma)*(u13+beta*delta)
         +(u03+alpha*delta)*(u12+beta*gamma))
r=[u01/(alpha*beta),u02/(alpha*gamma),u03/(alpha*delta),
   u12/(beta*gamma),u13/(beta*delta),u23/(gamma*delta)]
check('normalized quartic factorization', quartet-alpha*beta*gamma*delta*
      ((r[0]+1)*(r[5]+1)+(r[1]+1)*(r[4]+1)+(r[2]+1)*(r[3]+1)))
check('inactive column: three active coordinates',
      2*beta*gamma*u03-(gamma*(alpha*u13+beta*u03)
      +beta*(alpha*u23+gamma*u03)-alpha*(beta*u23+gamma*u13)))
check('inactive column: two active coordinates',
      2*beta*u02*u03-(u02*(alpha*u13+beta*u03)
      +u03*(alpha*u12+beta*u02)-alpha*(u02*u13+u03*u12)))
check('cubic residual elimination',
      alpha*(beta*u23+gamma*u13+delta*u12)-(
      beta*(alpha*u23+gamma*u03+delta*u02)
      +gamma*(alpha*u13+beta*u03+delta*u01)
      +delta*(alpha*u12+beta*u02+gamma*u01)
      -2*(beta*gamma*u03+beta*delta*u02+gamma*delta*u01)))
q=[s.symbols(f'q{i}_0:4') for i in range(4)]
y=s.symbols('y0:4')
t=s.symbols('tau')
x=[sum(q[j][i]*y[j] for j in range(4)) for i in range(4)]
poly=s.Poly(s.expand(a(t,x,x,x)+b4(x,x,x,x)), *y)
for subset in ((1,2,3),(0,2,3),(0,1,3),(0,1,2),(0,1,2,3)):
    averaged=s.S.Zero
    for powers,coef in poly.terms():
        weight_sum=sum(s.prod(sgn[i] for i in subset)*
                       s.prod(sgn[i]**powers[i] for i in range(4))
                       for sgn in product((-1,1), repeat=4))
        averaged += s.Rational(weight_sum,16)*coef*s.prod(y[i]**powers[i] for i in range(4))
    expected=(6*a(t,*(q[i] for i in subset)) if len(subset)==3
              else 24*b4(*q))*s.prod(y[i] for i in subset)
    check('high parity '+''.join(map(str,subset)), averaged-expected)
# All Boolean Walsh identities, checked separately in exact integer arithmetic.
patterns=list(product((-1,1), repeat=4))
masks=list(product((0,1), repeat=4))
def char(mask,pattern):
    return s.prod(pattern[i]**mask[i] for i in range(4))
for mask in masks:
    if any(mask):
        check('Walsh sum '+''.join(map(str,mask)),sum(char(mask,p) for p in patterns))
for i,p in enumerate(patterns):
    for j,rp in enumerate(patterns):
        check(f'Walsh orthogonality {i},{j}',
              sum(char(mask,p)*char(mask,rp) for mask in masks)-(16 if i==j else 0))

# Local tensor elimination: freely varying coordinate and bilinear entries.
a0s,xs,ys,zs,b1,b2,b3,m12,m13,m23,p1,p2,p3,ds,ts = s.symbols(
    'a x y z b1 b2 b3 m12 m13 m23 p1 p2 p3 d t')
e23=a0s*m23+ys*b3+zs*b2+3*ts*p1
e13=a0s*m13+xs*b3+zs*b1+3*ts*p2
e12=a0s*m12+xs*b2+ys*b1+3*ts*p3
e123=xs*m23+ys*m13+zs*m12+3*ts*ds
Q=xs*ys*b3+xs*zs*b2+ys*zs*b1
D=a0s*ds-xs*p1-ys*p2-zs*p3
E=(b1+a0s*xs)*p1+(b2+a0s*ys)*p2+(b3+a0s*zs)*p3
Braw=(b1+a0s*xs)*(m23+ys*zs)+(b2+a0s*ys)*(m13+xs*zs)+(b3+a0s*zs)*(m12+xs*ys)
Qres=-2*Q+3*ts*D
Bres=-2*(b2*b3*xs+b1*b3*ys+b1*b2*zs)-a0s*Q+3*a0s**2*xs*ys*zs-3*ts*E
check('local cubic elimination',a0s*e123-xs*e23-ys*e13-zs*e12-Qres)
check('local quartic elimination',a0s*Braw-(b1+a0s*xs)*e23-(b2+a0s*ys)*e13-(b3+a0s*zs)*e12-Bres)
v1=1-b2*b3+s.Rational(3,2)*a0s**2*ys*zs
v2=1-b1*b3
v3=1-b1*b2
W=s.Rational(3,4)*a0s*D+s.Rational(3,2)*E
check('local coordinate-sum elimination',
      (xs+ys+zs)-(v1*xs+v2*ys+v3*zs-ts*W)-(-Bres/2+a0s*Qres/4))
R=xs**2+ys**2+zs**2
err=(b1-1)*ys*zs+(b2-1)*xs*zs+(b3-1)*xs*ys
check('local positive quadratic form',R+3*ts*D-(xs+ys+zs)**2-2*err-Qres)
terms=s.symbols('v0:4')
check('four-term Cauchy square decomposition',
      4*sum(v*v for v in terms)-sum(terms)**2-
      sum((terms[i]-terms[j])**2 for i in range(4) for j in range(i+1,4)))
ar,br,cr,rho=s.symbols('ar br cr rho')
check('scalar fourth-root expansion identity',
      rho**4-(3-2*ar-4*br)-((rho**2-1)**2-2*(ar-1)*(rho**2-1)-4*br*(rho-1)-2*cr)
      -2*(ar*rho**2+2*br*rho+cr-1))
for mask in masks:
    selected={i for i in range(4) if mask[i]}
    for k in range(4):
        check(f'linear sign selection {mask},{k}',
              sum(char(mask,p)*p[k] for p in patterns)-(16 if selected=={k} else 0))
    if selected:
        for k in range(4):
            for l in range(4):
                check(f'quadratic sign selection {mask},{k},{l}',
                      sum(char(mask,p)*p[k]*p[l] for p in patterns)
                      -(16 if k!=l and selected=={k,l} else 0))
M=s.Matrix(4,4,lambda i,j:s.Symbol(f'e{i}{j}'))
U=s.eye(4)+M
for i in range(4):
    for j in range(4):
        check(f'Gram second-order identity {i},{j}',
              (U*U.T)[i,j]-(1 if i==j else 0)-M[i,j]-M[j,i]-(M*M.T)[i,j])

report={'scope':'Exact algebra only. No Lean execution or kernel verification.',
        'checks':len(checks), 'results':checks}
out=Path(__file__).resolve().parents[1]/'validation'/'algebra.json'
out.parent.mkdir(exist_ok=True)
out.write_text(json.dumps(report,indent=2)+'\n')
print(f'{len(checks)} exact algebra identities passed.')
print('Lean: NOT RUN by this script.')
