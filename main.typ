#import "template.typ": *
#set heading(numbering: "1.a.")
#let lebs = [ $L^2(Omega)$ ]
#let into = [ $integral_Omega$ ]
#let dx = [ $dif x$ ]
#let bd(term) = [ $bold(#term)$]

#let thm = counter("theorem")
#let theorem(term, name: "", type: "Theorem") = block(fill: luma(240), inset: 6pt, width: 100%, radius: 2pt)[
  *#type #thm.display()*#if name == "" {} else {[ (#name)]}. #thm.step() #term 
]
#let corollary(term, name: "") = theorem(name: name, type: "Corollary")[#term]
#let lemma(term, name: "") = theorem(name: name, type: "Lemma")[#term]
#let example(term, name: "") = theorem(name: name, type: "Example")[#term]
#let definition(term, name: "") = theorem(name: name, type: "Definition")[#term]
// #let proof(term) = block[_Proof._ #term #align(right)[$qed$]]
#let proof(term) = block(width: 100%)[_Proof._ #term #h(1fr) $qed$]



// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.
#show: project.with(
  title: "Scientific Computation and Numerical Analysis",
  authors: (
    "Yuhang Wei",
  ),
  date: "March 23, 2023",
)

= FEM for PDEs I

== Problem statement (strong form)

Define $Omega = [0, 1]$. Given $f : Omega -> RR$, find $u : Omega -> RR$ such that 
$ cases(-u'' = f, u(0) = 0, u(1) = 0) $

This is a two-point boundary value problem. 

== Problem statement (weak form)

Define the Sobolev spaces 
$ H^1(Omega) = {v : Omega -> RR | v, v' in L^2 (Omega)} $
$ H_0^1(Omega) = { v in H^1(Omega) | v(0) = v(1) = 0} $

where $L^2(Omega)$ is the Lebesgue space. 

Find $u in H_1^0(Omega)$ such that 
$ integral_0^1 u' v' dif x = integral_0 ^1 f v dif x  $
for any $v in H_0^1(Omega)$.



== Deriving weak form from strong form

Let $u$ solve the strong form. Then take any $v in H_0^1(Omega)$, we have $ -u'' v = f v $ Integrate over $Omega$ and use the boundary conditions to obtain 
$ integral_0^1 u' v' dif x = integral_0 ^1 f v dif x  $

== Petrov-Galerkin discretization


Abstract weak form. Find $u in U$ such that $ b(u, v) = l(v) $ for any $v in V$.

Given discrete subspaces $U_h subset U$ and $V_h subset V$ with $dim U_h = dim V_h$, find $u_h in U_h$ such that $ b(u_h, v_h) = l(v_h) $ for any $v_h in V_h$.

This method is called _Galerkin discretization_ when $U_h = V_h$.

A _finite element mesh_ is a partition of $Omega$ into non-overlapping subsets. $U_h$ and $V_h$ are the span of basis functions which are defined with respect to a finite element mesh. 

For example, let $U_h = "span"{x, x^2}$ and $V_h = "span"{1, x}$. Then $u_h = u_1 x + u_2 x^2$ where $u_1, u_2$ are to be determined. Setting $v_h(x) = 1$ and $v_h(x) = x$ gives two equations for $u_1$ and $u_2$. We then compute $u_1$ and $u_2$ to obtain $u_h(x)$. 

== Finite element spaces in 1-D

Consider $Omega subset RR$ with finite element mesh $ {(x_0, x_1), (x_1, x_2), dots, (x_(N-1), x_N)} $

Define 'hat' basis function $ phi _j (x_i) = cases(1 quad "if " i = j, 0 quad "if " i != j) $

Then $U_h = "span"{ phi_j } _(j = 1) ^ N$.

Also define $ psi_i(x) = cases(1 quad "if " x in (x_(i-1), x_i), 0 quad "otherwise") $

Then $V_h = "span"{ psi_i } _(i = 1) ^ N $. 

Then the problem can be changed to solving an algebraic system $A bold(u) = bold(b)$, where $ A = mat(
  1, 0, 0, ..., 0; 
  -1, 1, 0, ..., 0;
  0, -1, 1, ..., 0;
  0, 0, -1, ..., 0;
  dots.v, dots.v, dots.v, dots.down, dots.v;
  0, 0, 0, ..., 1
  ) $
and $ bold(b) =  vec(
  integral_(x_0) ^ (x_1) f(x) dif x, 
  integral_(x_1) ^ (x_2) f(x) dif x,
  dots.v,
  integral_(x_(N-1)) ^ (x_N) f(x) dif x,
)
$

= FEM for PDEs II



== Well-posedness

#definition[ A PDE problem is well-posed if
- A unique solution exists. 
- Continuous dependence (small changes in the problem lead to small changes in the solution).]


Main idea: if the weak form is well-posed (by L-M Theorem) and the data is regular, then the strong form is also well-posed and the solution to the weak form also solves the strong form.

== Lax-Milgram Theorem 

#theorem(name: "Lax-Milgram Theorem")[Let $V$ be a Hilbert space, $b(dot.c, dot.c)$ a bi-linear form of $V times V$, and $l(dot.c)$ a linear function on $V$. Assume: 

$ 
|b(w, v)| <= c_b || w || _V || v || _V quad & forall w, v in V \
|l(v)| <= c_l || v || _V quad & forall v in V \
b(w, w) >= alpha || w || ^2 _V quad & forall w in V
$

for some $c_b, c_l, alpha$.
Then the following problem has a unique solution (with continuous dependence):

- Find $u in V$ such that $b(u, v) = l(v)$ for all $v in V$.]

The proof is omitted. 

== Hilbert space

A Hilbert space is a complete inner product (linear vector) space.

An inner product space is written as $V, (dot.c, dot.c)_V$ where $V$ is a linear vector space and $(dot.c, dot.c)_V$ is a inner product. The inner product induces a norm $|| dot.c || _V$ on the space.

#example[$RR^n$. $(x, y) = sum_i x_i y_i$ and $|| x || _ (RR ^ n) = sqrt(sum_i x_i^2)$.]

#example[$L^2(Omega)$. $(f, g) = integral_Omega f g  dif x$ and $|| f || _(L^2(Omega)) = sqrt(integral_Omega f^2 dif x)$.]

== Poincare-Friedrichs inequality
#theorem(name: "Poincare-Friedrichs inequality")[
There is a $c_"PF" > 0$ such that $ || w ||_(L^2(Omega)) <= c_"PF" || w' ||_(L^2(Omega)) $ for any $w in H_0^1(Omega)$.]

#corollary[$ || w' ||_(L^2(Omega))^2 <=  || w' ||_(L^2(Omega))^2 + || w ||_(L^2(Omega))^2  <= (1 + c^2_"PF") || w' ||_(L^2(Omega))^2 $
where $|| w' ||_(L^2(Omega))^2 + || w ||_(L^2(Omega))^2 = || w || _(H^1(Omega))^2$. Then $|| w' ||_(L^2(Omega))^2$ is an equivalent norm on $H^1(Omega)$ and thus on $H_0^1(Omega)$.]

== Main example

#example(name: "Weak form")[ Given $f in L^2(Omega)$. Find $u in H_1^0(Omega)$ such that 
$ integral_0^1 u' v' dif x = integral_0 ^1 f v dif x  $
for any $v in H_0^1(Omega)$.

Here $b(u, v) = integral_0^1 u' v' dif x$ and $l(v) = integral_0 ^1 f v dif x$. This problem is well-posed.]

#proof[
We prove that the problem is well-posed by Lax-Milgram Theorem. 
- $V = H_0^1(Omega)$ is a Hilbert space, with inner product $(w, v)_V = integral_0^1 w' v' dif x$ and induced norm $|| w || _V = sqrt(integral_Omega (w')^2 dif x) $.
- Cauchy-Schwartz inequality with $c_b = 1$.
- Cauchy-Schwartz inequality and PF inequality (to go from $L^2(Omega)$ norms to $V$ norms).
- Trivial.
Thus the problem is well-posed.
]

== Convergence of FEM

#lemma(name: "Galerkin orthogonality")[
  $ into (u' - u_h')v_h' dx = 0 $
  for all $v_h in V_h$.
]
#proof[
  Take $v = v_h in V_h subset V$ in the weak form:
  $ into u'v_h' dx = into f v_h dx $
  Also we have the Galerkin discretization:
  $ into u_h' v_h' dx = into f v_h dx $
  Subtracting second equation from the first gives the result. 
]

#theorem(name: "A priori error analysis")[$ ||u - u_h|| _V = || u' - u_h' || _#lebs <= || u' - v_h' || _#lebs = ||u - v_h|| _V $ for any $v_h in V_h$. This implies that $u_h$ is the best possible approximation for $u$ in $V_h$.]

#proof[
  Applying the above lemma twice (the first time with $u_h = v_h$) and use C-S inequality: 
  $ 
    norm(u' - u_h')_lebs^2 &= into (u' - u_h') (u' - u_h') dx \
    &= into (u' - u_h') u' dx \
    &= into (u' - u_h') (u' - v_h') dx \
    &<= norm(u' - u_h')_lebs norm(u' - v_h')_lebs
  $

  Thus $norm(u' - u_h')_lebs <= norm(u' - v_h')_lebs$.
]

#corollary[
  $ || u' - u_h' || _#lebs <= C h $ for some constant $C$.
]

#proof[
  Take $v_h$ as the linear interpolant of $u$.
]

The corollary implies that as $h -> 0$, $u_h -> u$ and the order of convergence is linear.

== Intermezzo

$ C^oo(Omega) = {phi.alt: Omega -> RR |  phi.alt, phi.alt', phi.alt'', dots "are continuous"} $ 

$ C^oo_0(Omega) = {phi.alt: Omega -> RR | phi.alt, phi.alt', phi.alt'', dots "are continuous and 0 on the boundary"} $

#definition(name: "Weak derivative")[
  $v in #lebs$ has a weak derivative when there is $w in #lebs$ such that $ integral_Omega w phi.alt dif x = integral_Omega - v phi.alt' dif x $ for any $phi.alt in C_0^oo (Omega)$ (where $phi.alt'$ is the classical derivative of $phi.alt$). Then we define $v'$ (the _weak derivative_ of $v$) as $w$.
]
Not every function has a weak derivative. 

#example(name: "Main trivial example")[
  Assume $v in C^1(overline(Omega))$. Then $ integral_Omega v' phi.alt dif x = integral_Omega - v phi.alt' dif x + v phi.alt  ]_0 ^ 1 = integral_Omega - v phi.alt' dif x $ for any $phi.alt in C_0^oo (Omega)$. Thus the weak derivative of $v$ is the classcial derivative. 
]

#example(name: "Main non-trivial example")[Let $ v(x) = cases(2x quad x in [0, 1/2], 2 - 2x quad x in [1/2, 1]) $ 
Then $ w(x) = cases(2 quad x in (0, 1/2), -2 quad x in (1/2, 1)) $
The value of $w$ at $x = 1/2$ is arbitrary.
]

#example[The solution to the weak form also solves the strong form, assuming $f in C(overline(Omega))$.]

#proof[Given $ integral_Omega u' phi.alt' dif x = integral_Omega f phi.alt dif x $ for all $phi.alt in H_0^1(Omega) supset C_0^oo(Omega) $. Hence $u'$ has weak derivative $u'' = -f in L^2 (Omega)$. Next, assume $f in C(overline(Omega)) subset #lebs$, then $u'' in C(overline(Omega))$ and thus $u in C^2(overline(Omega))$. Thus $-u''(x) = f(x)$ for all $x in Omega$.]


= FEM for PDEs III: PDE extensions
== Poisson problem 
#definition(name: "Laplacian")[$ Delta = nabla dot.c nabla = diff^2/(diff^2 x) + diff^2/(diff^2 y) = (dot.c)_(x x) + (dot.c)_(y y) $]
Let $Omega in RR^2$ be an open subset. The _Poisson problem_ is solving $ -Delta u = f $ in $Omega$, subject to $u = 0$ on $diff Omega$. 

Weak form. Find $u in H_0^1(Omega)$ such that $ integral_Omega nabla u dot.c nabla v dif x = integral_Omega f v dif x $ for all $v in H_0^1(Omega)$.

We define 
$ #lebs = { v: Omega -> RR | norm(v)_#lebs < oo } $
$ H^1(Omega) = {v in #lebs | v_x, v_y in #lebs} $
$ H_0^1(Omega) = {v in H^1(Omega) | v = 0 "on" diff Omega} $

== Galerkin FEM method for triangulations

 
#list(
  [Mesh for $Omega$: triangulation.],
  [
    Galerkin FEM ($U_h = V_h$). Define 
    $ V_h = {w_h: Omega -> RR | w_h "is continuous", w_h = 0 "on" diff Omega, w_h | _T in PP^1(T) quad  forall T "in mesh"} $
    ($w_h(x, y) = c_0 + c_1 x + c_2 y$ for $(x, y) in T$), which is the set of continuous piecewise-linear functions defined on $Omega$ that vanish on $diff Omega$.  Find $u_h in V_h$ such that 
    $ integral_Omega nabla u_h dot.c nabla v_h dif x = integral_Omega f v_h dif x $ for any $v_h in V_h$.
  ],
  [
    Basis of hat-functions (2-D). 
  $ phi_j(bold(x)) = cases(
    1 quad bold(x) = bold(x)_j, 
    0 quad bold(x) = bold(x)_i "where" i != j,
    "linearly interpolated elsewhere"
    ) $
  ],
  [
    $V_h = "span"{phi_j}_(j=1)^N$ and $u_h = sum_(j=1)^N u_j phi_j$ where $u_j$ are coeffients. Pick $v_h = phi_i$ for all $i = 1, dots, N$ to obtain $A bold(u) = bold(b)$, where 
    $ A_(i j) = integral_Omega nabla phi_j dot.c nabla phi_i dif x $ and 
    $ b_i = integral_Omega f phi_i dif x $
  ]
)

#example[
  $ u_t - u_(x x) = f $ for all $(t, x) in (0, T) times Omega$, where $Omega  = (0, 1)$. 
  - Initial condition: $u(0, x) = u_0(x)$ for all $x in Omega$.
  - Boundary condition: $u(t, 0) = u(t, 1) = 0$ for all $t in (0, T)$.
]

#proof[
  Write the weak form: 
  $ integral_Omega u_t v dif x + integral_Omega u_x v_x dif x = integral_Omega f v dif x $ for all $v$ such that $v(t, 0) = v(t, 1) = 0$. Also $ u_h(t, x) = sum_(j=1)^(N-1) u_j(t) phi_j(x) $

  Take $v = phi_i$ for all $i = 1, dots, N-1$, we have
  $ M bold(dot(u))(t) + K bold(u)(t) = bold(b)(t) $
  where 
  $ M_(i j) = integral_Omega phi_j phi_i dif x$, $K_(i j) = into phi_j' phi_i' dx  $, and $b_i(t) = into f(t, x) phi_i(x) dx$.
]

= Linear Systems: Advanced Methods I 

== Problem 

Given $A in RR ^ (n times n), bold(b) in RR^n$. Assume there exists $bold(x) in RR^n$ such that $A bold(x) = bold(b)$. Given $hat(bold(x))$, an approximation to $bold(x)$, estimate the upper bound for the error $norm(bold(x) - bold(hat(x)))$. 

Main idea: use $bold(r) = bold(b) - A bold(hat(x))$ and $norm(bold(r))$.

== Vector norms and matrix norms

#definition[
  A _vector norm_ on $RR^n$ is a function $RR^ n -> RR$ with: 
  - $norm(bold(x)) >= 0$,
  - $norm(bold(x)) = 0$ if and only if $bold(x) = bold(0)$,
  - $norm(alpha x) = |alpha| norm(bold(x))$,
  - $norm(bold(x) + bold(y)) <= norm(bd(x)) + norm(bd(y))$.
]

#definition[
  A _matrix norm_ on $RR^(n times n)$ is a function $RR^(n times n) -> RR$ with: 
  - $norm(A) >= 0$,
  - $norm(A) = 0$ if and only if $A = O$,
  - $norm(alpha A) = |alpha| norm(A)$,
  - $norm(A+B) <= norm(A) + norm(B)$,
  - $norm(A B) <= norm(A) norm(B)$.
]

#definition[
  The induced/subordinate/natural matrix norm is defined as 
  $ norm(A)
  =max_(bd(x) != bd(0)) (norm(A bd(x)))/ (norm(bd(x)))
  =max_(norm(bd(x)) = 1) norm(A bd(x)) $
]

#example[ Let 
  $ A = mat(1, 1/3; 1/3, 1) $
  We now compute $norm(A)_2$. Take $bd(x) = vec(a, b) != bd(0)$, then 
  $ A bd(x) = vec(a + b/3, a/3 + b)$. Then
  $ (norm(A bd(x)) / norm(bd x)) ^2  = (10/9 (a² + b²) + 4/3 a b) / (a² + b²) = 10/9 + 2/3 (2a b) / (a² + b²) <= 10/9 + 2/3 = 16 / 9 $
  The maximum value is taken when $a = b$. Thus 
  $ norm(A)_2 = 4/3 $
]

#theorem[
  $ norm(A bd(x)) <= norm(A) norm(bd(x)) $
]
#definition[
  For a square matrix $A$,
  $ kappa(A)=norm(A) norm(A^(-1)) $ is the _condition number_ of $A$.
]

#theorem[
  (i).
  $ norm(bd(x) - bd(hat(x))) <= norm(A^(-1)) norm(hat(bd(r))) $ 
  (ii). For any $bd(x) != bd(0)$,
  $ norm(bd(x) - bd(hat(x))) / norm(bd(x)) <= kappa(A) norm(bd(hat(r))) / norm(bd(b)) $
]

#proof[
  (i).
  $ 
    norm(bd(x) - bd(hat(x))) 
    &= norm(A^(-1)bd(b) - bd(hat(x))) \
    &= norm(A^(-1) hat(bd(r))) \
    &<= norm(A^(-1)) norm(hat(bd(r)))
  $
  (ii).
  $
    norm(bd(b)) = norm(A bd(x)) <= norm(A) norm(bd(x))
  $
  Thus 
  $
    1 / norm(bd(x)) <= norm(A) / norm(bd(b))
  $
  for any $bd(x) != bd(0)$.
  Thus
  $
    norm(bd(x) - bd(hat(x))) / norm(bd(x)) <=norm(A) norm(A^(-1)) norm(bd(hat(r))) / norm(bd(b))  = kappa(A) norm(bd(hat(r))) / norm(bd(b))
  $

]


#lemma[
  For a symmetric matrix $A in RR^(n times n)$, the eigenvalues are real and we can choose a set of orthonormal eigenvectors that span $RR^n$.
]

#definition[
  A matrix $B in RR^(n times n)$ is _positive definite_ if $bd(x)^t B bd(x) > 0$ for any $bd(x) != bd(0)$.
]

#lemma[
  The eigenvalues of a positive definite matrix are positive. 
]
#definition[
  For a square matrix $A$,
  $rho(A) = max_k | lambda_k |$ where $lambda_k$ are eigenvalues of $A$.
]
#theorem[
  $
    norm(A)_2 = sqrt( rho (A^t A))
  $
]

#proof[
  $A^t A$ is symmetric and positive definite. Thus the eigenvalues $mu_j$ of $A^t A$ are positive and we can choose a set of orthonormal eigenvectors $bd(w)_j$ that span $RR ^ n$, where 
  $ A^t A bd(w)_j  = mu_j bd(w)_j $
  and $bd(w)_j dot.c bd(w)_k = delta_(j k)$. For any $bd(x) in RR^n$, $bd(x) = sum_(j=1)^n x_j bd(w)_j$ for some $x_j$.

  Then $ norm(A)_2^2 &= max_(norm(bd(x)) = 1) bd(x)^t A^t A bd(x) \
  &= max_(norm(bd(x)) = 1) (sum_(i=1)^n x_i bd(w)^t_i) A^t A (sum_(j=1)^n x_j bd(w)_j) \
  &= max_(norm(bd(x)) = 1) (sum_(i=1)^n x_i bd(w)^t_i)(sum_(j=1)^n x_j mu_j bd(w)_j) \
  &= max_(norm(bd(x)) = 1) sum_(i=1)^n sum_(j=1)^n x_i x_j  mu_j bd(w)^t_i bd(w)_j \
  &= max_(norm(bd(x)) = 1) sum_(i=1)^n x_i^2 mu_i \
  &<= max_(norm(bd(x)) = 1) sum_(i=1)^n x_i^2 max_j |mu_j| \
  &= max_j |mu_j|
  $ 
]

#theorem(name: "Perturbation Theorem")[
  Let $A bd(x) = bd(b)$ and $(A + delta A) hat(bd(x)) = bd(b) + delta bd(b)$, where $delta A$ and $delta bd(b)$ are perturbations. Then 
  $ norm(bd(x) - hat(bd(x))) / norm(bd(x))) <= C (norm(delta bd(b)) / norm(bd(b)) + norm(delta A) / norm(A) ) $
  where small $delta A$ is assumed: $norm(delta A) < 1/norm(A^(-1))$.
]

#proof[
  TODO
]

= Linear Systems: Advanced Methods II

#definition[
  $Q in RR^(n times n)$ is said to be an _orthognal_ matrix when $Q^t Q = I$.
]

#theorem[
  Let $A in RR^(n times n)$. Then there exist an orthognal matrix $Q in RR^(n times n)$ and an upper triangular matrix $R in RR^(n times n)$ such that $A = Q R$.
]

#corollary[
  If $A bd(x) = bd(b)$, then $R bd(x) = Q^t bd(b)$, which can be solved using backwards substitution.
]

TODO

= Linear Systems: Advanced Methods III

Problem: $A bd(x) = bd(b)$ where $A in RR^(n times n)$ and $A$ is SPD (symmetric positive definite).

== Stationary iterative methods

$ bd(x)_(k+1) = T bd(x)_k + bd(c) $ where $rho(T) < 1$ and $bd(x)_k -> bd(x)$ as $k -> oo$. Note that $T$ is fixed here for all $k$. 

Writing $A = D - L - U$ and we have the Jacobi method with 
$ T &= D^(-1) (L+U) \ bd(c) &= D^(-1) bd(b) $

and Gauss-Seidel method with 
$ T&=(D-L)^(-1) U  \ bd(c) &= (D - L)^(-1) bd(b) $

== Non-stationary methods

=== Steepest-descent method
$ bd(x)_(k+1) = bd(x)_k + alpha_k bd(r)_k $

where $bd(r)_k = bd(b) - A bd(x)_k$ and $bd(r)_k dot.c bd(r)_(k+1) = bd(r)_k^t (bd(b) - A bd(x)_(k+1)) = 0$. Therefore $ alpha_k = (bd(r)^t_k bd(r)_k) / (bd(r)^t_k A bd(r)_k) $

=== The CG method

Let $ bd(x)_k = bd(x)_0 + sum_(i=0)^(k-1) alpha_i bd(p)_i $ with ${bd(p)_i}$ are conjugate directions $ bd(p)_j^t A bd(p)_i = 0 $ for any $i != j$. Equivalently, $ bd(x)_(k+1) = bd(x)_k + alpha_k bd(p)_k $

Denote $bd(r)_k = b - A bd(x)_k$. Then we want $ bd(p)_j dot.c bd(r)_k = bd(p)_j^t (bd(b) -  A bd(x)_k) = 0 $ for all $j = 0, dots, k - 1$. Then $ alpha_j = (bd(p)_j^t bd(r)_0) / (bd(p)_j^t A bd(p)_j) $

Compute conjugate directions: $A$-orthogonal Gram-Schmidt:

$ bd(p)_k = bd(r)_k - sum_(i=0)^(k-1) c_(k i) bd(p)_i $

where $ c_(k i) = (bd(p)_i^t A bd(r)_k) / (bd(p)_i^t A bd(p)_i ) $ are obtained from the constraint of conjugate directions.


=== Minimisation of $A$-norm of the error

#definition(name: [$A$-norm])[
  $ norm(bd(x))_A = sqrt(bd(x)^t A bd(x)) $
]
#definition(name: ["Krylov" subspace])[
  $ cal(K)_k = "span"{bd(p)_0, dots, bd(p)_(k-1)} = "span"{bd(r)_0, dots, bd(r)_(k-1)} $
  
]
#theorem[
  Let $bd(x)_k$ be given by the CG method applied to $A bd(x) =bd(b)$ with $bd(x)_0  = bd(0)$. Assume the $k$-th step  is not yet converged, namely $bd(r)_(k-1) != bd(0)$, then $bd(x)_k$ is the unique minimiser in $cal(K)_k$ of $norm(bd(x) - bd(x)_k) _ A$. 
]

#proof[
  Consider an arbitrary $bd(y) in cal(K)_k$ and $bd(y) = bd(x)_k -  bd(delta x)$. Let $bd(e) = bd(x) - bd(y) = bd(x) - bd(x)_k + bd( delta  x)$. Let $bd(e)_k = bd(x) - bd(x)_k$, then $bd(e) = bd(e)_k +  bd(delta x)$.
  Then $ norm(bd(e))_A^2 &= (bd(e)_k + bd(delta x))^t A (bd(e)_k + bd(delta x)) \
  &= bd(e)_k^t A bd(e)_k + bd(delta x)^t A bd(e)_k + bd(e)_k^t A bd(delta x) + bd(delta x)^t A bd(delta x) \
  &= bd(e)_k^t A bd(e)_k + bd(delta x)^t A bd(delta x)
  $
  which is minimised exactly when $bd(delta x) = bd(0)$ since $A$ is positive definite. (Note that $bd(delta x) in cal(K)_k$, $bd(r)_k^t bd(p)_j = 0$ for all $j = 0, dots, k - 1$ and $A = A^t$.)
]

#theorem[
  Assume $bd(r)_k != 0$, then $bd(p)_k != 0$.
]
#proof[
  $ bd(p)_k^t bd(r)_k = bd(r)_k^t bd(r)_k - sum_(i=0)^(k-1) c_(k i) bd(p)_i^t bd(r)_k = bd(r)_k^t bd(r)_k $
]

#corollary[
  The CG method converges in at most $n$ steps. 
]
#proof[
  $dim cal(K)_n = n$ and therefore $cal(K)_n = RR^n$. Thus $bd(x)_n = bd(x)$.
]

#theorem[
  When $n$ is large,
  $ (norm(bd(e)_k)_A) / (norm(bd(e)_0)_A) <= 2 ((sqrt(kappa) - 1) / (sqrt(kappa) + 1))^k -> abs(1 - 2 / sqrt(kappa)) $ as $k -> oo$, where $kappa = kappa(A)$ is the conditional nubmer of $A$. 
]

= Low-Rank Approximation I

== The power method, and Rayleigh quotient

Problem: Given $A in RR^(m times m)$ and $A = A^t$. Find its dominant eigenvalue-eigenvector pair $bd(v), lambda$, where $ A bd(v) = lambda bd(v) $ for the largest $abs(lambda)$.

Power method. Given $bd(v)^((0))$ where $norm(bd(v)^((0))) = 1$. For $k = 1, 2, dots$, let $ bd(w) &= A bd(v)^((k-1)) \ bd(v)^((k)) &= (bd(w))/ (norm(bd(w))) \ lambda^((k)) &= (bd(v)^((k)))^t A bd(v)^((k)) $

Suppose $|lambda_1| > |lambda_2| >= dots >= |lambda_m| >= 0 $ and let $
bd(v)^((0)) = sum_(i=1)^m a_i bd(q)_i
$
Then $
bd(v)^((k)) &= c_k A^k bd(v)^((0)) \
&= c_k ( sum_(i=1)^m a_i A^k bd(q)_i) \
&= c_k ( sum_(i=1)^m a_i lambda_i^k bd(q)_i) \
&= c_k lambda_1^k (a_1 bd(q)_1 + sum_(i=2)^m a_i (lambda_i / lambda_1)^k bd(q)_i)
$
where $c_k$ are normalising coefficients.

Since $lambda_i < lambda_1$ for all $i = 2, dots, m$, $ (lambda_i / lambda_1)^k -> 0 $ as $k -> oo$. Thus $ bd(v)^((k)) -> c_k lambda_1^k a_1 bd(q)_1 $ as $k -> oo$. But $norm(bd(v)^((k))) = norm(bd(q)_1) = 1$, thus 
$ bd(v)^((k)) -> plus.minus bd(q)_1 $ as $k -> oo$, where $c_k lambda_1^k a_1 bd(q)_1 -> plus.minus bd(q)_1$ as $k -> oo$.

Also $ lambda^((k)) -> bd(q)_1^t A bd(q)_1 = lambda_1 bd(q)_1^t bd(q)_1 = lambda_1 $

Power Rank: the dominant eigenvalue is $1$.

== The power method: Convergence analysis

#definition(name: "Rayleigh Quotient")[
  Define Rayleigh quotient of vector $bd(x)$ as $ r(bd(x)) = (bd(x)^t A bd(x)) / (bd(x)^t bd(x)) $ 
]

#lemma[
  $ nabla r =  vec(diff/(diff x_1), dots, diff / (diff x_m)) r(bd(x)) = 2 / (bd(x)^t bd(x)) (A bd(x) - r(bd(x)) bd(x)) $
]

#lemma[
  $ r(bd(y)) = r(bd(x)) + nabla r dot.c  (bd(y) - bd(x)) + O(norm(bd(y)-bd(x))^2) $
]

#theorem[
  Suppose $|lambda_1| > |lambda_2| >= dots >= |lambda_m| >= 0 $ and $bd(q)_1^t bd(v)^((0)) != 0$. Then the power method converges and $ 
    norm(bd(v)^((k)) - (plus.minus bd(q)_1)) &= O(abs((lambda_2) / (lambda_1))^k) \

    |lambda^((k)) - lambda_1|  &= O(abs((lambda_2) / (lambda_1))^(2k))

  $
  as $k -> oo$. They are both linear convergence.
]

 #proof[
   $ norm(bd(v)^((k)) -  c_k lambda_1^k a_1 bd(q)_1) = norm(c_k lambda_1^k sum_(i=2)^m a_i (lambda_i / lambda_1)^k) -> O(abs((lambda_2) / (lambda_1))^k) $
  as $k -> oo$.


   By definition,
   $r(bd(q)_1) = lambda_1 $ and $r(bd(v)^((k))) = lambda^((k))$. Thus 
   $
     lambda^((k)) - lambda_1 = r(bd(v)^((k)))  - r(bd(q)_1) = nabla r (bd(q)_1)(bd(v)^((k)) - bd(q)_1)  + O(norm(bd(v)^((k)) - bd(q)_1)^2)
   $

   But $nabla r (bd(q)_1) = 0$. Thus 
   $ |lambda^((k)) - lambda_1|  &= O(abs((lambda_2) / (lambda_1))^(2k)) $
]

== Inverse iteration

Motivation. Let $lambda$ and $bd(v)$ be a pair of eigenvalue and eigenvector of matrix $A$, then $ A bd(v) = lambda bd(v) $ Then sice $ lambda^(-1) bd(v) = A^(-1) bd(v) $ we see that $lambda^(-1)$ is an eigenvalue of $A^(-1)$ for the same eigenvector $bd(v)$. To find the eigenvalue with the smallest absolute value of $A$, we only need to find the one with the largest absolute value for $A^(-1)$. Also since for $mu != lambda$,
$ (A - mu I) bd(v) &= (lambda - mu) bd(v) \
  1/(lambda - mu) bd(v) &= (A - mu I)^(-1) bd(v)
$
To find the eigenvalue of $A$ closest to $mu$, we only need to find the eigenvalue with the largest absolute value of $B = (A - mu I)^(-1)$.

We solve a linear system instead of actually computing the inverse matrix.

#theorem[
  Suppose $lambda_J$ and $lambda_K$ are the closest and second closest eigenvalue of $A$ to $mu$ and $bd(q)_J^t bd(v)^((0)) != 0$. Then the inverse iteration method converges, with 
  $ norm(bd(v)^((0)) - bd(q)_J^t) &= O(abs( (mu - lambda_J) / (mu - lambda_K) )^k) \

  abs(lambda^((k)) - lambda_J) &= O(abs( (mu - lambda_J) / (mu - lambda_K) )^(2k))
  
   $
]