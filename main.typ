#import "template.typ": *
#import "theorem.typ": *
#import "algo.typ" : *

#set heading(numbering: "1.a.")
#let lebs = [ $L^2(Omega)$ ]
#let into = [ $integral_Omega$ ]
#let dx = [ $dif x$ ]

#let bd(term) = [ $bold(#term)$]

#let theorem = thmbox(
  "theorem",
  "Theorem",
  fill: rgb("#e8e8f8"),
)

#let lemma = thmbox(
  "theorem",
  "Lemma",
  fill: rgb("#e8e8f8"),
)

#let definition = thmbox(
  "theorem",
  "Definition",
  fill: rgb("#e8f8e8"),
)

#let example = thmbox(
  "theorem",
  "Example",
  stroke: rgb("#ffaaaa") + 1pt,
)

#let method = thmbox(
  "theorem",
  "Method",
  stroke: rgb("#aaaaff") + 1pt,
)

#let problem = thmbox(
  "theorem",
  "Problem",
  stroke: rgb("#aaffaa") + 1pt,
)

#let corollary = thmbox(
  "theorem",
  "Corollary",
  fill: rgb("#e8e8f8"),
)

// #let thm = counter("theorem")
// #let theorem(term, name: "", type: "Theorem") = block(fill: luma(240), inset: 6pt, width: 100%, radius: 2pt)[
//   *#type #thm.display()*#if name == "" {} else {[ (#name)]}. #thm.step() #term 
// ]
// #let corollary(term, name: "") = theorem(name: name, type: "Corollary")[#term]
// #let lemma(term, name: "") = theorem(name: name, type: "Lemma")[#term]
// #let example(term, name: "") = theorem(name: name, type: "Example")[#term]
// #let definition(term, name: "") = theorem(name: name, type: "Definition")[#term]


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

#outline(indent: true)

#pagebreak()

= FEM for PDEs I

== Problem statement

Let $Omega subset RR$ be an open interval. We always take $Omega =  (0, 1)$ as an example. 

#definition(name: "Sobolev spaces")[
  Define the _Sobolev spaces_
  $ H^1(Omega) &= {v : Omega -> RR | v, v' in L^2 (Omega)} \
   H_0^1(Omega) &= { v in H^1(Omega) | v(0) = v(1) = 0} \
   H_(\(0)^1(Omega) &= { v in H^1(Omega) | v(0) = 0} \
   H_(0\))^1(Omega) &= { v in H^1(Omega) | v(1) = 0} $


  where $L^2(Omega)$ is the Lebesgue space. 
]

#problem(name: "Two-point boundary value problem, strong form")[Given $f in lebs$, the _strong form_ of a _two-point boundary value problem_ is to find $u in H_0^1(Omega)$ such that 
$ -u'' = f $]


#problem(name: "Two-point boundary value problem, weak form")[
Given $f in lebs$, the _weak form_ of a _two-point boundary value problem_ is to find $u in H_0^1(Omega)$ such that for all $v in H_0^1(Omega)$
$ integral_0^1 u' v' dif x = integral_0 ^1 f v dif x  $
<weak-form>
]

#theorem[
  Any solution $u in H_0^1(Omega)$ to the strong form also solves the weak form.
]

#proof[
  Let $u$ solve the strong form. Then take any $v in H_0^1(Omega)$, we have $ -u'' v = f v $ Integrate over $Omega$ and use the boundary conditions to obtain 
$ integral_0^1 u' v' dif x = integral_0 ^1 f v dif x  $
Thus $u$ also solves the weak form.
]



== Petrov-Galerkin discretization
#problem(name: "Abstract weak form")[
  Let $U, V$ be function spaces. Given a bilinear form $b: U times V -> RR$ and a linear functional $l : V -> RR$,
 find $u in U$ such that for all $v in V$ $ b(u, v) = l(v) $
]


#method(name: "Petrov-Galerkin discretization")[
Given discrete subspaces $U_h subset U$ and $V_h subset V$ with $dim U_h = dim V_h$, find $u_h in U_h$ such that for all $v_h in V_h$ $ b(u_h, v_h) = l(v_h) $ 

This method is called _Petrov-Galerkin discretization_ and specially, when $U_h = V_h$, _Galerkin discretization_.
]

#definition(name: "Finite element mesh")[
A _finite element mesh_ is a partition of $Omega$ into non-overlapping subsets. 
]

In Petrov-Galerkin discretization, $U_h$ and $V_h$ are the span of basis functions which are defined with respect to a finite element mesh. 

#example[
Let $U_h = "span"{x, x^2}$ and $V_h = "span"{1, x}$. Then $u_h = u_1 x + u_2 x^2$  where $u_1, u_2$ are to be determined. Setting $v_h(x) = 1$ and $v_h(x) = x$ gives two equations for $u_1$ and $u_2$. We then compute $u_1$ and $u_2$ to obtain $u_h(x)$. 
]


== Finite element spaces in 1-D

Consider $Omega subset RR$ with finite element mesh $ {(x_0, x_1), (x_1, x_2), dots, (x_(N-1), x_N)} $

#definition(name: ['Hat' basis functions])[
  Define for $j = 0, 1, dots, N$, $ phi _j (x_i) = cases(1 quad "if " i = j, 0 quad "if " i != j) $
  and $phi_j$ is linearly interpolated elsewhere.
]


#definition[
  Define for $i = 1, dots, N$, $ psi_i(x) = cases(1 quad "if " x in (x_(i-1), x_i), 0 quad "otherwise") $
]

Then $U_h = "span"{ phi_j } _(j = 0) ^ N$ is the space of continuous piecewise linear polynomials, and $V_h = "span"{ psi_i } _(i = 1) ^ N $ is the space of discontinuous piecewise constant polynomials. 


#example[
  Given $f$, find $u$ such that $u' = f$ for $x in (0, 1)$ and $u(0) = 0$.
]

#proof[
  Multiply $v$ on both sides of $u' = f$ and integrate over $[0, 1]$, we see that 
  $ integral_0^1  f v dx = integral_0^1 u' v dx =  [u v ]_0^1 - integral_0^1 u v' dx $

  We now derive two weak forms.

  #list(
    block(width: 100%)[  A weak form where no $v'$ appear: find $u in H_(\(0)^1(Omega)$ such that $ integral_0^1  f v dx = integral_0^1 u' v dx $ for any $v in L^2(Omega)$.],
    [  A weak form where no $u'$ appear: find $u in lebs$ such that $ integral_0^1  f v dx =  - integral_0^1 u v' dx  $ for any $v in  H_(0\))^1(Omega)$.]
  )
  We now apply Petrov-Galerkin discretization to the first weak form: find $u_h in U_h subset U = H_(\(0)^1$ such that 
  $ integral_0^1  f v_h dx = integral_0^1 u_h' v_h dx $
  for any $v_h in V_h subset V = lebs$.

  With a finite element mesh of $N$ intervals, we define $U_h = "span"{phi_j : j = 1, 2, dots, N}$. 
  // Note that $phi_0$ is not included since $u(0) = 0$. 
  Thus $ u_h = sum_(j=1)^N u_j phi_j(x) $ for $u_j in RR$, $j = 1, dots, N$. We define $V_h = "span"{psi_i : i = 1, dots, N}$ and pick $v_h = psi_i$ for $i = 1, dots, N$.

  

  We now need to find $bd(u) = vec(u_1, dots, u_N) in RR^N$ such that 
  $ sum_(j=1)^N u_j integral_0^1 phi_j'(x) psi_i(x) dx = integral_0^1 f(x) psi_i(x) dx $

  Define $A in RR^(N times N)$ where $ A_(i, j) = integral_0^1 phi_j'(x) psi_i(x) dx = cases(1 &"if " i = j, -1  &"if " i = j + 1, 0 &"otherwise") $ and $bd(b) in RR^N$ where 

  $ b_i = integral_0^1 f(x) psi_i(x) dx = integral_(x_(i-1))^(x_i) f(x) dx $

  Then the problem is reduced to solving an algebraic system $A bold(u) = bold(b)$, where $ A = mat(
  1, 0, 0, ..., 0; 
  -1, 1, 0, ..., 0;
  0, -1, 1, ..., 0;
  0, 0, -1, ..., 0;
  dots.v, dots.v, dots.v, dots.down, dots.v;
  0, 0, 0, ..., 1
  ) quad "and" quad bold(b) =  vec(
  integral_(x_0) ^ (x_1) f(x) dif x, 
  integral_(x_1) ^ (x_2) f(x) dif x,
  dots.v,
  integral_(x_(N-1)) ^ (x_N) f(x) dif x,
)
$
]
#pagebreak()


= FEM for PDEs II


== Hilbert space
#definition(name: [Inner product space])[
An inner product space is written as $(V, angle.l dot.c, dot.c angle.r _V)$ where $V$ is a linear vector space over $RR$ and $angle.l dot.c, dot.c angle.r _V : V times V -> RR$ is a inner product. The inner product induces a norm $|| dot.c || _V$ on the space. 
]

#definition(name: [Hilbert space])[
  A _Hilbert space_ is a complete inner product space.
]



#example(name: $RR^n$)[$angle.l x, y angle.r = sum_i x_i y_i$ and $|| x || _ (RR ^ n) = sqrt(sum_i x_i^2)$.]

#example(name: $L^2(Omega)$)[$angle.l f, g angle.r = integral_Omega f g  dif x$ and $|| f || _(L^2(Omega)) = sqrt(integral_Omega f^2 dif x)$.]

== Well-posedness

#definition(name: "Well-posedness")[ A PDE problem is _well-posed_ if
- a unique solution exists and
- it satisfies continuous dependence (small changes in the problem lead to small changes in the solution).]


Main idea: if the weak form is well-posed (usually by the following Lax-Milgram Theorem) and the data is regular, then the strong form is also well-posed and the solution to the weak form also solves the strong form.


#theorem(name: "Lax-Milgram Theorem")[Let $V$ be a Hilbert space, $b(dot.c, dot.c): V times V -> RR$ a bilinear form, and $l(dot.c) : V -> RR$ a linear functional. Assume: 

$ 
|b(w, v)| <= c_b || w || _V || v || _V quad & forall w, v in V  quad &"Continuity of " b \
|l(v)| <= c_l || v || _V quad & forall v in V  &"Continuity of " l\
b(w, w) >= alpha || w || ^2 _V quad & forall w in V &"Coercivity"
$

for some $c_b, c_l, alpha > 0$.
Then the following problem is well-posed:

- Find $u in V$ such that $b(u, v) = l(v)$ for all $v in V$.]


// == Poincare-Friedrichs inequality


#theorem(name: "Poincare-Friedrichs inequality")[
For all $w in H_0^1(Omega)$, there exists $c_"PF" > 0$ such that $ || w ||_(L^2(Omega)) <= c_"PF" || w' ||_(L^2(Omega)) $]


#corollary[
  $ || w || _(H^1(Omega)) =  sqrt(|| w' ||_(L^2(Omega))^2 + || w ||_(L^2(Omega))^2) $ and $|| w' || _(lebs)$ are equivalent norms on $H^1(Omega)$ and thus on $H_0^1(Omega)$.]

#proof[
  By Poincare-Friedrichs inequality,
  $ || w' ||_(L^2(Omega))^2 <=  || w' ||_(L^2(Omega))^2 + || w ||_(L^2(Omega))^2  <= (1 + c^2_"PF") || w' ||_(L^2(Omega))^2 $

  Taking the square root yields the result.
]

// == Main example

#example[#thmref(<weak-form>)[The weak form defined in Problem] is well-posed.]

#proof[
  Here $b(u, v) = integral_0^1 u' v' dif x$ and $l(v) = integral_0 ^1 f v dif x$. 

  $V = H_0^1(Omega)$ with inner product $angle.l w, v angle.r_V = integral_0^1 w' v' dif x$ is a Hilbert space with induced norm $ || w || _V = sqrt(integral_Omega (w')^2 dif x) $

#list(
  [Clearly $b(u, v) = integral_0^1 u' v' dif x = angle.l u, v angle.r _ V$ is bi-linear and $l(v) =integral_0 ^1 f v dif = angle.l f, v angle.r _ lebs $ is linear. ],
  [Continuity of $b$:  For all $u, v in V$, by Cauchy-Schwartz inequality on $V$, 
    $ |b(u, v)| = |angle.l u, v angle.r_V| <= norm(u)_V norm(v)_V $
    Thus we can take $c_b = 1$.],
      [Continuity of $l$: For all $v in V$, 

    $ |l(v)| = |angle.l f, v angle.r_lebs | <= norm(f)_lebs norm(v)_lebs <= norm(f)_lebs (c_"PF" norm(v')_lebs) = (c_"PF" norm(f)_lebs)  norm(v)_V $
    The first inequality is due to Cauchy-Schwartz inequality on $lebs$ and the second is due to Poincare-Friedrichs inequality. Thus we can take $c_l = c_"PF" norm(f)_lebs$.
  ],
  [
    Coersivity of $b$: For all $w in V$,
    $ b(w, w) = angle.l w, w angle.r_V = norm(w)_V^2 $
    Thus we can take $alpha=1$.],
)
By Lax-Milgram Theorem, the problem is well-posed.
]

== Weak derivative

#definition[
  $ C^oo(Omega) &= {phi.alt: Omega -> RR |  phi.alt, phi.alt', phi.alt'', dots "are continuous"} \ C^oo_0(Omega) &= {phi.alt: Omega -> RR | phi.alt, phi.alt', phi.alt'', dots "are continuous and 0 on the boundary"} $
]


#definition(name: "Weak derivative")[
  Let $v in #lebs$. If for all $phi.alt in C_0^oo (Omega)$, there exists $w in #lebs$ such that $ integral_Omega w phi.alt dif x = integral_Omega - v phi.alt' dif x $ where $phi.alt'$ is the classical derivative of $phi.alt$, then we define  the _weak derivative_ of $v$ as $w$.
]
Not every function has a weak derivative. 

#example(name: "Main trivial example")[
  Assume $v in C^1(overline(Omega))$. Then $ integral_Omega v' phi.alt dif x = integral_Omega - v phi.alt' dif x + [v phi.alt  ]_0 ^ 1 = integral_Omega - v phi.alt' dif x $ for any $phi.alt in C_0^oo (Omega)$. Thus the classical derivative of $v$ is its weak derivative. 
]

#example(name: "Main non-trivial example")[Let $ v(x) = cases(2x quad x in [0, 1/2], 2 - 2x quad x in [1/2, 1]) $ 
Then $ w(x) = cases(2 quad x in (0, 1/2), -2 quad x in (1/2, 1)) $ is the weak derivative of $v$.
The value of $w$ at $x = 1/2$ is arbitrary.
]

#example[The solution to the weak form also solves the strong form, assuming $f in C(overline(Omega))$.]

#proof[Given $ integral_Omega u' phi.alt' dif x = integral_Omega f phi.alt dif x $ for all $phi.alt in H_0^1(Omega) supset C_0^oo(Omega) $. Hence $u'$ has weak derivative $u'' = -f in L^2 (Omega)$. Next, assume $f in C(overline(Omega)) subset #lebs$, then $u'' in C(overline(Omega))$ and thus $u in C^2(overline(Omega))$. Thus $-u''(x) = f(x)$ for all $x in Omega$.]


== Convergence of FEM

#lemma(name: "Galerkin orthogonality")[For all $v_h in V_h$,
  $ angle.l u - u_h, v_h angle.r_V =  into (u' - u_h')v_h' dx = 0 $
]
#proof[
  Take $v = v_h in V_h subset V$ in the weak form:
  $ into u'v_h' dx = into f v_h dx $
  Also we have the Galerkin discretization:
  $ into u_h' v_h' dx = into f v_h dx $
  Subtracting second equation from the first gives the result. 
]

#lemma(name: "Interpolation error estimate")[
  Given $w in H^2(Omega)$, let $I_h(w) in V_h$ denote the linear interpolant of $w$ on the finite element mesh, namely for $i = 0, 1, dots, N$,
  $ I_h(w)(x_i) = x_i $
  Then there exists $C > 0$ such that 
  $ norm(w' - I_h(w)')_lebs <= C h $
]

#proof[
  Define for $x in Omega$, $ e(x) = w(x) - I_h(w)(x) $
  Fix $i in {1, dots, N}$. Since $e(x_(i-1)) = e(x_i) = 0$, by Rolle's Theorem, there exists $xi_i in (x_(i-1), x_i)$ such that $e'(xi_i) = 0$.
  For $x in (x_(i-1), x_i)$, $ |e'(x)| = |e'(xi_i) + integral_(xi_i)^x e''(t) dif t | = |integral_(xi_i)^x w''(t) dif t| <= sqrt(h) sqrt(integral_(x_(i-1))^(x_i) (w''(t))^2 dif t) $
  by C-S inequality. Then

  $ norm(e')^2_lebs &= sum_(i=1)^N integral_(x_(i-1))^(x_i) (e'(x))^2 dif x \
  &<= sum_(i=1)^N integral_(x_(i-1))^(x_i) (h integral_(x_(i-1))^(x_i) (w''(t))^2 dif t) dx \ 
  &= sum_(i=1)^N h^2 (integral_(x_(i-1))^(x_i) (w''(t))^2 dif t) \
  &= h^2 norm(w'')^2_lebs 
  $

  where we take $C^2 = norm(w'')^2_lebs $. Taking the square root yields the result.
]
#theorem(name: "A priori error analysis")[For all $v_h in V_h$, 
// $ ||u - u_h|| _V = || u' - u_h' || _#lebs <= || u' - v_h' || _#lebs = ||u - v_h|| _V $
$ ||u - u_h|| _V  <=  ||u - v_h|| _V $

This implies that $u_h$ is the best possible approximation for $u$ in $V_h$.]

// #proof[

//   $ 
//     norm(u' - u_h')_lebs^2 &= into (u' - u_h') (u' - u_h') dx \
//     &= into (u' - u_h') u' dx \
//     &= into (u' - u_h') (u' - v_h') dx \
//     &<= norm(u' - u_h')_lebs norm(u' - v_h')_lebs
//   $

//   Thus $norm(u' - u_h')_lebs <= norm(u' - v_h')_lebs$.
// ]

#proof[
  Apply Galerkin orthogonality twice (the first time with $u_h = v_h$) and use C-S inequality: 
  $
    norm(u - u_h)_V^2 &= angle.l u - u_h, u - u_h angle.r_V \
    &= angle.l u - u_h, u angle.r_V - angle.l u - u_h,  u_h angle.r_V - angle.l u - u_h,  v_h angle.r_V \
    &= angle.l u - u_h, u - v_h angle.r_V \
    &<= norm(u-u_h)_V norm(u-v_h)_V
  $

  Cancelling $norm(u - u_h)_V$ on both sides gives the result. 
]

#corollary[
  There exists $C > 0$ such that $ || u' - u_h' || _#lebs <= C h $ 
]

#proof[
  Take $v_h$ as the linear interpolant of $u$ in the previous theorem.
]

The corollary implies that as $h -> 0$, $u_h -> u$ and the order of convergence is linear.

#pagebreak()

= FEM for PDEs III
== Poisson problem 
#definition(name: "Laplacian")[$ Delta = nabla dot.c nabla = diff^2/(diff^2 x) + diff^2/(diff^2 y) = (dot.c)_(x x) + (dot.c)_(y y) $]

Let $Omega subset RR^2$ be an open subset.

#definition[
$ #lebs &= { v: Omega -> RR | norm(v)_#lebs < oo } \
 H^1(Omega) &= {v in #lebs | v_x, v_y in #lebs} \
 H_0^1(Omega) &= {v in H^1(Omega) | v = 0 "on" diff Omega} $
]

#problem(name: "Poisson problem, strong form")[
Given $f in lebs$, find $u in H_0^1(Omega)$ such that $ -Delta u = f $ 
]

#problem(name: "Poisson problem, weak form")[
Given $f in lebs$, find $u in H_0^1(Omega)$ such that for all $v in H_0^1(Omega)$, $ integral_Omega nabla u dot.c nabla v dif x = integral_Omega f v dif x $ 
]


== Galerkin FEM method for triangulations

#definition[
  A _2-D mesh_ for $Omega$ is a triangulation of $Omega$.
]

#definition(name: [2-D hat basis functions])[
  $ phi_j(bold(x)) = cases(
    1 quad bold(x) = bold(x)_j, 
    0 quad bold(x) = bold(x)_i "where" i != j,
    "linearly interpolated elsewhere"
    ) $
]
#method(name: [Galerkin FEM])[
    Define $U_h = V_h = "span"{phi_j}_(j=1)^N$. Then 
    $ V_h = {w_h: Omega -> RR | w_h "is continuous", w_h = 0 "on" diff Omega, lr(w_h |) _T in PP^1(T) quad  forall T "in mesh"} $
    where $lr(w_h |) _T in PP^1(T)$ is equivalent to $w_h(x, y) = c_0 + c_1 x + c_2 y$ for $(x, y) in T$. In other words, $V_h$ the set of continuous piecewise-linear functions defined on $Omega$ that vanish on $diff Omega$. 
    
    Now, find $u_h in V_h$ such that for all $v_h in V_h$,
    $ integral_Omega nabla u_h dot.c nabla v_h dif x = integral_Omega f v_h dif x $ 

     $u_h = sum_(j=1)^N u_j phi_j$ where $u_j$ are coeffients. Pick $v_h = phi_i$ for all $i = 1, dots, N$ to obtain $A bold(u) = bold(b)$, where 
    $ A_(i j) = integral_Omega nabla phi_j dot.c nabla phi_i dif x quad "and" quad b_i = integral_Omega f phi_i dif x $
]


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

#pagebreak()

= Linear Systems: Advanced Methods I 

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
  The _induced/subordinate/natural_ matrix norm for a given vector norm is defined as 
  $ norm(A)
  =max_(bd(x) != bd(0)) (norm(A bd(x)))/ (norm(bd(x)))
  =max_(norm(bd(x)) = 1) norm(A bd(x)) $
]

#example[ Let 
  $ A = mat(1, 1/3; 1/3, 1) $
  We now compute $norm(A)_2$. Take $bd(x) = vec(a, b) != bd(0)$, then 
  $ A bd(x) = vec(a + b/3, a/3 + b)$. Then
  $ (norm(A bd(x))_2 / norm(bd x)_2) ^2  = (10/9 (a² + b²) + 4/3 a b) / (a² + b²) = 10/9 + 2/3 (2a b) / (a² + b²) <= 10/9 + 2/3 = 16 / 9 $
  The maximum is obtained when $a = b$. Thus 
  $ norm(A)_2 = 4/3 $

  Although in practice, we use a later theorem to find $norm(A)_2 = sqrt(rho(A^t A))$.
]

#theorem[ For a vector norm and its induced matrix norm, 
  $ norm(A bd(x)) <= norm(A) norm(bd(x)) $ <matrix-norm>
]

#proof[
  This follows directly from the definition of induced matrix norm. 
]
#definition[
  For a non-singular square matrix $A$,
  $ kappa(A)=norm(A) norm(A^(-1)) $ is the _condition number_ of $A$.
]



#lemma[
  For a symmetric matrix $A in RR^(n times n)$, the eigenvalues are real and we can choose a set of orthonormal eigenvectors that span $RR^n$. <symmetric-eigen>
]

#definition[
  A matrix $B in RR^(n times n)$ is _positive definite_ if $bd(x)^t B bd(x) > 0$ for any $bd(x) != bd(0)$.
]

#lemma[
  The eigenvalues of a positive definite matrix are positive. <pd-eigenvalue> 
]
#definition[
  For a square matrix $A$,
  $rho(A) = max_k | lambda_k |$ where $lambda_k$ are eigenvalues of $A$.
]
#theorem[For a non-singular square matrix $A$,
  $
    norm(A)_2 = sqrt( rho (A^t A))
  $
]

#proof[
  $A^t A$ is clearly symmetric. $A^t A$ is also positive definite because for any $bd(x) != bd(0)$, $bd(x)^t (A^t A) bd(x) = norm(A bd(x))^2_2 > 0$ since $A$ is non-singular. By #thmref(<pd-eigenvalue>)[Lemma], the eigenvalues $mu_j$ of $A^t A$ are positive. By #thmref(<symmetric-eigen>)[Lemma], we can choose a set of orthonormal eigenvectors $bd(w)_j$ that span $RR ^ n$. Namely, for all $j, k = 1 , dots , N$,
  $ A^t A bd(w)_j  &= mu_j bd(w)_j \
   bd(w)_j dot.c bd(w)_k &= delta_(j k) $ and for all $bd(x) in RR^n$, there exist $x_1, dots, x_n$ such that $bd(x) = sum_(j=1)^n x_j bd(w)_j$.

  Then $ norm(A)_2^2 &= max_(norm(bd(x)) = 1) bd(x)^t A^t A bd(x) \
  &= max_(norm(bd(x)) = 1) (sum_(i=1)^n x_i bd(w)^t_i) A^t A (sum_(j=1)^n x_j bd(w)_j) \
  &= max_(norm(bd(x)) = 1) (sum_(i=1)^n x_i bd(w)^t_i)(sum_(j=1)^n x_j mu_j bd(w)_j) \
  &= max_(norm(bd(x)) = 1) sum_(i=1)^n sum_(j=1)^n x_i x_j  mu_j bd(w)^t_i bd(w)_j \
  &= max_(norm(bd(x)) = 1) sum_(i=1)^n x_i^2 mu_i \
  &<= max_(norm(bd(x)) = 1) sum_(i=1)^n x_i^2 max_j |mu_j| \
  &= max_j |mu_j|
  $ 

  If $k = "argmax"_j|mu_j|$, then the maximum is obtained when $x_i = delta_(i, k)$. This proves the result.
]
== Error estimates

Given $A in RR ^ (n times n), bold(b) in RR^n$. Assume there exists $bold(x) in RR^n$ such that $A bold(x) = bold(b)$. Given $hat(bold(x))$, an approximation to $bold(x)$, estimate the upper bound for the error $norm(bold(x) - bold(hat(x)))$.  The main idea is to use $bold(hat(r)) = bold(b) - A bold(hat(x))$ and $norm(bold(hat(r)))$.

// Let $A, bd(b), bd(x), bd(hat(x))$ be such that $A bd(x) = bd(b)$ and $bold(hat(r)) = bold(b) - A bold(hat(x))$.
#theorem(name: "Absolute error estimate")[
    $ norm(bd(x) - bd(hat(x))) <= norm(A^(-1)) norm(hat(bd(r))) $ <error-1>
]

#proof[
  $ 
    norm(bd(x) - bd(hat(x))) 
    &= norm(A^(-1)bd(b) - bd(hat(x))) \
    &= norm(A^(-1)(bd(b) - A bd(hat(x)))) \
    &= norm(A^(-1) hat(bd(r))) \
    &<= norm(A^(-1)) norm(hat(bd(r)))
  $
  The last inequality is due to #thmref(<matrix-norm>)[Theorem].
]
#theorem(name: "Relative error estimate")[
  For any $bd(x) != bd(0)$,
  $ norm(bd(x) - bd(hat(x))) / norm(bd(x)) <= kappa(A) norm(bd(hat(r))) / norm(bd(b)) $
  <error-2>
]

#proof[
  By #thmref(<matrix-norm>)[Theorem],
  $
    norm(bd(b)) = norm(A bd(x)) <= norm(A) norm(bd(x))
  $
  Thus for $bd(x) != bd(0)$,
  $
    1 / norm(bd(x)) <= norm(A) / norm(bd(b))
  $
  Then by #thmref(<error-1>)[Theorem],
  $
    norm(bd(x) - bd(hat(x))) / norm(bd(x)) <=norm(A) norm(A^(-1)) norm(bd(hat(r))) / norm(bd(b))  = kappa(A) norm(bd(hat(r))) / norm(bd(b))
  $

]


#theorem(name: "Perturbation Theorem")[
  Let $A bd(x) = bd(b)$ and $(A + delta A) hat(bd(x)) = bd(b) + delta bd(b)$, where $delta A$ and $delta bd(b)$ are perturbations. Assume $norm(delta A) < 1/norm(A^(-1))$. Then 
  $ norm(bd(x) - hat(bd(x))) / norm(bd(x)) <= kappa(A) / (1 - kappa(A) norm(delta A) / norm(A))  (norm(delta bd(b)) / norm(bd(b)) + norm(delta A) / norm(A) ) $
]

#proof[
  From $A bd(x) = bd(b)$ and $(A + delta A) hat(bd(x)) = bd(b) + delta bd(b)$ we can deduce that 
  $
    A(bd(x) - bd(hat(x))) = - delta bd(b) + delta A bd(hat(x)) = - delta bd(b) + delta A bd(x) - delta A (bd(x) - bd(hat(x)))
  $
  Thus $bd(x) - bd(hat(x)) = A^(-1)(- delta bd(b) + delta A bd(x) - delta A (bd(x) - bd(hat(x))))$ and by triangle inequality and #thmref(<matrix-norm>)[Theorem],
  $
    norm(bd(x) - bd(hat(x))) <= norm(A^(-1)) (norm(delta bd(b)) + norm(delta A) norm(bd(x)) + norm(delta A) norm(bd(x) - bd(hat(x))))
  $
  From $1/norm(bd(x)) <= norm(A) / norm(bd(b))$ and $kappa(A) = norm(A) norm(A^(-1)) $ we deduce that 
  $
    norm(bd(x) - hat(bd(x))) / norm(bd(x)) <= kappa(A) (norm(delta bd(b)) / norm(bd(b)) + norm(delta A) / norm(A) + norm(delta A) / norm(A) norm(bd(x) - hat(bd(x))) / norm(bd(x)))
  $
  Thus 
  $
    (1 - kappa(A) norm(delta A) / norm(A)) norm(bd(x) - hat(bd(x))) / norm(bd(x)) &<= kappa(A) (norm(delta bd(b)) / norm(bd(b)) + norm(delta A) / norm(A)) $
  When $norm(delta A) < 1/norm(A^(-1))$, we have that $1 - kappa(A) norm(delta A) / norm(A) > 0$ and thus
  $
    norm(bd(x) - hat(bd(x))) / norm(bd(x)) &<= kappa(A) / (1 - kappa(A) norm(delta A) / norm(A)) (norm(delta bd(b)) / norm(bd(b)) + norm(delta A) / norm(A))
  $
]

#pagebreak()
= Linear Systems: Advanced Methods II

#definition[
  $Q in RR^(n times n)$ is said to be an _orthognal_ or _orthonormal_ matrix when $Q^t Q = I$.
]

#theorem(name: "QR factorisation")[
  Let $A in RR^(n times n)$. Then there exist an orthognal matrix $Q in RR^(n times n)$ and an upper triangular matrix $R in RR^(n times n)$ such that $A = Q R$.
]

#corollary[
  If $A bd(x) = bd(b)$, then $R bd(x) = Q^t bd(b)$.
]

We can easily solve  $R bd(x) = Q^t bd(b)$  using backwards substitution.

#example(name: "Over-determined systems")[
  Consider $A bd(x) = bd(b)$, where $A in RR^(m times n), bd(x) = RR^n, bd(b) in RR^m$ and $m > n$. Then there is generally no solution to $bd(x)$. We would then like to find the least-squares solution, which is to find $bd(x) = RR^n$ that minimises $1/2 norm(bd(b) - A bd(x))^2_2$. Differentiating using matrix calculus gives $ A^t A bd(x) = A^t bd(b) $
  It is not advisable to compute $B = A^t A$ and then use Gaussian elimination on $B bd(x) = A^t bd(b)$. Instead, factorise $A$ as $A = Q R$ and $ (R^t Q^t) (Q R) bd(x) = (R^t Q^t) bd(b) $
  Since $Q^t Q = I$, pre-multiplying $R^(-t)$ gives 
  $ R bd(x) = Q^t bd(b) $
  Thus we see that QR factorisation solves the least-squares problem.
]
#definition[
  The _projection operator_ defined on an inner product space is $ "proj"_(bd(u))(bd(v)) = (angle.l bd(v), bd(u) angle.r)/(angle.l bd(u), bd(u) angle.r) bd(u) $
  This operator projects $bd(v)$ orthogonally onto the line spanned by vector $bd(u)$. Specially, when $norm(bd(u)) = 1$, $ "proj"_(bd(u))(bd(v)) = angle.l bd(v), bd(u) angle.r bd(u) $
]
To QR factorise any given matrix $A$, we apply the Gram-Schmidt algorithm.
#method(name: "Gram-Schmidt algorithm")[
Let $bd(a)_1, dots, bd(a)_n$ be the $n$ columns of a given matrix $A$. Define $r_(1, 1) = norm(bd(a)_1)$, $bd(q)_1 = bd(a)_1 \/r_(1, 1)$, and for all $1 <= i < j <= n$, define
$
  r_(i, j) &=  angle.l  bd(a)_j, bd(q)_i angle.r \
  bd(v)_j &= bd(a)_j - sum_(i=1)^(j-1) "proj"_(bd(q)_i) bd(a)_j = bd(a)_j - sum_(i=1)^(j-1) r_(i, j) bd(q)_i \
  bd(q)_j &= bd(v)_j / r_(j, j)  quad "with" quad  r_(j, j) = norm(bd(v)_j) 
$
Then $Q$ defined by its $n$ columns $bd(q)_j$ and $R$ defined by its entries $r_(i, j)$ satisfy $A= Q R$.
] 

The classical implementation given below is not stable. 

#algo(title: "Classical Gram-Schmidt algorithm")[
  for $j <- 1$ to $n$ #i\
    $bd(v)_j <- bd(a)_j$ \
    for $i <- 1$ to $j - 1$ #i\
      $r_(i, j) <- bd(q)_i^t bd(a)_j$ \
      $bd(v)_j <- bd(v)_j - r_(i, j) bd(q)_i$ #d\
    end\
    $r_(j, j) <- norm(bd(v)_j)_2$\
    $bd(q)_j <- bd(v)_j / r_(j, j)$ #d\
  end\
]

To find an orthognal (instead of orthonormal) basis $bd(q)_1, dots, bd(q)_n$ for $"span"{bd(a)_1, dots, bd(a)_n}$ (such that for all $i != j$, $angle.l bd(q)_i, bd(q)_j angle.r = 0$), the following simplified process can be used. 

#method(name: "Gram-Schmidt algorithm")[
Let $bd(a)_1, dots, bd(a)_n$ be the $n$ columns of a given matrix $A$. Define $bd(q)_1 = bd(a)_1 $, and for all $2 <= j <= n$, define
$
  bd(q)_j &= bd(a)_j - sum_(i=1)^(j-1) "proj"_(bd(q)_i) bd(a)_j 
$
<gs-simp>
] 


#pagebreak()
= Linear Systems: Advanced Methods III
#problem[
Given $A in RR^(n times n)$ and $bd(b) in RR^n$, solve for $bd(x)$ in $A bd(x) = bd(b)$, where $A$ is symmetric positive definite (SPD for short).
]


== Stationary iterative methods

#method(name: "Stationary iterative methods")[
  Iterate from an initial guess $bd(x)_0$ using 
$ bd(x)_(k+1) = T bd(x)_k + bd(c) $ for some $T$ and $bd(c)$ such that $rho(T) < 1$ and  $bd(x)_k -> bd(x)$ as $k -> oo$. Note that $T$ is fixed here for all $k$ (hence the name). 
]

Now write $A = D - L - U$ where $D$ is a diagnoal matrix, $L$ is lower triangular and $U$ is upper triangular. 

#method(name: "Jacobi method")[
The Jacobi method is a stationary iterative method with 
$ T &= D^(-1) (L+U) \ bd(c) &= D^(-1) bd(b) $
]

#method(name: "Gauss-Seidel method")[
  The Gauss-Seidel method is stationary iterative method with $ T&=(D-L)^(-1) U  \ bd(c) &= (D - L)^(-1) bd(b) $
]


== Non-stationary methods: Steepest-descent method
#method(name: "Steepest-descent method")[Iterate from an initial guess $bd(x)_0$ using 
  $ bd(x)_(k+1) = bd(x)_k + alpha_k bd(r)_k $

where $bd(r)_k = bd(b) - A bd(x)_k$ and  $ alpha_k = (bd(r)^t_k bd(r)_k) / (bd(r)^t_k A bd(r)_k) $

]

#theorem[
  Every two consecutive steps in the steepest-descent method are orthognal, i.e. $bd(r)_k dot.c bd(r)_(k+1) = 0$. 
]

#proof[
  $ bd(r)_k dot.c bd(r)_(k+1) &= bd(r)_k^t (bd(b) - A bd(x)_(k+1))  \
  &= bd(r)_k^t (bd(b) - A (bd(x)_k + alpha_k bd(r)_k)) \
  &= bd(r)_k^t (bd(r)_k -  alpha_k A bd(r)_k) \
  &= bd(r)_k^r bd(r)_k - alpha_k  bd(r)_k^t A bd(r)_k \
  &= 0
  
  $
]

== Non-stationary methods: The conjugate gradient method

#theorem[
  Let $A$ be a symmetric positive definite matrix. Then $ angle.l bd(u), bd(v) angle.r_A = bd(u)^t A bd(v) $ defines an inner product. <matrix-ip>
]

#definition(name: [$A$-norm])[ The _$A$-norm_ is the induced norm of the inner product defined in #thmref(<matrix-ip>)[Theorem]:
  $ norm(bd(x))_A = sqrt(bd(x)^t A bd(x)) $
]

#definition(name: "Conjugate directions")[
  Two vectors $bd(u)$ and $bd(v)$ are _conjugate_ if and only if they are orthogonal with respect to the inner product defined in #thmref(<matrix-ip>)[Theorem], i.e. $ angle.l bd(u), bd(v) angle.r_A = bd(u)^t A bd(v) = 0 $
]

#method(name: "Conjugate gradient method")[Iterate from an initial guess $bd(x)_0$ with $ bd(x)_(k+1) = bd(x)_k + alpha_k bd(p)_k $ where we define $bd(p)_0 &= bd(r)_0 = bd(b) - A bd(x)_0$ and $ 
alpha_j &= (bd(p)_j^t bd(r)_0) / (bd(p)_j^t A bd(p)_j)  \
bd(r)_k &= bd(b) - A bd(x)_k \
 bd(p)_k &= bd(r)_k - sum_(i=0)^(k-1) c_(k i) bd(p)_i quad "with" quad
 c_(k i) = (bd(p)_i^t A bd(r)_k) / (bd(p)_i^t A bd(p)_i ) \
 $
]

#theorem[
  In the conjugate gradient method, ${bd(p)_i}$ are conjugate directions, i.e. for all $i != j$, $ bd(p)_j^t A bd(p)_i = 0 $  <cg-conjugate>
]

#proof[
  For any given $k$, 
  ${bd(p)_0, dots, bd(p)_k}$ are obtained exactly by applying #thmref(<gs-simp>)[Method] to ${bd(r)_0, dots, bd(r)_k}$ with respect to the inner product defined in #thmref(<matrix-ip>)[Theorem].
]

#theorem[In the conjugate gradient method, for all $0 <= j <= k - 1$,
$ bd(p)_j dot.c bd(r)_k = bd(p)_j^t (bd(b) -  A bd(x)_k) = 0 $ 
]

#proof[ From the recursive relation we obtain
  $ bd(x)_k = bd(x)_0 + sum_(i=1)^(k-1) alpha_i bd(p)_i $
  Thus 
  $
    bd(p)_j dot.c bd(r)_k = bd(p)_j^t (bd(b) -  A bd(x)_k) &= bd(p)_j^t (bd(b) -  A (bd(x)_0 + sum_(i=1)^(k-1) alpha_i bd(p)_i ) ) \
    &= bd(p)_j^t (bd(r)_0 -  sum_(i=1)^(k-1) alpha_i A bd(p)_i  ) \
    &= bd(p)_j^t bd(r)_0 -  sum_(i=1)^(k-1) alpha_i bd(p)_j^t  A bd(p)_i  \
    &= bd(p)_j^t bd(r)_0 -  alpha_j bd(p)_j^t  A bd(p)_j \
    &= 0
  $

  where $ sum_(i=1)^(k-1) bd(p)_j^t  A bd(p)_i = bd(p)_j^t  A bd(p)_j$ due to #thmref(<cg-conjugate>)[Theorem].
]


// Let $ bd(x)_k = bd(x)_0 + sum_(i=0)^(k-1) alpha_i bd(p)_i $ with ${bd(p)_i}$ are conjugate directions $ bd(p)_j^t A bd(p)_i = 0 $ for any $i != j$. Equivalently, $ bd(x)_(k+1) = bd(x)_k + alpha_k bd(p)_k $

// Denote $bd(r)_k = b - A bd(x)_k$. Then we want $ bd(p)_j dot.c bd(r)_k = bd(p)_j^t (bd(b) -  A bd(x)_k) = 0 $ for all $j = 0, dots, k - 1$. Then $ alpha_j = (bd(p)_j^t bd(r)_0) / (bd(p)_j^t A bd(p)_j) $

// Compute conjugate directions: $A$-orthogonal Gram-Schmidt:

// $ bd(p)_k = bd(r)_k - sum_(i=0)^(k-1) c_(k i) bd(p)_i $

// where $ c_(k i) = (bd(p)_i^t A bd(r)_k) / (bd(p)_i^t A bd(p)_i ) $ are obtained from the constraint of conjugate directions.


// === Minimisation of $A$-norm of the error
== Error analysis of the conjugate gradient method

#definition(name: ["Krylov" subspace])[
  $ cal(K)_k = "span"{bd(p)_0, dots, bd(p)_(k-1)} = "span"{bd(r)_0, dots, bd(r)_(k-1)} $
  
]
#theorem[
  Let $bd(x)_k$ be given by the conjugate gradient method applied to $A bd(x) =bd(b)$ with $bd(x)_0  = bd(0)$. Assume at the $k$-th step  the method is not yet converged, namely $bd(r)_(k-1) != bd(0)$, then $bd(x)_k$ is the unique minimiser of $bd(y) |-> norm(bd(x) - bd(y)) _ A$ in $cal(K)_k$ . 
]

#proof[
  Consider an arbitrary $bd(y) in cal(K)_k$. We would like to show that $norm(bd(x) -bd(y))_A >= norm(bd(x) - bd(x)_k)_A$. Let $bd(e) = bd(x) - bd(y)$ and $bd(e)_k = bd(x) - bd(x)_k$. Then $A bd(e)_k = A(bd(x) - bd(x)_k) = bd(b)-A bd(x)_k = bd(r)_k$. 
  
  Further let $bd(delta x) = bd(x)_k - bd(y) $. Note that $bd(delta x) in cal(K)_k$ is a linear combination of $bd(p)_0, dots, bd(p)_(k-1)$ and $bd(r)_k^t bd(p)_j = 0$ for all $j = 0, dots, k - 1$. Thus $bd(delta x)^t bd(r)_k = 0$.
  
  From $bd(e) = bd(e)_k +  bd(delta x)$ we deduce
  $ norm(bd(e))_A^2 &= (bd(e)_k + bd(delta x))^t A (bd(e)_k + bd(delta x)) \
  &= bd(e)_k^t A bd(e)_k + bd(delta x)^t A bd(e)_k + bd(e)_k^t A bd(delta x) + bd(delta x)^t A bd(delta x) \
  &= bd(e)_k^t A bd(e)_k + 2 bd(delta x)^t A bd(e)_k  + bd(delta x)^t A bd(delta x) \ 
  &= bd(e)_k^t A bd(e)_k + 2 bd(delta x)^t bd(r)_k  + bd(delta x)^t A bd(delta x) \
  
  &= bd(e)_k^t A bd(e)_k + bd(delta x)^t A bd(delta x)
  $
  which is minimised exactly when $bd(delta x) = bd(0)$ since $A$ is positive definite. 
]

#theorem[
  Assume $bd(r)_k != 0$, then $bd(p)_k != 0$.
]
#proof[ From how we calculate $bd(p)_k$,
  $ bd(p)_k^t bd(r)_k = bd(r)_k^t bd(r)_k - sum_(i=0)^(k-1) c_(k i) bd(p)_i^t bd(r)_k = bd(r)_k^t bd(r)_k >0 $
  The result thus follows.
]

#corollary[
  The conjugate gradient method converges in at most $n$ steps. 
]
#proof[
  $dim cal(K)_n = n$ and therefore $cal(K)_n = RR^n$. Thus $bd(x)_n = bd(x)$.
]

#theorem[
  When $n$ is large,
  $ (norm(bd(e)_k)_A) / (norm(bd(e)_0)_A) <= 2 ((sqrt(kappa) - 1) / (sqrt(kappa) + 1))^k -> abs(1 - 2 / sqrt(kappa)) $ as $k -> oo$, where $kappa = kappa(A)$ is the conditional nubmer of $A$. 
]

#pagebreak()

= Low-Rank Approximation I

== The power method and Rayleigh quotient

#problem[
  Given $A in RR^(m times m)$ and $A = A^t$. Find its dominant eigenvalue-eigenvector pair $bd(v), lambda$, where $ A bd(v) = lambda bd(v) $ for the largest $abs(lambda)$.
]

#method(name: [Power method])[
  Given $bd(v)^((0))$ where $norm(bd(v)^((0))) = 1$. For $k = 1, 2, dots$, let $ bd(w) &= A bd(v)^((k-1)) \ bd(v)^((k)) &= (bd(w))/ (norm(bd(w))) \ lambda^((k)) &= (bd(v)^((k)))^t A bd(v)^((k)) $
]

#theorem[In the power method, 
  $ bd(v)^((k)) -> plus.minus bd(q)_1 quad "and" quad lambda^((k)) ->  lambda_1  quad "as " k -> oo $
]

#proof[ 
$A$ is real symmetric, so all eigenvalues of $A$ are real and $A$ has a set of orthonormal eigenvectors which span $RR^(m)$ by #thmref(<symmetric-eigen>)[Lemma]. 

For the eigenvalues of $A$, suppose $|lambda_1| > |lambda_2| >= dots >= |lambda_m| >= 0 $ and let $
bd(v)^((0)) = sum_(i=1)^m a_i bd(q)_i
$
Then by the recursive relation, $
bd(v)^((k)) &= c_k A^k bd(v)^((0)) \
&= c_k ( sum_(i=1)^m a_i A^k bd(q)_i) \
&= c_k ( sum_(i=1)^m a_i lambda_i^k bd(q)_i) \
&= c_k lambda_1^k (a_1 bd(q)_1 + sum_(i=2)^m a_i (lambda_i / lambda_1)^k bd(q)_i)
$
where $c_k$ are normalising coefficients.

Since $|lambda_i| < |lambda_1|$, for all $i = 2, dots, m$, $ (lambda_i / lambda_1)^k -> 0 $ Thus $ bd(v)^((k)) -> c_k lambda_1^k a_1 bd(q)_1 $ But $norm(bd(v)^((k))) = norm(bd(q)_1) = 1$ thanks to the normalising effect of $c_k$, thus 
$bd(v)^((k)) -> plus.minus bd(q)_1 $. Then $ lambda^((k)) = (bd(v)^((k)))^t A bd(v)^((k)) -> bd(q)_1^t A bd(q)_1 = lambda_1 bd(q)_1^t bd(q)_1 = lambda_1 $
]
// #example[
//   Power Rank: the dominant eigenvalue is $1$.
// ]


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
  as $k -> oo$. They both convergence linearly.
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

 
Let $lambda$ and $bd(v)$ be a pair of eigenvalue and eigenvector of matrix $A$, then $ A bd(v) = lambda bd(v) $ Then since $ lambda^(-1) bd(v) = A^(-1) bd(v) $ we see that $lambda^(-1)$ is an eigenvalue of $A^(-1)$ for the same eigenvector $bd(v)$. To find the eigenvalue with the smallest absolute value of $A$, we only need to find the one with the largest absolute value for $A^(-1)$. In general, since for $mu != lambda$,
$ (A - mu I) bd(v) &= (lambda - mu) bd(v) \
  1/(lambda - mu) bd(v) &= (A - mu I)^(-1) bd(v)
$  we have the following.

#method(name: "Inverse iteration")[Suppose $mu$ is not an eigenvalue of $A$. To find the eigenvalue $lambda$ of $A$ which is the closest to $mu$, we only need to find the largest-magnitude eigenvalue $lambda'$ of $B = (A - mu I)^(-1)$ and $ lambda = mu + 1 / (lambda') $ 

In practice, we solve a linear system at each step instead of actually computing the inverse matrix of $A - mu I$.]



#theorem[
  Suppose $lambda_J$ and $lambda_K$ are the closest and second closest eigenvalue of $A$ to $mu$ and $bd(q)_J^t bd(v)^((0)) != 0$. Then the inverse iteration method converges, with 
  $ norm(bd(v)^((0)) - bd(q)_J^t) &= O(abs( (mu - lambda_J) / (mu - lambda_K) )^k) \

  abs(lambda^((k)) - lambda_J) &= O(abs( (mu - lambda_J) / (mu - lambda_K) )^(2k))
  
   $
]

== Simultaneous iteration
#method(name: "Simultaneous iteration, unnormalised version")[
  Suppose $A in RR^(m times m)$, where $m >= n$. Take $ V^((0)) = mat( bd(v)_1^((0)), dots, bd(v)_n^((0)); ) $ where $bd(v)_i in RR^m$. For $k = 1, 2, dots$, $ V^((k)) = A V^((k-1)) = mat(A bd(v)_1^((k-1)), dots, A bd(v)_n^((k-1))  ; ) $

With QR factorisation of $V^((k))$, we expect that $Q^((k)) -> mat(bd(q)_1, dots, bd(q)_n; )$ where $ Q^((k)) R^((k)) = V^((k)) $ and $ Q^((k)) in RR^(m times n)$.
]
#method(name: "Simultaneous iteration, normalised version")[
Pick $Q^((0)) in RR^(m times n)$ with orthonormal columns. For $k = 1, 2, dots$, 
$ Z&= A Q^((k-1)) \ Q^((k)) R^((k)) &= Z $ which is the reduced QR factorisation of $Z$.
]
#theorem[
  Suppose $|lambda_1| > |lambda_2| > dots > |lambda_n| > |lambda_(n+1)| >= dots >= |lambda_m|$ and all leading principal submatrices of $Q^T V^((0))$ are nonsingular with $Q=mat(bd(q)_1, dots, bd(q)_n; )$. Then 
  $ Q^((k)) -> Q $ linearly with $ norm(bd(q)_j^((k)) - (plus.minus bd(q)_j)) = O(alpha^k) $ where $alpha = max_(1<=k<=n) (lambda_(k+1)) / (lambda_k)$.
]

#pagebreak()

= Low-Rank Approximation II

== Single value decomposition

#theorem(name: "Matrix diagonalisation")[
Suppose $A in RR^(n times n)$ with $n$ linearly independent eigenvalues. Then $ A = X Lambda X^(-1) $ where each column $bd(x)_i$ of $X$ is an eigenvector of $A$ and $lambda_i$ is the corresponding eigenvalue.
]

#definition(name: "Orthogonal matrices")[
  A matrix $Q in RR^(n times n)$ is _orthogonal_ if $ Q^t = Q^(-1) $
]


#theorem(name: "Spectral theorem")[
Suppose $A in RR^(n times n)$ is symmetric, then $ A = Q Lambda Q^t $ where $lambda_i in RR$ and $Q$ is an orthogonal matrix.
]
#definition[
  The _column (row) space_ of a matrix is the vector space spanned by its columns (rows).
]
#definition[
  The _rank_ of a matrix is the dimension of its column space (or equally, its row space).
]



We would like to decompose a matrix into two sets of vectors $bd(u)_i$ and $bd(v)_i$ satisfying  
$ A bd(v)_i = sigma_i bd(u)_i $ where $bd(v)_i$ is the $i$-th right singular vector, $sigma_i$ is the $i$-th singular value, and $bd(u)_i$ is the $i$-th left singular vector. Further, $A^t A$ and $A A^t$ are symmetric matrices which satisfy

$ A^t A bd(u)_i  &= sigma_i^2 bd(u)_i \
 A A^t bd(v)_i  &= sigma_i^2 bd(v)_i $

We then write $ A = U Sigma V^t $ where $bd(u)_i$ is the $i$-th column of $U$, $bd(v)_i$ is the $i$-th column of $V$, and $sigma_i$ is the $i$-th entry of the diagonal matrix $Sigma$. Equivalently, $ A = sum_(i=1)^r sigma_i bd(u)_i bd(v)_i^t $
where $r <= min{m, n}$ is the rank of $A$.

#definition(name: "Unitary matrices")[
  A matrix $U in RR^(m times n)$ is _unitary_ if $ U^t U = I_(n times n) $
]

We see that unitary matrices are a generalisation of orthogonal matrices. 

#definition(name: "Singluar value decomposition")[
Consider matrix $A in RR^(m times n)$ (not necessarily full rank). Then a _singular value decomposition_ of $A$ is
$ A = U Sigma V^t $
where
 $U in RR^(m times n)$ is a unitary matrix, $Sigma in RR^(n times n)$ is a diagonal matrix 
with non-negative entries, and $V in RR^(n times n)$  is an orthogonal matrix.
]


#theorem[
  An SVD always exists with $sigma_i$ unique, which are called the _singular values_ of $A$ and are the non-negative square roots of the eigenvalues of $A^t A$.

  If $A$ is square, then $bd(u)_i$ and $bd(v)_i$ are unique up to its sign. 
]

If $A = U Sigma V^t$, then 
$ A^t A = V Sigma^t Sigma V^t $

where $ Sigma^t Sigma = "diag"(sigma_1^2, dots, sigma_n^2) $This is the spectral theorem for $A^t A$. 

Since $ A V &= U Sigma \ A^t U &= V Sigma $

we have that 
$
underbrace(mat(O, A^t; A, O), H) underbrace(mat(V, V; U, -U), Q) = underbrace(mat(V, V; U, -U), Q) underbrace(mat(Sigma, O; O, -Sigma), Lambda)
$

Hence by computing the eigenvalues and eigenvectors of $H$ we can get the SVD of $A$. 

== Low rank approximation

#definition(name: "Low rank approximation")[
  Let $sigma_1 >= sigma_2 >= dots >= sigma_r >= 0$ be the singular values of $A$, then for $1 <= k <= r$, the _best rank-$k$ approximation_ of $A$ is 
  $ A_k = sum_(j=1)^k sigma_j bd(u)_j bd(v)_j^t $

  
]

#lemma[Let $sigma_1$ be the largest singular value of $A$, then
  $ norm(A)_2 = sigma_1 $
  <singular-norm>
]
#proof[
  This directly follows from $ norm(A)_2 = sqrt(rho(A^t A))$ and how we compute $sigma_1$.
]

#theorem(name: "The Eckart-Young Theorem")[
  $ norm(A-A_k) = min_(B in RR^(m times n), "rank" B <= k) norm(A - B) $
  where $norm(dot)$ is either $ norm(A)_2 = max_(bd(x)) (norm(A bd(x))_2 / norm(bd(x))_2) $ or 
  the Frobenius norm $ norm(A)_F = sqrt(sum_(i=1)^m sum_(j=1)^n |a_(i j)|^2) $
  Further, $ norm(A - A_k)_2 = sigma_(k+1) $ and $ norm(A - A_k)_F = sqrt(sum_(i=k+1)^n sigma_i^2) $
]

#proof[We only prove for the $2$-norm. 
  It is easy to see that $norm(A - A_k)_2 = sigma_(k+1)$ by #thmref(<singular-norm>)[Lemma].

  Assume that there exists $B in RR^(m times n)$ with $"rank" B <= k$ such that $ norm(A-B)_2 < norm(A - A_k)_2 = sigma_(k+1) $

  There exists $W_1 subset RR^n$ such that $dim W_1 = n - k$ and 
  $B bd(w)_1 = bd(0)$
  for all $bd(w)_1 in W_1$, since $"rank" B <= k$. 
  Then 
  $ 
  norm(A bd(w)_1)_2 = norm((A-B)bd(w)_1)_2 <= norm(A-B)_2 norm(bd(w)_1)_2 < sigma_(k+1) norm(bd(w)_1)_2
  $

  There exists $W_2 subset RR^n$ such that $W_2 = "span" {bd(v)_1, dots, bd(v)_(k+1)}$ and $dim W_2 = k + 1$. Then $ norm(A bd(w)_2)_2 >= sigma_(k+1) norm(bd(w)_2)_2 $

  Then $dim (W_1 sect W_2) >= 1$ and for $w in W_1 sect W_2$ we have both $norm(A bd(w))_2 < sigma_(k+1) norm(bd(w))_2$ and $norm(A bd(w))_2 >= sigma_(k+1) norm(bd(w))_2$, which is a contradiction.
]


// #proof[
//   Assume $m >= n$. Since $A^t A in RR^(n times n)$ is positive semi-definite, we can find a spectral decomposition of it: 
//   $ A^t A = V D V^t $

//   Let $Sigma = sqrt(D)$ but of size $m times n$ (pad with zero rows). Then $
//   (Sigma V^t)^t (Sigma V^t) = V Sigma^t Sigma V^t = V D V^t = A^t A
//   $

//   Then by the unitary freedom of PSD decompositions, there exists unitary $U$ such that $
//   A = U Sigma V^t
//   $
// ]
