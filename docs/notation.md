# LPP notation

[Papers and formalization guides](../README.md)

This page sets notation for the LPP models discussed in the guides. The current definitions describe the planar site-weight model; each theorem supplies its own assumptions on the weight distribution.

## Environment and geometry

The environment is a collection of real site weights

```math
\omega=(\omega_x)_{x\in\mathbb Z^2}.
```

Under $`\mathbb P=\mu^{\otimes\mathbb Z^2}`$ the weights are independent with common law $`\mu`$; expectation is denoted by $`\mathbb E`$. Signed and unbounded weights are allowed. We write $`\omega_x^+=\max\{\omega_x,0\}`$ and $`\omega_x^-=\max\{-\omega_x,0\}`$.

Let $`e_1=(1,0)`$ and $`e_2=(0,1)`$. The order $`u\le v`$ is coordinatewise, and $`\lfloor x\rfloor=(\lfloor x_1\rfloor,\lfloor x_2\rfloor)`$. The level of $`x`$ is

```math
\ell(x)=x_1+x_2.
```

For $`x`$ in the nonnegative quadrant this equals $`|x|_1`$; the level can be negative at a general lattice point.

## Paths and passage times

An admissible path $`x_{m:n}=(x_m,\ldots,x_n)`$ starts on level $`m`$, ends on level $`n`$, and satisfies $`x_{k+1}-x_k\in\{e_1,e_2\}`$. Its weight is

```math
W(x_{m:n})=\sum_{k=m}^{n-1}\omega_{x_k}.
```

**We collect the starting vertex and exclude the terminal vertex.** In particular, a length-zero path has weight zero, and weights add exactly when paths are concatenated.

For $`u\le v`$, the last-passage time is

```math
L_{u,v}(\omega)=\max\{W(x_{m:n}):x_m=u,\ x_n=v\},
\qquad m=\ell(u),\quad n=\ell(v).
```

There are finitely many admissible paths, and at least one. Thus this maximum is a real number for every environment, and $`L_{u,u}=0`$.

The **first-passage time** $`S_{u,v}`$ is the minimum over the same path weights, with the same terminal-excluded convention.

## Shape functions

Write $`\overline{\mathbb R}=[-\infty,+\infty]`$. A **shape function for the weight law $`\mu`$** is a deterministic function $`g:\mathbb{R}_{\geq 0}^2\to\overline{\mathbb R}`$ specified by the fixed-direction almost-sure limits

```math
g(x)=\lim_{n\to\infty}\frac{L_{0,\lfloor nx\rfloor}}n
\qquad\text{almost surely, for every fixed }x\in \mathbb{R}_{\geq 0}^2.
```

The probability-one event may depend on $`x`$. This definition does not require one common event for every real direction. A **first-passage shape function** $`h`$ is defined by the corresponding fixed-direction limits of $`S_{0,\lfloor nx\rfloor}/n`$.

The theorems supply existence and determine when these functions are finite. Fixed-direction limits determine them uniquely. Continuity, homogeneity, concavity or convexity, and uniform approximation are proved properties, rather than parts of this definition.

## Uniform shape approximation

For a finite function $`g:\mathbb{R}_{\geq 0}^2\to\mathbb R`$, the **uniform shape approximation** means that on one event of probability one, for every $`\varepsilon>0`$ there is $`N\in\mathbb N`$ such that

```math
|L_{0,z}-g(z)|\le\varepsilon|z|_1
\qquad(z\in\mathbb Z^2_{\ge0},\ |z|_1\ge N).
\tag{U}
```

Equivalently, almost surely,

```math
\lim_{R\to\infty}\ \sup_{\substack{z\in\mathbb Z^2_{\ge0}\\|z|_1\ge R}}
\frac{|L_{0,z}-g(z)|}{|z|_1}=0.
```

The first-passage version of (U) replaces $`L,g`$ with $`S,h`$. It is likewise a separate theorem conclusion. Its common event and its uniform bound over all sufficiently distant lattice points are stronger than convergence for each fixed direction.

## Shape properties

Positive homogeneity of degree one means $`g(cx)=cg(x)`$ for $`c\ge0`$ and $`x\in \mathbb{R}_{\geq 0}^2`$. Concavity means

```math
g(ax+by)\ge ag(x)+bg(y)
\qquad(x,y\in \mathbb{R}_{\geq 0}^2,\ a,b\ge0,\ a+b=1).
```

For a convex first-passage shape $`h`$, the inequality is reversed. Continuity in the theorem statements is on all of $`\mathbb{R}_{\geq 0}^2`$, including the axes.

An **expected-rate limit** is $`\mathbb E L_{0,\lfloor nx\rfloor}/n\to g(x)`$, or its first-passage counterpart. Proposition 2.1 of [*Limiting shape for directed percolation models*](graphs/paper-results/martin-2004.md#proposition-21) identifies the expected-rate and almost-sure limits. Negating weights gives the first-passage identification.

## Directions

Directions are represented on the unit simplex

```math
\mathcal U=\{(t,1-t):0\le t\le1\},
\qquad \textup{ri}\,\mathcal U=\{(t,1-t):0<t<1\}.
```

For a positively homogeneous shape, differentiability on the open quadrant can be checked through its profile on $`\textup{ri}\,\mathcal U`$.

## Percolation cone

When the weight law has finite upper support bound $`M_+=\sup(\textup{supp}\,\mu)`$,
write $`p_1=\mu(\{M_+\})`$ and let $`g^{\mathrm{top}}`$ be the directional
shape for the indicator weights $`\mathbf1\{\omega_x=M_+\}`$. Define

```math
\mathcal U_{\mathrm{perc}}
=\{\xi\in\mathcal U:g^{\mathrm{top}}(\xi)=1\}.
```

The **percolation cone** consists of the rays through
$`\mathcal U_{\mathrm{perc}}`$, together with the origin. Thus
$`\mathcal U_{\mathrm{perc}}`$ is its unit-direction slice, called the
flat segment in the paper. Under the hypotheses of the
[percolation cone theorem](guides/differentiability.md#percolation-cone),
it also equals $`\{\xi\in\mathcal U:g(\xi)=M_+\}`$, and
$`g(x)=M_+\ell(x)`$ on the cone.

If the support is unbounded above, set $`\mathcal U_{\mathrm{perc}}=\varnothing`$.

Write $`\vec p_c`$ for the critical density of oriented site percolation
and $`\beta_{p_1}`$ for the right-edge speed of the origin cluster when
$`p_1>\vec p_c`$. The speed limit is taken on the survival event.

## Reading the certificates

<details>
<summary>Translation to Lean notation</summary>

The guides use endpoints $`u,v`$. The released Lean definition uses a starting point and a nonnegative displacement. The expression `lastPassage ω u d` means $`L_{u,u+d}(\omega)`$, so the code for $`L_{u,v}`$ uses $`d=v-u`$.

| Mathematical object | Released definition |
|---|---|
| Environment $`\omega`$ | [`Environment`](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/LPP_Foundations/Frozen/Model/Environment.lean) |
| Path weight $`W`$ | [`pathWeight`](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/LPP_Foundations/Frozen/Model/PathWeight.lean#L13) |
| Passage time $`L`$ | [`lastPassage`](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/LPP_Foundations/Frozen/Model/LastPassage.lean#L12) |
| Shape properties and moment assumptions | [`ShapeDefinitions`](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/LPP_Foundations/Statements/ShapeDefinitions.lean) |

Paper-specific objects are introduced on their own pages.

</details>
