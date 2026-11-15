# Limiting shape for directed percolation models

**James B. Martin**<br>
*The Annals of Probability* **32** (4), 2908–2937 (2004).<br>
[Published paper](https://doi.org/10.1214/009117904000000838) · [Author's preprint](https://arxiv.org/abs/math/0301055) · [Paper catalogue](../../README.md) · [Common notation](../notation.md)

This paper provides the shape theory used throughout the library. Its results give directional passage-time limits, continuity up to the axes, a universal square-root expansion near an axis, and convergence of associated growth sets. It also supplies concentration and truncation tools used in later LPP arguments.

The released shape results cover **dimension two**. Supporting concentration and directional-limit statements are included below.

## Certified results

Use the [common LPP model](../notation.md), with i.i.d. real weights of law $\mu$ and terminal-excluded passage times $L_{u,v}$. Write $|x|_1=x_1+x_2$ for $x\in \mathbb{R}_{\geq 0}^2$. For $u\le v$, define $S_{u,v}$ by taking the minimum of the same path weights used to define $L_{u,v}$. We write

$$
I_+(\mu)=\int_0^\infty\mathbb P\{\omega_0>s\}^{1/2}\,ds,
\qquad
I_-(\mu)=\int_{-\infty}^0\mathbb P\{\omega_0\le s\}^{1/2}\,ds.
$$

The paper writes $T$ for our $L$ and $\mu$ for the mean. Here $\mu$ denotes the weight law, $m=\mathbb E\omega_0$, and $\sigma^2=\mathbb E[(\omega_0-m)^2]$. The terminal-excluded path convention agrees with ours.

The [shape functions](../notation.md#shape-functions) $g$ and $h$ are defined by fixed-direction almost-sure limits. The results below prove their existence, finiteness and further properties under the indicated hypotheses. The [uniform shape approximation (U)](../notation.md#uniform-shape-approximation) is a separate conclusion, with one common probability-one event and a bound over all sufficiently distant lattice points.

### Theorem 2.3

*Finiteness and continuity.*

If $\mathbb E|\omega_0|<\infty$ and $I_+(\mu)<\infty$, the directional shape $g$ exists, is finite and continuous on the closed quadrant, and is symmetric, positively homogeneous and concave. For every fixed $x\in \mathbb{R}_{\geq 0}^2$,

$$
\frac{\mathbb E L_{0,\lfloor nx\rfloor}}n\longrightarrow g(x),
\qquad
\mathbb E\left|\frac{L_{0,\lfloor nx\rfloor}}n-g(x)\right|\longrightarrow0.
$$

[Finite-continuity certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L135) · [Directional-limit certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L73)

The first certificate combines Propositions 2.1–2.2 with Theorem 2.3 and states almost-sure and $L^1$ convergence on lattice rays. Proposition 2.1 supplies convergence in every fixed real direction. The directional definition determines $g$ uniquely.

### Section 5.3

*Uniform shape theorem in dimension two.*

If $I_+(\mu)<\infty$ and $I_-(\mu)<\infty$, the shape $g$ satisfies [the uniform approximation (U)](../notation.md#uniform-shape-approximation). This strengthens fixed-direction convergence to a common almost-sure bound over all sufficiently distant lattice points.

No positivity or nondegeneracy assumption is needed for this statement. [Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L187)

### Theorem 2.4

*Square-root boundary expansion in dimension two.*

If $I_+(\mu)<\infty$ and $I_-(\mu)<\infty$, then $\mathbb E\omega_0^2<\infty$ and

$$
g(1,\alpha)=m+2\sigma\sqrt\alpha+o(\sqrt\alpha)
\qquad\text{as }\alpha\downarrow0.
$$

The leading correction depends on the law only through its variance. The zero-variance case is included. [Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/BoundaryAsymptotics.lean#L82)

### Corollary 2.5(i)

*Finite continuous first-passage expected-rate limit in dimension two.*

If $\mathbb E|\omega_0|<\infty$ and $I_-(\mu)<\infty$, there is exactly one function $h:\mathbb{R}_{\geq 0}^2\to\mathbb R$ such that, for every $x\in \mathbb{R}_{\geq 0}^2$,

$$
\frac{\mathbb E S_{0,\lfloor nx\rfloor}}n\longrightarrow h(x),
$$

and for all $c\ge0$ and $x,y\in \mathbb{R}_{\geq 0}^2$,

$$
h(cx)=ch(x),\qquad h(x_2,x_1)=h(x_1,x_2),\qquad
h(x+y)\le h(x)+h(y).
$$

This function is continuous on all of $\mathbb{R}_{\geq 0}^2$. It is the first-passage directional shape because $S_\omega=-L_{-\omega}$ and [Proposition 2.1](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L73), applied to the negated weight law, identifies its expected-rate limits with its almost-sure limits in every fixed direction. The [certificate for Corollary 2.5(i)](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/BoundaryAsymptotics.lean#L141) itself states only the displayed expected-rate and deterministic properties. No uniform approximation is asserted in this part.

### Corollary 2.5(ii)

*First-passage boundary expansion in dimension two.*

If $I_+(\mu)<\infty$ and $I_-(\mu)<\infty$, the finite continuous first-passage shape $h$ also satisfies the first-passage version of [the uniform approximation (U)](../notation.md#uniform-shape-approximation), and

$$
h(1,\alpha)=m-2\sigma\sqrt\alpha+o(\sqrt\alpha)
\qquad\text{as }\alpha\downarrow0.
$$

[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/BoundaryAsymptotics.lean#L211)

For last-passage and first-passage shape functions $g,h$ and $t\ge0$, all four sets below are subsets of $\mathbb{R}_{\geq 0}^2$.

$$
\begin{aligned}
B&=\{x\in \mathbb{R}_{\geq 0}^2:g(x)\le1\},&
B(t)&=\{x\in \mathbb{R}_{\geq 0}^2:L_{0,\lfloor x\rfloor}\le t\},\\
C&=\{x\in \mathbb{R}_{\geq 0}^2:h(x)\le1\},&
C(t)&=\{x\in \mathbb{R}_{\geq 0}^2:S_{0,\lfloor x\rfloor}\le t\}.
\end{aligned}
$$

### Theorem 5.1(i)

*Last-passage growth sets in dimension two.*

If $I_+(\mu)<\infty$, $I_-(\mu)<\infty$ and $m>0$, then on one event of probability one, for every $\varepsilon>0$ there is $t_0>0$ such that for every real $t\ge t_0$,

$$
(1-\varepsilon)_+B\subseteq t^{-1}B(t)\subseteq(1+\varepsilon)B,
\qquad (1-\varepsilon)_+=\max\{1-\varepsilon,0\}.
$$

[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/GrowthSets.lean#L86)

For $0<\varepsilon<1$, the inner factor is the usual $1-\varepsilon$. The truncated factor records the release's nonnegative-scalar convention for larger $\varepsilon$.

### Theorem 5.1(ii)

*First-passage growth sets in dimension two.*

Assume $I_+(\mu)<\infty$ and $I_-(\mu)<\infty$. If

$$
\exists c>0\ \forall x\in \mathbb{R}_{\geq 0}^2,\qquad h(x)\ge c|x|_1,
$$

then on one event of probability one, for every $\varepsilon>0$ there is $t_0>0$ such that for every real $t\ge t_0$,

$$
(1-\varepsilon)_+C\subseteq t^{-1}C(t)\subseteq(1+\varepsilon)C.
$$

The shape exists without the positive lower bound; the growth-set conclusion is conditional on it. The lower bound is equivalent to $\inf_{x\in \mathbb{R}_{\geq 0}^2\setminus\{0\}}h(x)/|x|_1>0$. [Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/GrowthSets.lean#L157)

<!-- PAPER_MAP_START -->
## Progress and dependencies

The map groups the paper's results. Open the full graph to see each named result and its formalization status.

Graph presentation based on Scott Armstrong’s visual paper design for [*Homogenization at a polynomial scale in high contrast*](https://scottnarmstrong.github.io/hcp-visual-paper/).

[Full result graph and progress list](../graphs/paper-results/martin-2004.md)

```mermaid
flowchart TD
  C0["Limits along a fixed direction<br/>Prop. 2.1"]
  C1["A finite continuous shape<br/>Prop. 2.2 · Thm. 2.3 · Cor. 2.5(i)<br/>Lem. 3.1 · Lem. 3.2 · Lem. 3.3<br/>Prop. 3.4 · Lem. 3.5 · Lem. 3.6"]
  C2["The shape near an axis<br/>Thm. 2.4 · Cor. 2.5(ii) · Lem. 4.1<br/>Lem. 4.2 · Lem. 4.3 · Lem. 4.4<br/>Lem. 4.5 · Lem. 4.6"]
  C3["One error bound for all distant endpoints<br/>Lem. 5.2 · Lem. 5.3 · Lem. 5.4<br/>Lem. 5.5"]
  C4["Sets reached by a given time<br/>Thm. 5.1 · Remark 5.1(i)"]
  C5["Weaker moment assumptions<br/>Remark 5.1(ii)"]
  C0 --> C1
  C0 --> C2
  C1 --> C3
  C3 --> C4
```

<details>
<summary>Every result and its status</summary>

**✓ Certified** · **◐ Restricted** · **○ Not in this release** · **? Not assessed**

```mermaid
flowchart TD
  subgraph S0["Limits along a fixed direction"]
    R0["◐ Proposition 2.1<br/>Directional passage-time limits"]
  end
  subgraph S1["A finite continuous shape"]
    R1["◐ Proposition 2.2<br/>Finite values of the shape"]
    R2["◐ Theorem 2.3<br/>Continuity at boundary points"]
    R4["◐ Corollary 2.5(i)<br/>A finite continuous first-passage shape"]
    R6["✓ Lemma 3.1<br/>A probability bound for a maximum of sums"]
    R7["◐ Lemma 3.2<br/>Changing a small coordinate"]
    R8["◐ Lemma 3.3<br/>Continuity for bounded weights"]
    R9["◐ Proposition 3.4<br/>Weight bounds for connected sets"]
    R10["◐ Lemma 3.5<br/>Upper and lower passage bounds"]
    R11["◐ Lemma 3.6<br/>Effect of capping large weights"]
  end
  subgraph S2["The shape near an axis"]
    R3["✓ Theorem 2.4<br/>Shape near a coordinate axis"]
    R5["✓ Corollary 2.5(ii)<br/>First-passage shape near an axis"]
    R12["✓ Lemma 4.1<br/>A bound for Bernoulli weights"]
    R13["✓ Lemma 4.2<br/>Changing the weight distribution"]
    R14["✓ Lemma 4.3<br/>Bounded weights with the same mean and variance"]
    R15["✓ Lemma 4.4<br/>Grouping consecutive weights"]
    R16["✓ Lemma 4.5<br/>Comparing grouped weights with normal weights"]
    R17["✓ Lemma 4.6<br/>A normal comparison near the axis"]
  end
  subgraph S3["One error bound for all distant endpoints"]
    R21["◐ Lemma 5.2<br/>Capping weights changes passage times little"]
    R22["◐ Lemma 5.3<br/>Capped passage times stay near their means"]
    R23["◐ Lemma 5.4<br/>Mean passage times approach the shape"]
    R24["◐ Lemma 5.5<br/>Capping weights changes the shape little"]
  end
  subgraph S4["Sets reached by a given time"]
    R18["◐ Theorem 5.1<br/>Passage-time level sets at large times"]
    R19["◐ Remark 5.1(i)<br/>Checking a positive lower bound"]
  end
  subgraph S5["Weaker moment assumptions"]
    R20["◐ Remark 5.1(ii)<br/>Weaker moment assumptions for growth"]
  end
  R10 --> R1
  R8 --> R2
  R11 --> R2
  R0 --> R7
  R6 --> R7
  R0 --> R8
  R7 --> R8
  R9 --> R10
  R0 --> R10
  R10 --> R11
  R0 --> R11
  R0 --> R12
  R12 --> R13
  R0 --> R13
  R0 --> R15
  R13 --> R16
  R14 --> R17
  R15 --> R17
  R16 --> R17
  R13 --> R17
  R17 --> R3
  R2 --> R4
  R1 --> R4
  R3 --> R5
  R0 --> R18
  R2 --> R18
  R21 --> R18
  R22 --> R18
  R23 --> R18
  R24 --> R18
  R10 --> R21
  R6 --> R22
  R2 --> R23
  R0 --> R23
  R11 --> R24
  R0 --> R19
  classDef certified fill:#eaf6ec,stroke:#2d8544,color:#163b20
  classDef restricted fill:#fff5db,stroke:#a77815,color:#594005
  classDef not_assessed fill:#f6f8fa,stroke:#8c959f,stroke-dasharray:4 3,color:#424a53
  classDef not_in_release fill:#fff,stroke:#8c959f,color:#59636e
  class R0 restricted
  class R1 restricted
  class R2 restricted
  class R3 certified
  class R4 restricted
  class R5 certified
  class R6 certified
  class R7 restricted
  class R8 restricted
  class R9 restricted
  class R10 restricted
  class R11 restricted
  class R12 certified
  class R13 certified
  class R14 certified
  class R15 certified
  class R16 certified
  class R17 certified
  class R18 restricted
  class R19 restricted
  class R20 restricted
  class R21 restricted
  class R22 restricted
  class R23 restricted
  class R24 restricted
```

| Paper result | Formalization |
| --- | --- |
| **Proposition 2.1**<br/>Directional passage-time limits | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L73) |
| **Proposition 2.2**<br/>Finite values of the shape | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L135) |
| **Theorem 2.3**<br/>Continuity at boundary points | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L135) |
| **Corollary 2.5(i)**<br/>A finite continuous first-passage shape | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/BoundaryAsymptotics.lean#L141) |
| **Lemma 3.1**<br/>A probability bound for a maximum of sums | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/ProbabilityBasics/Statements/Concentration.lean#L81) |
| **Lemma 3.2**<br/>Changing a small coordinate | **◐ Restricted**<br/>[Bounded continuity and face estimate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/MartinBoundedContinuity.lean#L131) |
| **Lemma 3.3**<br/>Continuity for bounded weights | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/MartinBoundedContinuity.lean#L131) |
| **Proposition 3.4**<br/>Weight bounds for connected sets | **◐ Restricted**<br/>[Expected animal bound](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/AnimalPositiveMean.lean#L75) · [Almost-sure animal bound](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/GreedyAnimalAlmostSureBound.lean#L143) |
| **Lemma 3.5**<br/>Upper and lower passage bounds | **◐ Restricted**<br/>[Mean and ray-shape upper bounds](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/MartinPassageMean.lean#L33) · [Uniform passage upper bound](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/UniformPassageUpper.lean#L57) · [Shape lower bound under a negative moment](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/ShapeAboveMean.lean#L32) |
| **Lemma 3.6**<br/>Effect of capping large weights | **◐ Restricted**<br/>[Two-sided shape comparison](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/RealExpectedTruncation.lean#L158) · [Compact uniform approximation](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/MartinWeakContinuity.lean#L85) |
| **Theorem 2.4**<br/>Shape near a coordinate axis | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/BoundaryAsymptotics.lean#L82) |
| **Corollary 2.5(ii)**<br/>First-passage shape near an axis | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/BoundaryAsymptotics.lean#L211) |
| **Lemma 4.1**<br/>A bound for Bernoulli weights | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/BernoulliShapeBound.lean#L88) |
| **Lemma 4.2**<br/>Changing the weight distribution | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/ShapeComparison.lean#L119) |
| **Lemma 4.3**<br/>Bounded weights with the same mean and variance | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/MeanVarianceTruncationTail.lean#L289) |
| **Lemma 4.4**<br/>Grouping consecutive weights | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/BlockingComparison.lean#L185) |
| **Lemma 4.5**<br/>Comparing grouped weights with normal weights | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/GaussianBlockComparison.lean#L270) |
| **Lemma 4.6**<br/>A normal comparison near the axis | **✓ Certified**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/BoundaryUniversality.lean#L156) |
| **Lemma 5.2**<br/>Capping weights changes passage times little | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/UniformTruncationApproximation.lean#L89) |
| **Lemma 5.3**<br/>Capped passage times stay near their means | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/BoundedPassageFluctuations.lean#L192) |
| **Lemma 5.4**<br/>Mean passage times approach the shape | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/BoundedExpectedUniform.lean#L53) |
| **Lemma 5.5**<br/>Capping weights changes the shape little | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/MartinWeakContinuity.lean#L32) |
| **Theorem 5.1**<br/>Passage-time level sets at large times | **◐ Restricted**<br/>[Last-passage growth sets](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/GrowthSets.lean#L86) · [First-passage growth sets](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/GrowthSets.lean#L157) |
| **Remark 5.1(i)**<br/>Checking a positive lower bound | **◐ Restricted**<br/>[Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/GrowthSets.lean#L200) |
| **Remark 5.1(ii)**<br/>Weaker moment assumptions for growth | **◐ Restricted**<br/>[Weak-negative uniform shape theorem](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Probability/WeakNegativeShape.lean#L161) |

</details>

<!-- PAPER_MAP_END -->

## Supporting results

<details>
<summary>Directional limits, deterministic lower bound and concentration</summary>

### Proposition 2.1

*Directional limits in dimension two.*

If $\mathbb E|\omega_0|<\infty$, there is exactly one function $g:\mathbb{R}_{\geq 0}^2\to\mathbb R\cup\{+\infty\}$ with the following properties. For every fixed $x\in \mathbb{R}_{\geq 0}^2$,

$$
\frac{\mathbb E L_{0,\lfloor nx\rfloor}}n\longrightarrow g(x),
\qquad
\frac{L_{0,\lfloor nx\rfloor}}n\longrightarrow g(x)
\quad\text{almost surely}.
$$

If $g(x)<\infty$, then also

$$
\mathbb E\left|\frac{L_{0,\lfloor nx\rfloor}}n-g(x)\right|\longrightarrow0.
$$

For all $c\ge0$ and $x,y\in \mathbb{R}_{\geq 0}^2$,

$$
g(cx)=cg(x),\qquad
g(x_2,x_1)=g(x_1,x_2),\qquad
g(x+y)\ge g(x)+g(y),
$$

with $0\cdot(+\infty)=0$. The finite-mean lower bound rules out $-\infty$; $+\infty$ is allowed. The almost-sure assertion is quantified separately for each fixed direction. It does not assert one exceptional null set valid for all real directions. [Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/LimitShape.lean#L73)

### Remark 5.1(i)

*The deterministic lower bound, first sentence only.*

Let $h:\mathbb{R}_{\geq 0}^2\to\mathbb R$ satisfy $h(cx)=ch(x)$ for $c\ge0$, $h(x_2,x_1)=h(x_1,x_2)$, and $h(x+y)\le h(x)+h(y)$ for $x,y\in \mathbb{R}_{\geq 0}^2$. Then for every $x\in \mathbb{R}_{\geq 0}^2$,

$$
h(x)\ge\frac{|x|_1}{2}h(1,1).
$$

No continuity or probability assumption is required. This certificate concerns the first sentence and does not assert coverage of the whole remark. [Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/Martin2004/Statements/GrowthSets.lean#L200)

### Lemma 3.1

*Concentration on a general probability space.*

Let $I$ be finite and let $(Y_i)_{i\in I}$ be independent measurable real random variables on a probability space $(\Omega,\mathcal F,\mathbb P)$. Let $b\ge0$ satisfy $|Y_i|\le b$ almost surely for every $i$. Let $R\ge0$ be an integer and let $\mathcal C\ne\varnothing$ be a family of subsets of $I$ with $|C|\le R$ for each $C\in\mathcal C$. Define

$$
Z=\max_{C\in\mathcal C}\sum_{i\in C}Y_i.
$$

If $b>0$ and $R>0$, then for every $u>0$,

$$
\mathbb P\{|Z-\mathbb EZ|\ge u\}
\le \exp\!\left(64-\frac{u^2}{64Rb^2}\right).
$$

If $R=0$ or $b=0$, then $Z=0$ almost surely and $\mathbb P\{|Z-\mathbb EZ|\ge u\}=0$ for $u>0$. This result belongs to this paper's guide even though its code is in the general probability library. [Lean certificate](https://github.com/cjanjigi/LPP/blob/5a3c7a612144b68468559ea1800bf7f39a5d3ef1/ProbabilityBasics/Statements/Concentration.lean#L81)

</details>

## Deviations from the printed text

### Alternative arguments for correct statements

These replacements preserve the required conclusions of arguments treated as correct.

| Source location | What the formalization does | Why this route was chosen |
| --- | --- | --- |
| Lemma 3.1 and its cited concentration input | Proves a mean-centered concentration bound by entropy tensorization and Herbst's argument, then deduces Martin's displayed bound. | Supplies a direct proof for signed bounded variables and arbitrary families, without building the cited convex-distance and median machinery. A stronger bound, $2\exp(-u^2/(16Rb^2))$, is proved first. |
| Lemma 4.5, the cited nonuniform Berry–Esseen estimate | Uses the central limit theorem, a uniform fourth-moment bound for normalized sums of bounded variables, and dominated convergence. | The cited Petrov source was unavailable, and the subsequent argument needs only a qualitative weighted-distribution limit. No quantitative rate is used downstream. |
| Lemma 4.1, the cited solvable column model | Constructs the stationary model and proves the particular bound needed by the comparison. | Avoids formalizing an entire external exact-solution theory when the paper uses only this bound. |
| Proof of Theorem 2.4, the exponential shape formula | Derives the exponential shape through a stationary LPP model with the Burke property. | Reuses a direct stationary construction instead of the cited hydrodynamic argument. |

The stronger concentration theorem is an additional formalized result; the source-facing certificate above states Martin's bound. These two claims have different roles.

### Formulation changes and expanded details

- **Common probability space.** The LPP statements use the canonical product environment. This gives one concrete representation of iid weights throughout the library. The concentration certificate itself is stated on a general probability space.
- **Real directions in Proposition 2.1.** The formal proof supplies an explicit random-phase argument to handle rounding in nonlattice directions, followed by a comparison back to phase zero. This expands an omitted argument; it is not an unformalized part of the proposition.
- **First-passage results.** Negating weights turns maxima into minima and concave shapes into convex shapes. This follows the relation described in the paper and makes the transfer explicit.
- **Lemma 4.2.** The proof integrates the finite-size comparison before taking the scaling limit. This avoids requiring an unstated dominating function for the original order of operations.

### A formula-level correction for signed weights

The all-real-direction supremum in printed equation (2.3) need not equal the shape limit when weights can be negative. For deterministic weights $\omega_z=-1$ and $x=(1/2,0)$, the $n=1$ term is zero, while the limiting rate is $-1/2$. The formalization therefore characterizes the shape by directional limits and, where available, uniform lattice asymptotics. It does not use the printed off-lattice supremum as its definition. This is a correction of a formula, separate from the optional proof replacements above.

## Remaining coverage

The paper also treats higher dimensions; the released shape certificates described here are planar. The progress list records the remaining numbered results and whether a matching certificate has been assessed. Examples, simulations and the rest of the remarks are outside this guide's coverage claim.
