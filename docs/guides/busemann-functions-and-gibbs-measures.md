# Busemann functions and Gibbs measures in directed polymer models on ℤ²

**Christopher Janjigian and Firas Rassoul-Agha**<br>
*The Annals of Probability* **48** (2020), 778–816. [Journal article](https://doi.org/10.1214/19-AOP1375) · [Extended arXiv version](https://arxiv.org/abs/1810.03580v3)

[**Busemann existence in the related dependency graph**](https://cjanjigi.github.io/LPP/?paper=strong-existence&result=theorem-2.7)

[Paper catalogue](../../README.md) · [Common LPP notation](../notation.md)

## Theorem 4.7 · Busemann process at zero temperature

Assume i.i.d. real weights with positive variance and $`\mathbb E|\omega_0|^p<\infty`$ for some $`p>2`$. Let $`g`$ be the [directional last-passage shape](../notation.md#shape-functions). The index set is

```math
\mathcal H_\infty=\bigcup_{\xi\in\textup{ri}\,\mathcal U}(-\partial g(\xi)),
\qquad \mathcal U=\{(t,1-t):0\le t\le 1\}.
```

Here $`v\in\partial g(\xi)`$ means $`g(z)\le g(\xi)+v\cdot(z-\xi)`$ for every $`z\in\mathbb R_{\geq 0}^2`$.

There is a shift-invariant probability law on an extension with the original weight marginal and fields $`B^{h-}(x,y),B^{h+}(x,y)`$, jointly measurable in the tilt, sites and sample. At every $`h\in\mathcal H_\infty`$ both fields are integrable at each pair $`x,y`$, and their mean increments from $`x`$ to $`x+e_i`$ are $`-h_i`$.

- For each $`I\subseteq\mathbb Z^2`$, the weights $`(\omega_x)_{x\in I}`$ and all fields $`B^{h\pm}(x,y)`$ with $`x\in I`$ and $`y\ge x`$ are jointly independent of $`(\omega_z)_{z\in I_{<}}`$, where $`I_{<}=\{z:x\not\le z\text{ for every }x\in I\}`$ in the coordinatewise order.
- On one shift-invariant probability-one event, both fields are additive and shift covariant and recover the weights by $`\min_{i=1,2} B^{h\pm}(x,x+e_i)=\omega_x`$. On the same event, the east increments are nonincreasing and the north increments nondecreasing along the sequence $`B^{h-}, B^{h+}, B^{k-}, B^{k+}`$ for $`h_1<k_1`$.
- On that event, as $`k\to h`$, both branches converge to $`B^{h-}(x,y)`$ from $`k_1<h_1`$ and to $`B^{h+}(x,y)`$ from $`k_1>h_1`$. Wherever the branches agree at a pair, both are continuous there as functions of the tilt.
- At each fixed $`h`$, the branches agree almost surely for all pairs $`x,y`$.

[Lean certificate](https://github.com/cjanjigi/LPP/blob/a1a2ed304ad2459ea0a0482b1eed72971cc6ddeb/Busemann/Process/NativeFullFamily.lean#L30)

## Certificate scope

**Restricted to zero temperature and the product weight space.** The journal theorem also couples a countable set of positive temperatures and permits an arbitrary starting probability space carrying the weights with the stated shift action. The Lean proof supplies the process used in [Theorem 2.7 of *Strong existence and uniqueness of the tilt-indexed Busemann process in the planar corner growth model*](../graphs/paper-results/strong-existence.md#theorem-27).

In part (e) the journal version writes $`h_1\le k_1`$ on the common event. Applying that chain with $`h=k`$ would force the branches to agree simultaneously at every tilt. Lean uses $`h_1<k_1`$ across tilts, with the within-tilt inequalities on the common event and equality almost surely at each fixed tilt, as in part (g). The extended arXiv version numbers the existence result Theorem 4.8.
