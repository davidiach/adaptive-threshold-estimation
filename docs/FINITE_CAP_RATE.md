# An explicit convergence rate for the optimized stopping programs

Let $P_N(B)$ denote the ordinary cap-$N$ stopping-program value, $G_N(B)$
the cap-$N$ dual value when a genie reveals the latent coin at depth $N$,
and $P_\infty(B)$ the common limit. The [original programs and qualitative
brackets](../paper/v6/appendix-genie.tex) use a known law on $(0,1/2]$,
the global rarity constraint $\int q\,d\mu\le\rho$, and a positive expected
observation budget $B$. The two optimization problems may choose different
variance and work references.

**Theorem.** For every admissible law, $0<\rho\le1/2$, $B>0$, integer
$N\ge1$ and $k>1$, one has
$$
 N\ \ge\ \frac{B}{(1-1/k)^2(k^2-1)}
 \quad\Longrightarrow\quad
 G_N(B)\ \le\ P_\infty(B)\ \le\ P_N(B)\ \le\ k G_N(B).
$$
In particular $N=\max(1,\lceil4B/3\rceil)$ guarantees the factor-two
stopping test and therefore $R(B)\le P_N(B)\le16R(B)$. For $N\ge B$ one
may take $k=1+2(B/N)^{1/3}$. This gives relative convergence of both
optimized values uniformly in the law and rarity. The exponent is a
sufficient rate. Its optimality is open.

## Proof

Fix an admissible quartet of sign priors $(q_L,q_H,q_v,q_w)$, and write
$m=(q_L+q_H)/2$, $\Delta=q_H-q_L$. For $0<e<1$, replace both references
by the admissible mixtures $v'=(1-e)q_v+em$ and $w'=(1-e)q_w+em$. Keep
the endpoints and hence their target separation. Let $K$ be the cap-$N$
ordinary information/work ratio for the original quartet. We prove
$$
 K_N^+(q_L,q_H;v',w')\ \le\
 \max\!\left\{\frac{K}{(1-e)^2},\frac{4}{e^2 N}\right\}.
 \tag{1}
$$

Fix any root-active policy stopped by $N$. Write $W_u$ for its expected
paid flips with sign prior $u$, and $p_u(s)$ for the probability of a
specific potential binary word $s$ on the coin. The policy's independent
seed can be conditioned on and then averaged. Both the work and each word
probability are affine in $u$.

Before the cap, $p_{v'}(s)\ge(1-e)p_{q_v}(s)$. Thus the sum of ordinary
stop rewards before the cap, under the new variance reference, is at most
$K W_{q_w}/(1-e)$. Indeed, after applying the dominance inequality to
each stopped word, adding the nonnegative ordinary terminal rewards gives
the information of the original policy. This also holds for zero-probability
words with the closed-perspective convention.

At a terminal word $s$, condition on the latent gap and sign. For a positive
sign the midpoint weight is $m$ and $v'\ge em$. Since
$|\Delta|\le 2m$, its contribution before multiplying by the word likelihood
is at most $4m/e$. For a negative sign, use $1-v'\ge e(1-m)$ and
$|\Delta|\le2(1-m)$ to get $4(1-m)/e$. These bounds include the zero
weights by continuity of the stated inequality with a zero contrast.
Multiplication by the respective nonnegative likelihoods and integration
give $g'_s\le4p_m(s)/e$ for the genie terminal reward.
Consequently the total terminal information is at most
$4\Pr_m(T=N)/e\le 4W_m/(eN)$, since reaching $N$ consumes $N$ paid
flips. This accounts for all stops at the cap, including a policy which
would choose to stop on the last observation.

Finally $W_{w'}=(1-e)W_{q_w}+eW_m$. Dividing the sum of the two information
bounds by this work gives (1) for every policy and therefore for its
supremum. When $K$ is infinite the corresponding original dual quotient
is zero, so only the finite case is needed for the next step.

Choose $e=1-1/k$. Under the stated cap condition, $4+4B/(e^2 N)\le4k^2$.
Equation (1) then gives
$$
 4+B K_N^+(q_L,q_H;v',w')\ \le\ k^2(4+BK).
$$
Divide the squared target separation by these two denominators and optimize
over the original quartet. The finite dual characterization of $P_N^2$
and the definition of $G_N^2$ give $P_N\le kG_N$. The middle inequalities
and $G_N/8\le R\le P_N$ are the established minimax brackets.

For $k=2$ the cap condition is $N\ge4B/3$. For $t=(B/N)^{1/3}\le1$ and
$k=1+2t$, $(1-1/k)^2(k^2-1)=16t^3(1+t)/(1+2t)^2\ge t^3$.

## Scope

Regularization depends on the requested comparison factor. The theorem
compares the **optimized** values. A fixed unregularized quartet can have
infinite latent divergence and an infinite genie ratio at every cap.
The work bound charges every first observation and revisit. A cap of order
$B$ can still leave a large conic program, and a floating-point solver
output does not certify a feasible policy or a dual bound.
