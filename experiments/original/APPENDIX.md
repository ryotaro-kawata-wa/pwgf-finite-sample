# A numerical sanity check for non-spikiness and adaptive perturbations

## Purpose and scope

We examine two questions in a nonlinear matrix-factorization example: whether the paired particle errors remain non-spiky as the particle count increases, and how independently chosen adaptive perturbation times affect comparison with a population path. The experiment is a diagnostic for these questions, rather than a benchmark of optimization performance. We show every trial and particle count, including large discrepancies and unmatched perturbation attempts.

The population is a **specified finitely supported probability measure**, whose evolution can be computed by following all its atoms. Thus, population integrals require no additional Monte Carlo approximation. Time integration is still numerical. We do not identify this population with a continuous Gaussian law, take a numerical infinite-particle limit, or infer a convergence rate from the five particle counts. Moreover, the adaptive, attempt-index coupling below is outside the prescribed deterministic common-schedule setting of our tracking theorem.

## Objective and initial distribution

A particle is a matrix $W\in\mathbb R^{32\times 2}$, with $q=64$ scalar coordinates. All matrix norms below are Frobenius norms unless otherwise indicated. For a probability measure $\nu$ on this space, define

$$
A_\nu=\int \tanh(W)\,\nu(dW),\qquad
F(\nu)=f(A_\nu),\qquad
f(A)=\frac14\|AA^\top-M_*\|_F^2,
$$

where $\tanh$ acts entrywise. For $a=1,\ldots,32$, let

$$
(u_1)_a=\frac1{\sqrt{32}},\qquad
(u_2)_a=\frac{(-1)^{a-1}}{\sqrt{32}},\qquad
M_*=u_1u_1^\top+\frac12u_2u_2^\top.
$$

The target has rank two and nonzero eigenvalues $1$ and $1/2$. The minimum objective is zero: the factor $A_*=[u_1,u_2/\sqrt2]$ has all entries in $(-1,1)$, so the point mass at the entrywise matrix $\operatorname{arctanh}(A_*)$ realizes $A_\nu=A_*$. This is factorization through the **mean transformed particle**, not the objective $\int\|WW^\top-M_*\|_F^2\,\nu(dW)$.

Set $K=32768$. Generate $K/2$ independent matrices $Z_a$ with independent standard normal entries once, and define

$$
P_a(0)=Z_a,\quad P_{a+K/2}(0)=-Z_a
\quad(1\le a\le K/2),\qquad
\mu_0=\frac1K\sum_{a=1}^K\delta_{P_a(0)}.
$$

The atom generator is NumPy's `default_rng(20260925)`, drawing an array of shape `(K//2, 32, 2)` before appending its negative. We condition on this realized atom set and use it for every trial and every $N$. Antithetic pairing gives $A_{\mu_0}=0$ in exact arithmetic, hence zero initial population drift and $F(\mu_0)=5/16$. Floating-point summation need not give exactly zero.

For each trial, independently of the atom generator and population perturbation innovations, draw labels $I_1,\ldots,I_{32768}$ independently and uniformly from $\{1,\ldots,K\}$. For

$$
N\in\{2048,4096,8192,16384,32768\},\qquad
X_i^N(0)=P_{I_i}(0),\quad
\widehat\mu_t^N=\frac1N\sum_{i=1}^N\delta_{X_i^N(t)},
$$

use the first $N$ labels. Sampling is **with replacement**; $N=K$ therefore does not reproduce the population measure exactly. Particle counts within a trial share their initial-label prefixes and the population path; they are not independent repetitions. The three trial indices are $0,1,2$.

## Flow and Gaussian perturbations

Between jumps, both systems use their own current measure in the velocity field. Differentiating $f$ gives

$$
G(A)=\nabla f(A)=(AA^\top-M_*)A,\qquad
b_\nu(W)=-(1-\tanh^2 W)\odot G(A_\nu),
$$

where $\odot$ denotes entrywise multiplication. Accordingly,

$$
\dot P_a=b_{\mu_t}(P_a),\quad
\mu_t=\frac1K\sum_{a=1}^K\delta_{P_a(t)},\qquad
\dot X_i^N=b_{\widehat\mu_t^N}(X_i^N).
$$

For $F_N(X_1,\ldots,X_N)=F(N^{-1}\sum_i\delta_{X_i})$, the latter velocity is $-N\nabla_{X_i}F_N$, including the mean-field normalization. Integrals with respect to $\mu_t$ are the full $K$-atom averages. Classical fourth-order Runge–Kutta (RK4) approximates these ODEs.

To specify the jump covariance, let $\operatorname{vec}$ flatten a matrix in row-major order and put

$$
J_W=\operatorname{diag}\!\left(\operatorname{vec}(1-\tanh^2W)\right).
$$

The $64\times64$ matrix $L_A$ represents the derivative of $G$:

$$
L_A\operatorname{vec}(B)
=\operatorname{vec}\!\left((AA^\top-M_*)B+B(A^\top A)+AB^\top A\right).
$$

The integral Hessian kernel and its squared-operator covariance kernel are

$$
H_\nu(W,V)=J_W L_{A_\nu}J_V,\qquad
S_\nu=\int J_U^2\,\nu(dU),
$$

$$
C_\nu(W,V)
=\int H_\nu(W,U)H_\nu(V,U)^\top\,\nu(dU)
=J_W L_{A_\nu}S_\nu L_{A_\nu}^\top J_V.
$$

Here $S_\nu$ is diagonal. The kernel $H_\nu$ is the measure-interaction part of the Hessian; the spatial derivative of $J_W\operatorname{vec}(G(A_\nu))$ at fixed $A_\nu$ is not added to this jump kernel. In particular, these jumps do not use the square of the full Euclidean Hessian of $F_N$.

A centered Gaussian field with covariance $C_\nu$ can be sampled as

$$
\operatorname{vec}\bigl(\xi_\nu(W)\bigr)
=J_W L_{A_\nu}S_\nu^{1/2}z,\qquad z\sim\mathcal N(0,I_{64}),
$$

using the same $z$ at every evaluation point. A population jump with amplitude $\eta=0.2$ is

$$
\mu^+=(\operatorname{Id}+\eta\xi_{\mu^-})_\#\mu^-.
$$

The finite-particle marginal jump law is equivalently

$$
\operatorname{vec}(X_i^+-X_i^-)
=\frac{\eta}{\sqrt N}\sum_{j=1}^N
H_{\widehat\mu^-}(X_i^-,X_j^-)g_j,
\qquad g_j\overset{\mathrm{iid}}\sim\mathcal N(0,I_{64}).
$$

Indeed, the covariance of these increments is $\eta^2C_{\widehat\mu^-}(X_i^-,X_k^-)$. The implementation uses the equivalent 64-dimensional factorization, with the population/empirical coupling specified below.

This example has an explicit finite-rank simplification: the Gaussian field has rank at most 64 **even for a continuous measure** $\nu$. At the initial population mean, $L_0[B]=-M_*B$ has rank four. The experiment therefore tests state-dependent covariance sampling in a finite-feature model, not the approximation of a genuinely infinite-rank Gaussian field. Finite $K$ separately makes the chosen population computable; it does not remove the empirical errors in $A_\nu$, $S_\nu$, or the evaluation points.

## Autonomous adaptive schedule

The controller follows the gradient-trigger/wait/decrease-test pattern of Algorithm 1 in [Yamamoto, Kim, and Suzuki (2025)](https://arxiv.org/html/2509.16974v1#S4.SS2), with explicit numerical thresholds and a discrete inspection grid. Each system makes decisions from its **own** objective and gradient norm,

$$
g(\nu)=\left(\int\|b_\nu(W)\|_F^2\,\nu(dW)\right)^{1/2}.
$$

At $t=0$ and subsequent inspection times, a system that is not in a waiting window perturbs if $g(\nu)\le 0.01$. It saves the pre-jump measure $\nu^-$ and its objective, applies the jump, and evolves for $\tau=10$ units of flow time without another perturbation. At the end of that window:

$$
F(\nu^-)-F(\nu_{t+\tau})\le 0.001
\quad\Longrightarrow\quad
\text{stop and return the saved pre-jump measure }\nu^-.
$$

Otherwise, inspection resumes on the next grid tick; a passed decrease test does not permit a new jump on that same tick. The executed state is not rewound to the returned candidate. Attempt counts include the final attempt whose decrease test fails. A cap of $T=100$ applies; no new jump is initiated exactly at $T$. A run reaching the cap without a completed stopping test is labelled `horizon`, not a returned solution. Every system in the recorded experiment stopped before this cap.

| Setting | Main experiment | Integration refinement | Inspection refinement |
|---|---:|---:|---:|
| RK4 step $h$ | 0.05 | 0.025 | 0.025 |
| Inspection interval $\Delta$ | 0.1 | 0.1 | 0.05 |
| Population atoms $K$ | 32768 | 32768 | 32768 |
| Particle counts | All five above | All five above | All five above |
| Trials | 0, 1, 2 | 0, 1, 2 | 0, 1, 2 |
| Jump amplitude / wait / decrease threshold | 0.2 / 10 / 0.001 | Same | Same |

These thresholds were fixed using earlier prescribed-schedule experiments before inspecting these adaptive outcomes; they are not certified choices from a convergence theorem. All nine trial/resolution jobs are retained. We do not compare adaptive and prescribed schedules as competing optimizers.

## Coupling by attempt index

We first generate the population path independently of the empirical initial labels and save every attempted jump, including the last attempt. The empirical system's $j$th attempt is coupled to the population's $j$th attempt whenever that population attempt exists. Their physical times may differ. For this coupling only, let $P$ denote the population pre-state at attempt $j$, let $X_i$ be the empirical pre-state at its own attempt $j$, and set $Y_i=P_{I_i}$. These $Y_i$ are not in general the population particles at the empirical jump's physical time.

Write $L_P=L_{A_{\mu_P}}$, $S_P=S_{\mu_P}$ for the full population pre-state. Write $L_X,L_Y$ and $S_X,S_Y$ for the same quantities evaluated using the empirical measures of $X$ and $Y$. Define the diagonal matrices

$$
D_{XY}=\frac1N\sum_iJ_{X_i}J_{Y_i},\quad
T_Y=S_Y^{1/2},\quad B_{XY}=D_{XY}T_Y^{-1},
$$

$$
V_{XY}=\frac1N\sum_i
\left(J_{X_i}-D_{XY}S_Y^{-1}J_{Y_i}\right)^2
=S_X-B_{XY}B_{XY}^\top\succeq0.
$$

The implementation evaluates the sum of squares rather than subtracting nearly equal terms. It raises an error if a reference diagonal moment is nonpositive or nonfinite; it adds no covariance jitter. For the symmetric matrix $T_YL_YT_Y$, let $Q$ be its spectral sign, with the sign of zero set to $+1$. If

$$
T_YL_PS_P^{1/2}=U\Sigma V^\top
$$

is a full singular-value decomposition, set $R=UV^\top$, retaining an orthogonal completion in zero singular directions. With the population innovation $z_j$ and a fresh independent $z_{\mathrm{aux}}\sim\mathcal N(0,I_{64})$, use

$$
e_X=B_{XY}QRz_j+V_{XY}^{1/2}z_{\mathrm{aux}},\qquad
\operatorname{vec}(X_i^+-X_i^-)=\eta J_{X_i}L_Xe_X.
$$

Since $Q$ and $R$ are orthogonal,

$$
\operatorname{Cov}(e_X)
=B_{XY}B_{XY}^\top+V_{XY}=S_X,
$$

conditional on the corresponding pre-attempt data. This verifies the required empirical marginal covariance. Freshness is with respect to attempt-index history: existence and pre-state of population attempt $j$ depend on innovations preceding $z_j$, and we do not select attempts by whether their subsequent decrease test succeeds. This construction is not asserted to be adapted to a common physical-time filtration. If the empirical attempt has no population counterpart, we use a fresh independent Gaussian field with its own empirical covariance. Reference particles and tracking errors never enter the controller or drift.

For exact seed construction, `default_rng(SeedSequence(words))` uses the following words, where $s\in\{0,1,2\}$ is the trial:

| Stream | Seed words | Draw convention |
|---|---|---|
| Initial labels | `[81073, s, 0]` | One vector of length 32768; prefixes for smaller $N$ |
| Population innovations | `[81073, s, 1]` | 64 normal coordinates per population attempt |
| Empirical auxiliary | `[81073, s, 2, N]` | 64 normal coordinates at every empirical attempt, including an unused draw on unmatched attempts |
| Independent fallback | `[81073, s, 3, N]` | 64 normal coordinates only at unmatched attempts |

The same stream definitions are used for the refinements. The initial-atom generator is the separate seed specified above.

## Recorded diagnostics

For trajectory comparison, return to **common physical time** and define

$$
Y_i(t)=P_{I_i}(t),\quad
\delta_i(t)=X_i^N(t)-Y_i(t),\quad
r_t=\left(\frac1N\sum_i\|\delta_i(t)\|_F^2\right)^{1/2},
$$

$$
s_t=\frac{N^{-1}\sum_i\|\delta_i(t)\|_F^3}{r_t^3},\qquad
\Delta F_t=\left|F(\widehat\mu_t^N)-F(\mu_t)\right|.
$$

The instantaneous ratio $s_t$ quantifies concentration of the **paired errors**, not the spatial spread of the particles. For $r_t>0$, monotonicity of empirical $L^p$ norms gives $s_t\ge1$. A ratio near one is consistent with comparable error magnitudes across labels, but does not imply that $r_t$ is small.

We record every inspection time and both sides of every jump while both systems are active. Simultaneous jumps are grouped into one before/after pair. Pairwise diagnostics end at the earlier stopping time; each system's own objective is retained until its own stop. Omit $s_t$, but retain $r_t$, when

$$
r_t\le10^{-12}\max\!\left\{1,
\left(\frac1N\sum_i\|Y_i(t)\|_F^2\right)^{1/2}\right\}.
$$

Let $\mathcal R_N$ be these ordered common-active records, distinguishing pre- and post-jump values, and write $v\preceq u$ for their storage order. At record $u$, the plotted non-spikiness statistic is

$$
A_{\mathrm{sp}}^{\mathrm{rec}}(u)
=\max_{v\in\mathcal R_N:\,v\preceq u,\ s_v\ \mathrm{defined}}s_v,
$$

plotted against $\operatorname{time}(u)$, with an empty maximum omitted. The final recorded maximum is denoted $A_{\mathrm{sp}}^{\mathrm{rec}}$. This is an empirical analogue of the theorem's cubic non-spikiness constant, not a certified supremum over continuous time.

For returned candidates, let $X_i^{\mathrm{out}}$ and $P_a^{\mathrm{out}}$ be the saved empirical and population candidates, respectively. We separately report

$$
r_{\mathrm{out}}=\left(\frac1N\sum_i
\|X_i^{\mathrm{out}}-P_{I_i}^{\mathrm{out}}\|_F^2\right)^{1/2},\qquad
\Delta F_{\mathrm{out}}=
\left|F(\widehat\mu^{N,\mathrm{out}})-F(\mu^{\mathrm{out}})\right|.
$$

The candidate times can differ, so $r_{\mathrm{out}}$ is not $r_t$ at a shared stopping time. There is no orthogonal alignment in either $r_t$ or $r_{\mathrm{out}}$. Neither a small objective gap nor a small objective value uniquely determines particle positions, since $F$ depends only on the mean transformed factor and its product.

## Results and numerical checks

All 15 empirical systems and the three population systems in the main experiment stopped. Across all main common-active records, the largest $A_{\mathrm{sp}}^{\mathrm{rec}}$ was **1.017416**. This is evidence of non-spiky paired errors in these runs, rather than an all-path or high-probability bound.

The table includes every main condition. $F_{\mathrm{out}}$ is the empirical returned objective, whose global minimum is zero; it is distinct from the empirical/population gap $\Delta F_{\mathrm{out}}$. Figures and tables use rounded display values; machine-readable files retain full precision.

| Trial | $N$ | Attempts | $r_{\mathrm{out}}$ | $\Delta F_{\mathrm{out}}$ | $F_{\mathrm{out}}$ | $A_{\mathrm{sp}}^{\mathrm{rec}}$ |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 2048 | 1 | 2.296149 | 2.873598e-05 | 1.398578e-04 | 1.010196 |
| 0 | 4096 | 1 | 2.356095 | 1.377644e-05 | 1.248982e-04 | 1.010811 |
| 0 | 8192 | 2 | 0.152965 | 1.051431e-05 | 1.216361e-04 | 1.013710 |
| 0 | 16384 | 2 | 0.147749 | 6.316573e-06 | 1.174384e-04 | 1.016067 |
| 0 | 32768 | 2 | 0.041268 | 4.387975e-06 | 1.155098e-04 | 1.017416 |
| 1 | 2048 | 1 | 2.404608 | 2.004515e-05 | 1.375517e-04 | 1.006928 |
| 1 | 4096 | 1 | 1.141178 | 5.455890e-06 | 1.229624e-04 | 1.006992 |
| 1 | 8192 | 2 | 0.075332 | 1.292916e-06 | 1.162136e-04 | 1.014015 |
| 1 | 16384 | 2 | 0.061789 | 4.994117e-06 | 1.125124e-04 | 1.013978 |
| 1 | 32768 | 2 | 0.045958 | 5.402760e-06 | 1.121038e-04 | 1.011761 |
| 2 | 2048 | 1 | 0.764154 | 2.543435e-05 | 1.408861e-04 | 1.008835 |
| 2 | 4096 | 1 | 2.068589 | 7.622123e-06 | 1.230739e-04 | 1.008689 |
| 2 | 8192 | 2 | 2.042344 | 6.438086e-06 | 1.218899e-04 | 1.010973 |
| 2 | 16384 | 3 | 0.174628 | 3.953000e-06 | 1.194048e-04 | 1.013195 |
| 2 | 32768 | 2 | 0.038686 | 1.229069e-06 | 1.142227e-04 | 1.012479 |

At $N=32768$, the three returned-candidate discrepancies were approximately $0.0413$, $0.0460$, and $0.0387$, and the objective gaps were between $1.23\times10^{-6}$ and $5.40\times10^{-6}$. However, the dependence on $N$ was not monotone; six smaller-$N$ conditions had $r_{\mathrm{out}}>1$. We therefore do not fit a scaling exponent or assert asymptotic convergence. Small objective gaps also do not by themselves establish close particle configurations.

The schedules explain why same-time peak errors require care. At $N=2048$ and $4096$, all three trials began above the gradient threshold and did not perturb at $t=0$, whereas the population and all $N\ge8192$ systems did. Trial 2 with $N=16384$ made three attempts, the last using the independent fallback; the population made two. Even at $N=32768$, recorded $r_t$ peaks were about $0.584$–$0.601$, despite the smaller returned-candidate errors. A lag between two jumps can expose a full jump-sized mismatch over a short interval. Shrinking such a lag does not in general force the same-time supremum error to shrink. We therefore plot physical-time trajectories and event times explicitly.

We distinguish ODE-step sensitivity from inspection-grid sensitivity. Halving the RK4 step while keeping the inspection interval fixed preserved all attempt counts, jump times, and stopping times. Across the three trials, the maximum RMS change in a saved returned state, including population and empirical states, was $4.20\times10^{-10}$ or less; the maximum relative change in $r_t$ over matched stored records was $2.54\times10^{-8}$ or less.

Next, halving the inspection interval from $0.1$ to $0.05$ while holding the RK4 step at $0.025$ preserved attempt counts, but shifted some jump and stopping times by $0.05$. The maximum returned-state RMS change was $4.95\times10^{-4}$ or less, and the maximum change in an empirical returned objective was $4.89\times10^{-6}$ or less. Changes in $r_t$ at matched stored time/phase records reached approximately $0.5004$ near asynchronous jumps. Thus, the small largest-$N$ objective gaps are comparable to the observed sensitivity of individual returned objectives to the inspection grid; they should not be presented as a precision-independent rate measurement. These refinements are numerical consistency checks, not rigorous discretization-error bounds or a certified continuous-trigger limit.

The implementation additionally checks the reduced covariance identity, the polar factorization, controller timing and decrease tests, saved-candidate semantics, and preservation of duplicate initial labels. The population replay agrees exactly with its independently generated pre/post-jump snapshots and terminal state. All nine archived job audits passed. Fourteen unit tests cover derivatives, covariance construction, coupling, and adaptive-control behavior. These checks validate the implemented finite example; they do not verify every hypothesis of the paper's tracking theorem or certify mathematical convergence of an adaptive scheme.

## Figures and captions

The following are the original vector PDF exports; each filename contains its generation time in JST and the first 12 hexadecimal digits of its own SHA-256. The matching PNGs are also supplied. `report/figure_manifest.json` records the complete SHA-256 values and the original data/code provenance.

**Figure S1.** **Common-time tracking and non-spikiness.** Columns are the three trials; colors are particle counts. Rows show paired RMS error, absolute population/empirical objective gap, and the running recorded maximum of the cubic spikiness ratio. Curves end at the earlier stopping time. Dots in the top row mark empirical jumps; dotted vertical lines mark population jumps. Vertical segments show stored pre/post-jump values. The lower row is a recorded maximum, not a continuous-time bound.

[Original PDF](report/figures/adaptive_K32768_time_tracking_20260925-220738JST_402967415f7c.pdf)

SHA-256: `402967415f7cfc9d9aa3b9d50d1ac7d10c18ced3a7df003f58a96256fe8f19d0`.

**Figure S2.** **Instantaneous error spikiness.** The cubic-to-quadratic moment ratio at recorded common-active times, with one panel per trial. Near-zero denominators are omitted. This differs from the running maximum in the tracking figure.

[Original PDF](report/figures/adaptive_K32768_instantaneous_spikiness_20260925-220740JST_e1f6acdcbae6.pdf)

SHA-256: `e1f6acdcbae646d2d4f74bb879f93213ef3bba70c5df82b0aa0fbce7fb58e0ab`.

**Figure S3.** **Independently chosen schedules.** Each row shows one system until its stopping time. Circles denote attempts whose subsequent decrease test passes; triangles denote pre-jump candidates returned by the final failed decrease test; crosses mark the later stopping time. An open square marks an empirical attempt without a population counterpart. Population and empirical jumps are coupled by attempt index, not forced to occur at the same time.

[Original PDF](report/figures/adaptive_K32768_schedules_20260925-220741JST_41bda0385c70.pdf)

SHA-256: `41bda0385c70878636949f883817d6b0ceb2abe1b65dac5a71cfc0772c26c4de`.

**Figure S4.** **Executed objectives and returned candidates.** Each curve continues to that system's own stop; black denotes the population. Stars mark the saved pre-jump candidates at their candidate times. The minimum objective is zero. The executed trajectory is not rewound at stopping.

[Original PDF](report/figures/adaptive_K32768_objectives_20260925-220741JST_f5f6c2a2d261.pdf)

SHA-256: `f5f6c2a2d26175776bd862da7f870bbb8b75aa2c64f6246f34f806be10827109`.

**Figure S5.** **Returned outputs as particle count increases.** Each line is one trial. Panels show returned-candidate paired RMS error, returned-objective gap, and the maximum recorded common-active spikiness ratio. Candidate comparisons can use different candidate times. All five particle counts and all three trials are retained; no rate is fitted. Here one axis unit “k” denotes 1024 particles.

[Original PDF](report/figures/adaptive_K32768_returned_outputs_20260925-220743JST_9ed1d032ebdb.pdf)

SHA-256: `9ed1d032ebdbde11e52f4370e7cf27db7a171174e60cfb386d8dfee8cd4e3653`.

## Reproducibility

The accompanying package contains the numerical implementation, exact configurations and seeds, all scalar time series and event logs for the nine jobs, the full-precision analysis, original PDF/PNG figures, and plotting code. The original environment used Python 3.12.4, NumPy 1.26.4 with MKL 2023.1, and Matplotlib 3.8.4 on Linux x86-64, with one BLAS/OpenMP thread per worker and up to three CPU workers. No GPU was used. `README.md` describes file-integrity verification, figure regeneration, and a full simulation rerun; `ORIGINAL_ENVIRONMENT.json` records observed scientific-package builds.

The lightweight package omits the nine compressed particle-state snapshots (approximately 2.55 GB in total), but records their full hashes and provides a complete rerun path that regenerates them. Those snapshots are needed to independently repeat the saved-state audits without rerunning the simulations; they are not needed to redraw the archived figures from the supplied scalar records and analysis. The packaging tool also supports a full package with hash-verified original snapshots.

Hashes authenticate archived bytes. They are not a guarantee of bitwise agreement after rerunning on another numerical library or platform. In particular, near-zero eigenspaces and full-SVD orthogonal completions can be represented differently across numerical environments. Regenerated figure timestamps and PDF metadata also change the figure hashes. Accordingly, the package distinguishes original-file integrity, reproduction of recorded plots, and numerical reruns.
