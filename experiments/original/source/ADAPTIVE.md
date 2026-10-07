# Autonomous adaptive schedule: frozen experimental protocol

This extension was agreed with the author before execution. It leaves the
prescribed-schedule code and historical outputs intact. No manuscript is edited.

## Model and parameters

The model, antithetic construction of the initial population, iid sampling with
replacement, and q=64 particle coordinates are as in README.md. K=32768 is the support size of the
chosen population law, not an approximation asserted to equal a continuous law.
K is fixed across all N and equals the largest N. This replaces the initial
K=16384 adaptive protocol at the author's request; its completed results are
retained separately. Changing K changes the population law. The RNG stream names
are retained, but the sampled atom labels/states need not match across K.
N=2048,4096,8192,16384,32768 and trials=0,1,2 are fixed;
none is discarded. The initial population seed is 20260925; trial seed is 81073.

Each system independently observes its own Wasserstein gradient norm (the RMS
of particle velocities), with threshold 0.01. Ordinary particle-parameter
gradient norms are not used: they contain an extra N-dependent normalization.
The first check is at t=0; later checks occur every 0.1 units. Jump strength is
fixed at 0.2. After each attempted jump, there is a 10-unit waiting window. Save
the pre-jump candidate and its objective. At the window's end, if candidate F
minus current F <= 0.001, return that candidate and stop. Otherwise resume
checking on the next check tick. A successful decrease test does not trigger a
new jump on that same tick (strict cooldown). All attempted jumps, including
the final unsuccessful attempt, are retained and numbered chronologically.

This is the control logic of Yamamoto, Kim, Suzuki (2025), Algorithm 1, with
explicit numerical parameters and a discrete inspection grid:
https://arxiv.org/html/2509.16974#S4.SS2
We interpret its inconsistent cooldown spelling as the same wait time and save
the pre-perturbation candidate explicitly. RK4 approximates the between-jump
flow; this is not the Euler algorithm or a certified continuous-trigger limit.
These numerical thresholds are informed by the previous prescribed data, not
selected after viewing adaptive outcomes. They are not theorem-certified.

T=100 is a fixed observation cap. A system that has not stopped is labelled
`horizon`, never counted as a returned solution. An attempt before T whose
waiting window ends after T is incomplete; no new attempt starts exactly at T.
There is no extra maximum-jump cap; the cooldown and T already bound the count.
The main RK4 step is 0.05. `integration_half` uses 0.025 with the same 0.1 check
grid. `trigger_half` also uses 0.025, but checks every 0.05. Thus integration
and event-grid changes can be examined separately, with all three seeds.

## Event-index coupling and independence

Generate the entire population path independently of empirical samples first,
saving every attempted jump's pre-state, Hessian, covariance statistic, and
fresh normal z_j. For empirical attempt j, use the existing `empirical_field`
with that frozen population pre-state and its sampled labels. The physical
times may differ. Never use the current same-clock reference state to form the
rotation: it may already contain z_j and invalidate the Gaussian calculation.

Population attempt j exists by T based only on z_<j. Its pre-state, and each
empirical pre-state/trigger for attempt j, use only past innovations. Given this
event-index history, the existing frozen-state covariance identity applies to
fresh z_j and the empirical auxiliary normal. If population attempt j does not
exist, use the self-state population_field factor with a fresh independent
fallback normal. Existence refers to an attempted jump, not one that later
passes the decrease test. Selecting only successful attempts would condition
on the current innovation and is forbidden.

Empirical drift and controllers receive only their own states. Reference
particles and tracking diagnostics never enter control. The population is
replayed alongside empirical systems solely for diagnostics; equality at its
saved events and terminal point is checked bitwise. No full K-by-time path is
stored. This event-index construction is not the paper's synchronized-time
tracking theorem applied to adaptive schedules.

## Measurements and figures

At a common physical time, Y_i is the population atom with the same initial
label as X_i. Record r=sqrt(mean(||X_i-Y_i||_F^2)), absolute objective gap, and
s=mean(||X_i-Y_i||_F^3)/r^3. The instantaneous s is distinct from A_sp, the maximum
over recorded common-active times. A running maximum is labelled as such.
Values below the same numerical r threshold as the original experiment are
not assigned a spikiness ratio. Every check and both sides of each jump in
either system are recorded; simultaneous jumps have only one before/after
pair, avoiding a fictitious intermediate mismatch.

Pairwise path comparisons end when either system stops. Each system's own
objective is retained until its own stop. The executed state is never rewound
to draw a curve through a returned candidate. Returned candidates from their
different times are compared separately, using the same initial labels; this
is an output error, not a same-time trajectory error. The executed final state
and the returned pre-jump candidate are stored separately in states.npz.

Main figures use physical time on the horizontal axis. Same-time sup errors
are supplementary diagnostics: asynchronous jumps can retain an O(jump-size)
peak even when their times approach each other. Show individual seeds, event
times, stop times, and unmatched attempts. Do not smooth jump discontinuities.
The experiment does not establish a rate, adaptive superiority, or an all-path
non-spikiness guarantee from three seeds and a finite observation grid.

Each PDF/PNG filename includes its creation time in JST and the first 12 hex
digits of its own SHA-256. A manifest records full file hashes, input data,
configuration, source snapshots, plotting code, and numerical checks. Retain
previous artifacts rather than overwriting them.

## Execution

Run unittest discovery in this directory, then:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
python run_adaptive_protocol.py --out /new/exclusive/output/path --workers 3
```

NumPy is the only simulation dependency; figures additionally use Matplotlib.
All output roots are created exclusively. No external model downloads, GPU,
package installation, or changes to the server environment are required.
