# Editorial handoff

Manuscript and protocol notes are maintained locally and excluded from the code submission. When describing these experiments, preserve the distinctions below. These experiments do not establish a new theorem or an extension of an existing theorem's scope.

- The experiment checks non-spikiness of paired errors and autonomous adaptive schedules. It does not compare adaptive and prescribed schedules as competing optimizers.
- The population is the specified fixed distribution on $K=32768$ atoms. It is not certified as a continuous Gaussian approximation. Sampling is with replacement even when $N=K$.
- Particles are $32\times2$ matrices, and factorization uses $A=\mathbb E[\tanh W]$. The Gaussian field has rank at most 64 even for continuous distributions. State this finite-feature simplification explicitly.
- $A_{\rm sp}^{\rm rec}$ is a maximum over recorded common-active times, not an all-time guarantee or a measure of the spread of particle positions. Small spikiness does not imply small trajectory or returned-state error.
- Distinguish same-time $r_t$, returned-candidate $r_{\rm out}$ at possibly different times, the objective gap, and the absolute objective. The executed terminal state and returned pre-jump candidate are also different objects.
- Jumps are coupled by attempt index, not physical time. The draft does not assert adaptation to a common physical-time filtration or apply the prescribed-schedule theorem to adaptive schedules.
- Retain the large position discrepancies at smaller $N$, nonmonotonicity, and the unmatched attempt. All three trials are reported and no convergence rate is fitted.
- Inspection-grid refinement changes an individual returned objective by up to approximately $4.89\times10^{-6}$, comparable to the small gaps at the largest $N$. Do not present those gaps as precision-independent scaling evidence.

Use the timestamped, content-hashed PDFs in `report/figures/`. Full hashes are in `report/figure_manifest.json`. Main figure candidates are `time_tracking` and `returned_outputs`; `schedules` helps explain adaptive timing. `instantaneous_spikiness` differs from the running maximum.

Follow `README.md` for reproduction and packaging. Host-name collection and archived host-name metadata have been removed. Report text has been translated to English, while numerical analysis and plotting functions are unchanged. `PROVENANCE.json` records the original-to-packaged hashes. The exported ZIP excludes Git history and author metadata.

The lightweight package omits approximately 2.55 GB of state arrays. It supports redrawing the recorded figures and rerunning the complete simulation. Repeating saved-state audits directly requires the original state files, which can be hash-checked and included with `--states-root`. Do not claim that the lightweight archive contains those states or that a new production simulation was run for this delivery.
