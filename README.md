# RRAI Trace-Preserving Refactoring Artifact

This repository contains the executable artifact and experimental summaries accompanying the manuscript:

> **A Calculus of Trace-Preserving Refactorings for Reactive Rule-Based Artificial Intelligence Systems**

The artifact implements priority-aware nondeterministic semantics, four supported refactoring classes, exhaustive proof-obligation checking over the represented finite domain, rule-correspondence construction, bidirectional outgoing-transition comparison, sampled finite-trace validation, counterexample generation, and an execution-volume scalability experiment.

## Reported results

- 16 Boolean state predicates yield 65,536 states.
- Three environmental events: `sensor`, `timer`, and `watchdog`.
- The complete proof-obligation domain contains 196,608 state–event contexts.
- Four preservation-valid transformations pass all applicable proof obligations.
- Each valid transformation exhibits zero divergences in 10,000 sampled executions of length 20.
- Three intentionally invalid controls fail their targeted obligations and yield finite-domain counterexamples.
- Sampled divergence rates are 24.66% for invalid merging, 24.59% for invalid priority adjustment, and 49.29% for unsafe decomposition.

Formal preservation follows from satisfaction of the sufficient proof obligations. The absence of sampled divergence is complementary empirical evidence, not a proof of equivalence.

## Repository layout

| Path | Contents |
|---|---|
| `src/rrai_refactoring.py` | Executable verification and experimentation code |
| `tests/test_artifact.py` | Semantic and proof-obligation tests |
| `results/manuscript/` | Stored experimental summaries accompanying the manuscript |
| `README.md` | Artifact description and reproduction instructions |
| `CITATION.cff` | Citation metadata |
| `LICENSE` | MIT License |
| `requirements.txt` | Plotting dependency |

## Requirements

- Python 3.10 or later
- `matplotlib>=3.7` for generating Figure 3

Install the dependency:

```bash
python -m pip install -r requirements.txt
```

The verification and CSV/JSON generation logic otherwise uses only the Python standard library. `pandas` and `IPython` are optional and used only for notebook-style result previews.

The dependency specification does not pin the original Google Colab environment. Runtime measurements depend on the Python version, dependencies, hardware, and system load.

## Quick verification

Run commands from the repository root.

Quick mode checks the complete 196,608-context proof-obligation domain but reduces behavioural validation to 200 sampled executions per transformation and scalability to two repetitions at each of the sizes 100 and 500:

```bash
python src/rrai_refactoring.py --quick
```

Quick-mode results should not be substituted for the manuscript's 10,000-execution results or 30-repetition timing summaries.

Run the tests:

```bash
python -m unittest discover -s tests -v
```

The tests check internal semantic assertions, the complete domain size, and the outcomes of the valid and invalid proof-obligation controls. They do not reproduce the full behavioural or scalability experiments.

## Reproduce the manuscript configuration

Run:

```bash
python src/rrai_refactoring.py
```

The default configuration uses:

- input-sampling seed `20260723`;
- 10,000 sampled executions per transformation;
- trace length 20;
- scalability sizes 100, 500, 1,000, 2,000, 5,000, and 10,000;
- 30 repetitions per scalability size.

Initial states are sampled with independently equiprobable Boolean predicates, except that `hazardFlag` is set to `false`. Events are sampled independently and uniformly from the three-event set. The same sampled initial states and event words are reused across all transformation pairs.

Separate seeded pseudo-random generators select matching transition pairs for sampled continuation. For scalability, input seeds vary by repetition as implemented in the source.

Generated outputs are written directly to `results/` and do not overwrite the stored summaries in `results/manuscript/`.

The seeded behavioural validation has been rerun with this artifact and reproduced the reported divergence counts. Runtime measurements differ across execution environments; a rerun is not expected to reproduce the original Colab timings exactly.

## Semantics implemented

The implementation distinguishes the stored acyclic priority graph `G` from its semantic transitive closure `G+`. Priority edges are oriented from lower-priority rules to higher-priority rules.

For every state–event context, the operational semantics returns all transitions induced by maximal enabled rules. It does not impose a fixed selection function. If no rule is enabled, it generates the idle transition, which preserves the state.

Finite traces start in:

```text
I = {s ∈ S | hazardFlag(s) = false}
```

The admissible finite event language is:

```text
L = E*
```

Transition comparison is correspondence-based and bidirectional: every outgoing transition in either system must have a matching transition in the other system with the same source state, event, executed action, and successor state, together with rule labels related by the refactoring certificate. Idle transitions match only idle transitions.

After the complete bidirectional outgoing-transition check succeeds, one matching transition pair is selected using a seeded pseudo-random generator solely to continue a common sampled prefix. This sampling choice does not define the operational semantics or exclude other admissible transitions from the local comparison.

Sampled validation follows one common prefix for each input instance; it does not explore every possible nondeterministic execution path.

A failed proof obligation means that the applicable sufficient preservation conditions are not satisfied. It does not alone establish finite-trace inequivalence. Finite-domain counterexamples identify local unmatched transitions; their reachability under the initial-state set and admissible event language must be considered separately.

## Supported transformations

1. Rule decomposition
2. Rule merging
3. Rule elimination
4. Priority adjustment

The main preservation-valid sequence applies priority adjustment, merging, and decomposition. Elimination is evaluated independently using a controlled extension containing a shadow rule.

The three negative controls intentionally violate:

- external priority compatibility for merging;
- maximal-enabled-rule preservation for priority adjustment;
- guard partitioning and action preservation for decomposition.

## Result files

The `results/manuscript/` directory contains seven stored summary files:

| File | Contents |
|---|---|
| `behavioural_validation.csv` | Sample counts, divergence counts, rates, and recorded timings |
| `proof_obligations.csv` | Verification status, domain size, failed obligations, and counterexample availability |
| `table2_structural_changes.csv` | Rule counts and stored priority-graph edge counts |
| `table3_valid_transformations.csv` | Results for preservation-valid transformations |
| `table4_invalid_transformations.csv` | Failed obligations and sampled divergence results |
| `table5_counterexamples.csv` | Summary of obligation failures and counterexample availability |
| `table6_scalability.csv` | Aggregate execution-time statistics |

Abbreviations in Table IV:

- `PC`: `PriorityCompatibility`
- `MRP`: `MaximalRulePreservation`
- `GP`: `GuardPartition`
- `AP`: `ActionPreservation`

A full run additionally generates detailed JSON counterexamples, raw per-repetition scalability timings, divergence-position data, experiment metadata, and Figure 3 in PNG and PDF formats.

The committed summaries preserve the supplied experimental results. They are not raw execution logs. Newly generated timings and diagnostic outputs belong to the rerun and should be distinguished from the original manuscript experiment.

Generated CSV, JSON, PNG, and PDF files directly under `results/` are ignored by the supplied `.gitignore`. To publish selected generated outputs, explicitly include them in version control.

## Scalability scope

The scalability experiment measures bidirectional outgoing-transition validation for the valid decomposition pair. Input generation is outside the timed region.

Only the number of sampled traces varies. Trace length and rule-base structure remain fixed. The experiment therefore evaluates execution-volume scaling, not scaling with increasing rule count, guard complexity, or priority-graph density.

## Authors

- Thanh-Binh Trinh, Phenikaa University
- Van-Cuong Nguyen, Phenikaa University
- Nguyen Viet Ha, VNU University of Engineering and Technology

## Citation

Citation metadata is provided in `CITATION.cff`. Until publication details are available, cite the software repository. The associated manuscript title is given above.

## License

The artifact software is released under the MIT License; see `LICENSE`.

The manuscript and any publisher-formatted article are not covered by this software license.
