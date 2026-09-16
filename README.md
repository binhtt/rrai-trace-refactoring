# RRAI Trace-Preserving Refactoring Artifact

This repository contains the executable artifact and manuscript-facing results for:

> **A Calculus of Trace-Preserving Refactorings for Reactive Rule-Based Artificial Intelligence Systems**

The artifact implements the priority-aware nondeterministic semantics, the four supported refactoring classes, exhaustive proof-obligation checking over the represented finite domain, correspondence construction, bidirectional outgoing-transition comparison, sampled finite-trace validation, counterexample generation, and the reported execution-volume experiment.

## Reproduced claims

- 16 Boolean state predicates: 65,536 states.
- Three events: `sensor`, `timer`, and `watchdog`.
- Complete proof-obligation domain: 196,608 state-event contexts.
- Four preservation-valid transformations pass all applicable obligations.
- No divergence is observed for the valid transformations in 10,000 sampled executions of length 20.
- Three negative controls fail their targeted obligations and produce counterexamples.
- Sampled divergence rates are 24.66%, 24.59%, and 49.29%.

## Repository layout

```text
.
├── src/rrai_refactoring.py       # complete executable artifact
├── results/manuscript/           # results reported in the paper
├── tests/test_artifact.py        # semantic and smoke tests
├── CITATION.cff                  # citation metadata
├── LICENSE                       # MIT license for the artifact code
└── requirements.txt              # plotting dependency
```

## Requirements

- Python 3.10 or later
- `matplotlib` for generating Figure 3

Install the dependency:

```bash
python -m pip install -r requirements.txt
```

The verification and CSV/JSON generation logic otherwise uses only the Python standard library. `pandas` and `IPython` are optional and are used only for notebook-style result previews.

## Quick verification

The quick mode still checks the complete 196,608-context proof-obligation domain, but reduces sampled executions and scalability repetitions:

```bash
python src/rrai_refactoring.py --quick
```

Run the tests with:

```bash
python -m unittest discover -s tests -v
```

## Reproduce the manuscript configuration

From the repository root, run:

```bash
python src/rrai_refactoring.py
```

The default configuration uses:

- random seed `20260723`;
- 10,000 sampled executions per transformation;
- trace length 20;
- scalability sizes 100, 500, 1,000, 2,000, 5,000, and 10,000;
- 30 repetitions per scalability size.

Outputs are written to `results/`. Runtime measurements can vary by machine, while proof-obligation outcomes and seeded divergence counts should reproduce the reported logical and behavioural results.

## Semantics implemented

The implementation distinguishes the stored acyclic priority graph `G` from its semantic transitive closure `G+`. For every state-event context, it returns all transitions induced by maximal enabled rules. It does not impose a globally fixed selection function. If no rule is enabled, it generates the idle transition.

Trace comparison is correspondence-based and bidirectional: every outgoing transition in either system must have a matching transition in the other system with the same source state, event, action, and successor state, and with rule labels related by the refactoring certificate.

## Supported transformations

1. Rule decomposition
2. Rule merging
3. Rule elimination
4. Priority adjustment

The included negative controls intentionally violate priority compatibility, maximal-rule preservation, or guard/action preservation.

## Result files

The `results/manuscript/` directory contains the exact summary tables reported in the manuscript. A full run additionally generates detailed JSON counterexamples, raw scalability repetitions, divergence-position data, and Figure 3 in PNG and PDF formats.

## Authors

- Thanh-Binh Trinh, Phenikaa University
- Van-Cuong Nguyen, Phenikaa University
- Nguyen Viet Ha, VNU University of Engineering and Technology

## License

The artifact code is released under the MIT License. The manuscript and publisher-formatted article are not covered by this software license.
