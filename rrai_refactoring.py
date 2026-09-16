"""
RRAI Refactoring Verification Framework
Algorithm-1-aligned reproducibility version

This version aligns the executable artifact with the calculus and evaluation
described in the manuscript "A Calculus of Trace-Preserving Rule
Refactorings for Reactive Rule-Based Artificial Intelligence Systems".

Reviewer-1 alignment points:
1. Guards are predicates over (state, event), matching g_r : S x E -> Bool.
2. A valid merge is a true many-to-one transformation: r11,r4 -> one rule r15.
3. The invalid-priority control removes r9 < r3; it does not reverse the edge.
4. The invalid-merge target is well formed; no dangling priority edge is retained.
5. Algorithm 1 is implemented end-to-end for the four supported transformation
   classes: detection, changed-rule identification, obligation checking,
   correspondence construction, witnesses, and counterexample search.
6. Algorithm 1 is checked over the complete represented finite domain D = S x E
   (all 16 Boolean state predicates paired with all three events).
7. Scalability measures the full correspondence-based behavioural-validation
   procedure, rather than trace generation alone.
8. Output filenames are fixed and documented for reproducibility.
9. The stored priority graph G is distinguished from its semantic strict
   partial order prec = G+ (transitive closure).
10. The operational semantics returns the complete set of outgoing transitions;
    it does not use a fixed select function.
11. Sampled traces start in the explicit initial-state set I and use words from
    the admissible finite event language L = E*.
12. Behavioural comparison is bidirectional over outgoing transition sets, and
    a counterexample records the direction of an unmatched transition.
"""

from __future__ import annotations

from dataclasses import dataclass, asdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Set, Tuple
import ast
import csv
import json
import random
import statistics
import time


# ============================================================
# PART 1. CORE SEMANTICS
# ============================================================

State = Dict[str, bool]
Priority = Set[Tuple[str, str]]


@dataclass(frozen=True)
class Rule:
    """
    Reactive rule r = (g_r, a_r).

    The guard is evaluated over both state and event.  Event conditions are
    therefore represented inside the guard expression, matching the manuscript's
    formal type g_r : S x E -> {true,false}.
    """
    name: str
    guard: str
    action: str


@dataclass
class RuleBase:
    rules: List[Rule]
    priority: Priority  # generating edges (lower, higher)

    def by_name(self) -> Dict[str, Rule]:
        return {r.name: r for r in self.rules}


@dataclass(frozen=True)
class Transition:
    event: str
    rule: Optional[str]
    action: str
    before: Tuple[Tuple[str, bool], ...]
    after: Tuple[Tuple[str, bool], ...]


@dataclass
class FailureRecord:
    obligation: str
    witness: Any


@dataclass
class VerificationResult:
    status: str  # Pass | Fail | Unsupported
    transformation: str
    failed: List[FailureRecord]
    counterexample: Optional[dict]
    changed_rules: dict
    correspondence: Set[Tuple[str, str]]
    domain_size: int

    @property
    def passed(self) -> bool:
        return self.status == "Pass"

    def to_jsonable(self) -> dict:
        return {
            "status": self.status,
            "transformation": self.transformation,
            "failed": [asdict(x) for x in self.failed],
            "counterexample": self.counterexample,
            "changed_rules": self.changed_rules,
            "correspondence": sorted([list(x) for x in self.correspondence]),
            "domain_size": self.domain_size,
        }


class GuardEvaluator(ast.NodeVisitor):
    """Safe evaluator for the Boolean guard fragment used by the artifact."""

    def __init__(self, state: Mapping[str, bool], event: str):
        self.state = state
        self.event = event

    def visit_Expression(self, node):
        return self.visit(node.body)

    def visit_Name(self, node):
        if node.id == "event":
            return self.event
        if node.id in ("True", "False"):
            return node.id == "True"
        return bool(self.state.get(node.id, False))

    def visit_Constant(self, node):
        if isinstance(node.value, (bool, str)):
            return node.value
        raise ValueError("Only Boolean and string constants are supported")

    def visit_BoolOp(self, node):
        vals = [bool(self.visit(v)) for v in node.values]
        if isinstance(node.op, ast.And):
            return all(vals)
        if isinstance(node.op, ast.Or):
            return any(vals)
        raise ValueError("Unsupported Boolean operator")

    def visit_UnaryOp(self, node):
        if isinstance(node.op, ast.Not):
            return not bool(self.visit(node.operand))
        raise ValueError("Unsupported unary operator")

    def visit_Compare(self, node):
        # The artifact only needs event == "..." and event != "...".
        if len(node.ops) != 1 or len(node.comparators) != 1:
            raise ValueError("Only single comparisons are supported")
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        op = node.ops[0]
        if isinstance(op, ast.Eq):
            return left == right
        if isinstance(op, ast.NotEq):
            return left != right
        raise ValueError("Only == and != comparisons are supported")

    def generic_visit(self, node):
        raise ValueError(f"Unsupported guard syntax: {ast.dump(node)}")


@lru_cache(maxsize=None)
def _parse_guard(expr: str):
    return ast.parse(expr, mode="eval")


@lru_cache(maxsize=None)
def _compile_guard(expr: str):
    """
    Validate the small guard language once, then compile it for efficient
    repeated evaluation during exhaustive checking and Monte-Carlo runs.
    """
    tree = _parse_guard(expr)
    allowed = (
        ast.Expression, ast.Name, ast.Load, ast.Constant,
        ast.BoolOp, ast.And, ast.Or, ast.UnaryOp, ast.Not,
        ast.Compare, ast.Eq, ast.NotEq,
    )
    for node in ast.walk(tree):
        if not isinstance(node, allowed):
            raise ValueError(f"Unsupported guard syntax: {ast.dump(node)}")
        if isinstance(node, ast.Constant) and not isinstance(node.value, (bool, str)):
            raise ValueError("Only Boolean and string constants are supported")
    return compile(tree, "<guard>", "eval")


def eval_guard(expr: str, state: Mapping[str, bool], event: str) -> bool:
    env = dict(state)
    env["event"] = event
    # The full verification domain supplies every Boolean state variable.
    # For robustness in auxiliary calls, unspecified predicates default to False.
    code = _compile_guard(expr)
    try:
        return bool(eval(code, {"__builtins__": {}}, env))
    except NameError:
        complete = {name: False for name in PREDICATES} if "PREDICATES" in globals() else {}
        complete.update(env)
        return bool(eval(code, {"__builtins__": {}}, complete))


def event_guard(event: str, state_guard: str = "True") -> str:
    """Convenience syntax for Table-1-style rules with one triggering event."""
    return f"(event == {event!r}) and ({state_guard})"


def R(name: str, event: str, guard: str, action: str) -> Rule:
    return Rule(name=name, guard=event_guard(event, guard), action=action)


def enabled_rules(rb: RuleBase, state: State, event: str) -> List[Rule]:
    return [r for r in rb.rules if eval_guard(r.guard, state, event)]


@lru_cache(maxsize=None)
def _closure_cached(priority_tuple: Tuple[Tuple[str, str], ...]):
    closure = set(priority_tuple)
    changed = True
    while changed:
        changed = False
        new = set(closure)
        for a, b in closure:
            for c, d in closure:
                if b == c and (a, d) not in new:
                    new.add((a, d))
                    changed = True
        closure = new
    return frozenset(closure)


def transitive_closure(priority: Priority) -> Priority:
    return set(_closure_cached(tuple(sorted(priority))))


def validate_rulebase(rb: RuleBase) -> List[str]:
    """
    Validate the manuscript's structural requirement that priority is a strict
    partial order over Rules.  Stored edges may be a transitive reduction; their
    closure is used as the semantic relation.
    """
    errors: List[str] = []
    names = set(rb.by_name())

    if len(names) != len(rb.rules):
        errors.append("Duplicate rule names")

    dangling = [(a, b) for a, b in rb.priority if a not in names or b not in names]
    if dangling:
        errors.append(f"Dangling priority relations: {sorted(dangling)}")

    closure = transitive_closure(rb.priority)
    cycles = sorted([a for a in names if (a, a) in closure])
    if cycles:
        errors.append(f"Priority relation is not irreflexive/acyclic: {cycles}")

    return errors


def maximal_enabled(rb: RuleBase, state: State, event: str) -> List[Rule]:
    enabled = enabled_rules(rb, state, event)
    closure = transitive_closure(rb.priority)
    result = []
    for r in enabled:
        if not any(
            (r.name, q.name) in closure
            for q in enabled
            if q.name != r.name
        ):
            result.append(r)
    return sorted(result, key=lambda r: r.name)


def apply_action(state: State, action: str) -> State:
    s = dict(state)
    if action == "emergencyStop":
        s["highSpeed"] = False
        s["idle"] = True
    elif action == "moveForward":
        s["idle"] = False
    elif action in ("turnLeft", "reroute", "evade"):
        s["pathBlocked"] = False
    elif action == "returnToCharge":
        s["batteryLow"] = False
    elif action == "shutdown":
        s["idle"] = True
        s["highSpeed"] = False
    elif action == "dock":
        s["batteryLow"] = False
        s["batteryCritical"] = False
    elif action == "hazardFlag":
        s["hazardFlag"] = True
    elif action == "safeMode":
        s["idle"] = True
    # stop, reduceSpeed, restartSensor, relocalize are observable actions
    # whose state abstraction is unchanged in this case study.
    return s


def transition_for_rule(state: State, event: str, rule: Optional[Rule]) -> Transition:
    before = tuple(sorted(state.items()))
    if rule is None:
        return Transition(event, None, "tau", before, before)
    after_state = apply_action(state, rule.action)
    return Transition(
        event,
        rule.name,
        rule.action,
        before,
        tuple(sorted(after_state.items())),
    )


def outgoing_transitions(
    rb: RuleBase,
    state: State,
    event: str,
) -> Tuple[Transition, ...]:
    """Return every transition admitted by the nondeterministic semantics.

    Each maximal enabled rule induces one outgoing transition. If no rule is
    enabled, the singleton result contains the distinguished idle transition.
    No global or local ``select`` function is part of the semantic model.
    """
    maximal = maximal_enabled(rb, state, event)
    if not maximal:
        return (transition_for_rule(state, event, None),)
    return tuple(transition_for_rule(state, event, rule) for rule in maximal)


def transitions_correspond(
    t1: Transition,
    t2: Transition,
    corr: Set[Tuple[str, str]],
) -> bool:
    if (
        t1.event != t2.event
        or t1.action != t2.action
        or t1.before != t2.before
        or t1.after != t2.after
    ):
        return False
    if t1.rule is None or t2.rule is None:
        return t1.rule is None and t2.rule is None
    return (t1.rule, t2.rule) in corr


def _transition_set_matches(
    rb1: RuleBase,
    rb2: RuleBase,
    s1: State,
    s2: State,
    event: str,
    correspondence: Set[Tuple[str, str]],
):
    """
    Check both directions of transition correspondence in one context.

    Returns the two complete outgoing transition sets, all matching pairs, and
    the unmatched transitions in each direction.
    """
    out1 = outgoing_transitions(rb1, s1, event)
    out2 = outgoing_transitions(rb2, s2, event)
    matches = [
        (t1, t2)
        for t1 in out1
        for t2 in out2
        if transitions_correspond(t1, t2, correspondence)
    ]
    unmatched1 = [
        t1 for t1 in out1
        if not any(transitions_correspond(t1, t2, correspondence) for t2 in out2)
    ]
    unmatched2 = [
        t2 for t2 in out2
        if not any(transitions_correspond(t1, t2, correspondence) for t1 in out1)
    ]
    return out1, out2, matches, unmatched1, unmatched2


def run_corresponding_trace_pair(
    rb1: RuleBase,
    rb2: RuleBase,
    initial_state: State,
    events: Sequence[str],
    correspondence: Set[Tuple[str, str]],
    rng: random.Random,
):
    """
    Sampled behavioural validation consistent with correspondence-based
    trace equivalence.

    At every step, every outgoing transition in either system must have a
    corresponding transition in the other system. One matching pair is sampled
    only after the complete bidirectional check succeeds, and is then used to
    continue the common finite prefix.
    """
    s1 = dict(initial_state)
    s2 = dict(initial_state)
    t1, t2 = [], []

    for pos, event in enumerate(events, start=1):
        out1, out2, matches, unmatched1, unmatched2 = _transition_set_matches(
            rb1, rb2, s1, s2, event, correspondence
        )
        if unmatched1 or unmatched2:
            tr1 = unmatched1[0] if unmatched1 else out1[0]
            tr2 = unmatched2[0] if unmatched2 else out2[0]
            t1.append(tr1)
            t2.append(tr2)
            direction = (
                "original_to_transformed" if unmatched1
                else "transformed_to_original"
            )
            return t1, t2, pos, direction

        tr1, tr2 = rng.choice(matches)
        s1, s2 = dict(tr1.after), dict(tr2.after)
        t1.append(tr1)
        t2.append(tr2)

    return t1, t2, None, None


# ============================================================
# PART 2. CASE STUDY AND REFACTORINGS
# ============================================================

ORIGINAL_RULES = [
    R("r3", "sensor", "obstacleDetected and highSpeed", "emergencyStop"),
    R("r8", "sensor", "collisionRisk", "evade"),
    R("r12", "sensor", "cliffDetected", "stop"),
    R("r5", "sensor", "batteryCritical", "shutdown"),
    R("r2", "sensor", "batteryLow", "returnToCharge"),
    R("r14", "sensor", "chargingStationNear", "dock"),
    R("r1", "sensor", "pathBlocked", "reroute"),
    R("r9", "sensor", "obstacleDetected", "turnLeft"),
    R("r6", "sensor", "narrowCorridor", "reduceSpeed"),
    R("r11", "sensor", "goalVisible", "moveForward"),
    R("r4", "timer", "idle and goalVisible", "moveForward"),
    R("r7", "watchdog", "communicationLost", "safeMode"),
    R("r10", "watchdog", "sensorFailure", "restartSensor"),
    R("r13", "watchdog", "localizationLost", "relocalize"),
]

ORIGINAL_PRIORITY: Priority = {
    ("r2", "r3"),
    ("r9", "r3"),
    ("r1", "r8"),
    ("r2", "r5"),
    ("r6", "r11"),
    ("r10", "r7"),
}

ORIGINAL = RuleBase(list(ORIGINAL_RULES), set(ORIGINAL_PRIORITY))

# Valid priority adjustment: 14 rules, 7 explicit priority relations.
PRIORITY_ADJUSTED = RuleBase(
    list(ORIGINAL_RULES),
    set(ORIGINAL_PRIORITY) | {("r6", "r4")},
)

# Valid cardinality-changing merge: 14 -> 13 rules.
# This is one logical Rule object with a guard over S x E.
R15 = Rule(
    "r15",
    "((event == 'sensor') and goalVisible) or "
    "((event == 'timer') and idle and goalVisible)",
    "moveForward",
)

MERGED = RuleBase(
    [r for r in PRIORITY_ADJUSTED.rules if r.name not in {"r11", "r4"}] + [R15],
    {
        ("r2", "r3"),
        ("r9", "r3"),
        ("r1", "r8"),
        ("r2", "r5"),
        ("r6", "r15"),
        ("r10", "r7"),
    },
)

# Valid decomposition is the next stage of the main sequence: 13 -> 14 rules.
DECOMPOSED = RuleBase(
    [r for r in MERGED.rules if r.name != "r3"]
    + [
        R(
            "r3a",
            "sensor",
            "obstacleDetected and highSpeed and frontObstacle",
            "emergencyStop",
        ),
        R(
            "r3b",
            "sensor",
            "obstacleDetected and highSpeed and not frontObstacle",
            "emergencyStop",
        ),
    ],
    {
        ("r2", "r3a"),
        ("r2", "r3b"),
        ("r9", "r3a"),
        ("r9", "r3b"),
        ("r1", "r8"),
        ("r2", "r5"),
        ("r6", "r15"),
        ("r10", "r7"),
    },
)

# Elimination is evaluated independently, as stated in the manuscript.
ELIM_ORIGINAL = RuleBase(
    list(ORIGINAL_RULES) + [R("r16", "sensor", "goalVisible", "moveForward")],
    set(ORIGINAL_PRIORITY) | {("r16", "r11")},
)
ELIMINATED = RuleBase(list(ORIGINAL_RULES), set(ORIGINAL_PRIORITY))

# Unsafe decomposition negative control.
UNSAFE_DECOMPOSITION = RuleBase(
    [r for r in ORIGINAL_RULES if r.name != "r3"]
    + [
        R("r3u1", "sensor", "obstacleDetected", "hazardFlag"),
        R("r3u2", "sensor", "hazardFlag and highSpeed", "emergencyStop"),
    ],
    {
        ("r2", "r3u1"),
        ("r2", "r3u2"),
        ("r9", "r3u1"),
        ("r9", "r3u2"),
        ("r1", "r8"),
        ("r2", "r5"),
        ("r6", "r11"),
        ("r10", "r7"),
    },
)

# Invalid priority adjustment: remove r9 < r3, exactly as described in the paper.
INVALID_PRIORITY = RuleBase(
    list(ORIGINAL_RULES),
    set(ORIGINAL_PRIORITY) - {("r9", "r3")},
)

# Invalid merge: create one merged rule r15u but deliberately omit the inherited
# r6 < r15u relation.  Priority edges incident to removed rules are first removed,
# so the target is a well-formed RRAI system with no dangling relation.
R15U = Rule(
    "r15u",
    "((event == 'sensor') and goalVisible) or "
    "((event == 'timer') and idle and goalVisible)",
    "moveForward",
)

INVALID_MERGE = RuleBase(
    [r for r in ORIGINAL.rules if r.name not in {"r11", "r4"}] + [R15U],
    {
        ("r2", "r3"),
        ("r9", "r3"),
        ("r1", "r8"),
        ("r2", "r5"),
        # deliberately omit ("r6", "r15u")
        ("r10", "r7"),
    },
)


# ============================================================
# PART 3. FINITE VERIFICATION DOMAINS
# ============================================================

EVENTS = ["sensor", "timer", "watchdog"]

# Admissible event language L = E*. Experiments sample its fixed-length words.
EVENT_LANGUAGE_DESCRIPTION = "E*"

PREDICATES = [
    "obstacleDetected",
    "highSpeed",
    "frontObstacle",
    "collisionRisk",
    "cliffDetected",
    "batteryCritical",
    "batteryLow",
    "chargingStationNear",
    "pathBlocked",
    "narrowCorridor",
    "goalVisible",
    "idle",
    "communicationLost",
    "sensorFailure",
    "localizationLost",
    "hazardFlag",
]


class FiniteDomain:
    """Re-iterable complete finite domain D=S x E with shared state objects."""
    def __init__(self, states: List[State], events: Sequence[str]):
        self.states = states
        self.events = tuple(events)

    def __len__(self) -> int:
        return len(self.states) * len(self.events)

    def __iter__(self):
        for state in self.states:
            for event in self.events:
                yield state, event


Domain = FiniteDomain


def all_states(predicates: Sequence[str]) -> List[State]:
    return [
        dict(zip(predicates, bits))
        for bits in product([False, True], repeat=len(predicates))
    ]


def complete_domain() -> FiniteDomain:
    """
    Complete represented finite domain D = S x E. The case-study state is the
    16 Boolean predicates in PREDICATES and E={sensor,timer,watchdog}; hence
    |D| = 2^16 * 3 = 196,608.  Only the 65,536 state dictionaries are stored;
    state-event pairs are produced lazily to avoid unnecessary memory pressure.
    """
    return FiniteDomain(all_states(PREDICATES), EVENTS)


FULL_DOMAIN: FiniteDomain = complete_domain()


def is_initial_state(state: Mapping[str, bool]) -> bool:
    """Membership predicate for the designated initial-state set I.

    The auxiliary ``hazardFlag`` is initially false and can be raised only by
    the intentionally unsafe transformed rule. All other Boolean predicates
    are unconstrained initially.
    """
    return not bool(state.get("hazardFlag", False))


def is_admissible_event_word(events: Sequence[str]) -> bool:
    """Recognise the finite event language L = E*."""
    return all(event in EVENTS for event in events)

DOMAINS: Dict[str, FiniteDomain] = {
    "Decomposition": FULL_DOMAIN,
    "Merging": FULL_DOMAIN,
    "Elimination": FULL_DOMAIN,
    "Priority adjustment": FULL_DOMAIN,
    "Invalid merge": FULL_DOMAIN,
    "Invalid priority adjustment": FULL_DOMAIN,
    "Unsafe decomposition": FULL_DOMAIN,
}



# ============================================================
# PART 4. ALGORITHM 1: END-TO-END VERIFICATION
# ============================================================

DECOMPOSITION = "Decomposition"
MERGE = "Merge"
ELIMINATION = "Elimination"
PRIORITY_ADJUSTMENT = "PriorityAdjustment"
UNSUPPORTED = "Unsupported"


def detect_refactoring(before: RuleBase, after: RuleBase) -> str:
    """DetectRefactoring(R,R') from Algorithm 1."""
    b = before.by_name()
    a = after.by_name()
    removed = set(b) - set(a)
    added = set(a) - set(b)
    common = set(b) & set(a)

    common_rules_unchanged = all(b[n] == a[n] for n in common)

    if not removed and not added and common_rules_unchanged:
        if transitive_closure(before.priority) != transitive_closure(after.priority):
            return PRIORITY_ADJUSTMENT
        return UNSUPPORTED  # identity/no refactoring

    if len(removed) == 1 and len(added) >= 2 and common_rules_unchanged:
        return DECOMPOSITION

    if len(removed) >= 2 and len(added) == 1 and common_rules_unchanged:
        return MERGE

    if len(removed) == 1 and len(added) == 0 and common_rules_unchanged:
        return ELIMINATION

    return UNSUPPORTED


def identify_changed_rules(before: RuleBase, after: RuleBase) -> dict:
    """IdentifyChangedRules(R,R') from Algorithm 1."""
    b = set(before.by_name())
    a = set(after.by_name())
    return {
        "removed": sorted(b - a),
        "added": sorted(a - b),
        "retained": sorted(b & a),
    }


def build_correspondence(
    transformation: str,
    before: RuleBase,
    after: RuleBase,
    changed: dict,
) -> Set[Tuple[str, str]]:
    """BuildCorrespondence(T,R,R') from Algorithm 1."""
    common = set(before.by_name()) & set(after.by_name())
    corr = {(x, x) for x in common}

    removed = changed["removed"]
    added = changed["added"]

    if transformation == DECOMPOSITION:
        original = removed[0]
        corr |= {(original, x) for x in added}
    elif transformation == MERGE:
        merged = added[0]
        corr |= {(x, merged) for x in removed}
    # Elimination: removed rule has no image.
    # Priority adjustment: identity relation already complete.
    return corr


def _priority_relation(rb: RuleBase) -> Priority:
    return transitive_closure(rb.priority)


def check_frame_preservation(
    before: RuleBase,
    after: RuleBase,
    changed: dict,
) -> List[FailureRecord]:
    """
    Ensure that retained rules and priority relations among retained rules are
    unchanged.  This prevents hidden changes outside the detected refactoring.
    """
    failures: List[FailureRecord] = []
    b = before.by_name()
    a = after.by_name()
    retained = set(changed["retained"])

    changed_retained = [n for n in retained if b[n] != a[n]]
    if changed_retained:
        failures.append(
            FailureRecord(
                "FramePreservation",
                {"changed_retained_rules": sorted(changed_retained)},
            )
        )

    pb = _priority_relation(before)
    pa = _priority_relation(after)
    for x in sorted(retained):
        for y in sorted(retained):
            if x == y:
                continue
            if ((x, y) in pb) != ((x, y) in pa):
                failures.append(
                    FailureRecord(
                        "FramePreservation",
                        {
                            "priority_pair": [x, y],
                            "before": (x, y) in pb,
                            "after": (x, y) in pa,
                        },
                    )
                )
                return failures

    return failures


def check_guard_partition(
    original: Rule,
    parts: List[Rule],
    domain: Domain,
) -> List[FailureRecord]:
    failures: List[FailureRecord] = []
    seen = {p.name: False for p in parts}

    for s, e in domain:
        orig = eval_guard(original.guard, s, e)
        enabled = [p for p in parts if eval_guard(p.guard, s, e)]
        for p in enabled:
            seen[p.name] = True

        if orig != bool(enabled):
            failures.append(
                FailureRecord(
                    "GuardPartition",
                    {
                        "reason": "union_not_equivalent",
                        "state": s,
                        "event": e,
                        "original_enabled": orig,
                        "enabled_parts": [p.name for p in enabled],
                    },
                )
            )
            break

        if len(enabled) > 1:
            failures.append(
                FailureRecord(
                    "GuardPartition",
                    {
                        "reason": "parts_not_disjoint",
                        "state": s,
                        "event": e,
                        "enabled_parts": [p.name for p in enabled],
                    },
                )
            )
            break

    missing = sorted([name for name, was_seen in seen.items() if not was_seen])
    if missing:
        failures.append(
            FailureRecord(
                "GuardPartition",
                {"reason": "empty_partition_component", "rules": missing},
            )
        )

    return failures


def check_action_preservation(
    original: Rule,
    parts: List[Rule],
) -> List[FailureRecord]:
    bad = [p.name for p in parts if p.action != original.action]
    if not bad:
        return []
    return [
        FailureRecord(
            "ActionPreservation",
            {
                "original_rule": original.name,
                "original_action": original.action,
                "mismatching_rules": {
                    p.name: p.action for p in parts if p.name in bad
                },
            },
        )
    ]


def check_priority_inheritance(
    before: RuleBase,
    after: RuleBase,
    original_name: str,
    part_names: List[str],
) -> List[FailureRecord]:
    pb = _priority_relation(before)
    pa = _priority_relation(after)
    external = set(before.by_name()) - {original_name}

    for q in sorted(external):
        for p in sorted(part_names):
            expected_low = (original_name, q) in pb
            actual_low = (p, q) in pa
            expected_high = (q, original_name) in pb
            actual_high = (q, p) in pa

            if expected_low != actual_low or expected_high != actual_high:
                return [
                    FailureRecord(
                        "PriorityInheritance",
                        {
                            "original": original_name,
                            "part": p,
                            "external_rule": q,
                            "expected_part_below_external": expected_low,
                            "actual_part_below_external": actual_low,
                            "expected_external_below_part": expected_high,
                            "actual_external_below_part": actual_high,
                        },
                    )
                ]

    for p in part_names:
        for q in part_names:
            if p != q and (p, q) in pa:
                return [
                    FailureRecord(
                        "PriorityInheritance",
                        {
                            "reason": "priority_between_decomposed_parts",
                            "pair": [p, q],
                        },
                    )
                ]

    return []


def check_merge_guards(
    originals: List[Rule],
    merged: Rule,
    domain: Domain,
) -> List[FailureRecord]:
    for s, e in domain:
        enabled_originals = [r for r in originals if eval_guard(r.guard, s, e)]
        merged_enabled = eval_guard(merged.guard, s, e)

        if bool(enabled_originals) != merged_enabled:
            return [
                FailureRecord(
                    "MergeGuards",
                    {
                        "reason": "union_not_equivalent",
                        "state": s,
                        "event": e,
                        "enabled_originals": [r.name for r in enabled_originals],
                        "merged_enabled": merged_enabled,
                    },
                )
            ]

        if len(enabled_originals) > 1:
            return [
                FailureRecord(
                    "MergeGuards",
                    {
                        "reason": "original_guards_not_disjoint",
                        "state": s,
                        "event": e,
                        "enabled_originals": [r.name for r in enabled_originals],
                    },
                )
            ]

    return []


def check_common_action(
    originals: List[Rule],
    merged: Rule,
) -> List[FailureRecord]:
    actions = {r.action for r in originals} | {merged.action}
    if len(actions) == 1:
        return []
    return [
        FailureRecord(
            "CommonAction",
            {
                "original_actions": {r.name: r.action for r in originals},
                "merged_rule": merged.name,
                "merged_action": merged.action,
            },
        )
    ]


def check_priority_compatibility(
    before: RuleBase,
    after: RuleBase,
    original_names: List[str],
    merged_name: str,
) -> List[FailureRecord]:
    """
    Implements the merge condition in Section II-D:
    all merged rules must have the same external priority relation, and the
    single merged rule must inherit that common relation.
    """
    pb = _priority_relation(before)
    pa = _priority_relation(after)
    external = set(before.by_name()) - set(original_names)

    for q in sorted(external):
        below = [(r, (r, q) in pb) for r in original_names]
        above = [(r, (q, r) in pb) for r in original_names]

        low_values = {v for _, v in below}
        high_values = {v for _, v in above}

        if len(low_values) > 1 or len(high_values) > 1:
            return [
                FailureRecord(
                    "PriorityCompatibility",
                    {
                        "reason": "original_rules_have_incompatible_external_priorities",
                        "external_rule": q,
                        "original_below_external": dict(below),
                        "external_below_original": dict(above),
                    },
                )
            ]

        expected_low = next(iter(low_values))
        expected_high = next(iter(high_values))
        actual_low = (merged_name, q) in pa
        actual_high = (q, merged_name) in pa

        if expected_low != actual_low or expected_high != actual_high:
            return [
                FailureRecord(
                    "PriorityCompatibility",
                    {
                        "reason": "merged_rule_does_not_inherit_common_priority",
                        "external_rule": q,
                        "merged_rule": merged_name,
                        "expected_merged_below_external": expected_low,
                        "actual_merged_below_external": actual_low,
                        "expected_external_below_merged": expected_high,
                        "actual_external_below_merged": actual_high,
                    },
                )
            ]

    return []


def check_elimination(
    before: RuleBase,
    name: str,
    domain: Domain,
) -> List[FailureRecord]:
    for s, e in domain:
        maximal = {r.name for r in maximal_enabled(before, s, e)}
        if name in maximal:
            return [
                FailureRecord(
                    "EliminationCondition",
                    {
                        "rule": name,
                        "state": s,
                        "event": e,
                        "maximal_enabled": sorted(maximal),
                    },
                )
            ]
    return []


def check_maximal_rule_preservation(
    before: RuleBase,
    after: RuleBase,
    domain: Domain,
) -> List[FailureRecord]:
    for s, e in domain:
        mb = {r.name for r in maximal_enabled(before, s, e)}
        ma = {r.name for r in maximal_enabled(after, s, e)}
        if mb != ma:
            return [
                FailureRecord(
                    "MaximalRulePreservation",
                    {
                        "state": s,
                        "event": e,
                        "before": sorted(mb),
                        "after": sorted(ma),
                    },
                )
            ]
    return []


def generate_counterexample(
    before: RuleBase,
    after: RuleBase,
    domain: Domain,
    correspondence: Set[Tuple[str, str]],
) -> Optional[dict]:
    """
    Exhaustive directional one-step divergence search over the finite domain.

    The witness is one transition in either system for which no corresponding
    transition exists in the other system. Counterexample generation is
    diagnostic and is not used to prove equivalence.
    """
    for s, e in domain:
        out1, out2, _matches, unmatched1, unmatched2 = _transition_set_matches(
            before, after, s, s, e, correspondence
        )
        if unmatched1:
            tr = unmatched1[0]
            return {
                "direction": "original_to_transformed",
                "state": s,
                "event": e,
                "unmatched_transition": asdict(tr),
                "original_outgoing": [asdict(t) for t in out1],
                "transformed_outgoing": [asdict(t) for t in out2],
            }
        if unmatched2:
            tr = unmatched2[0]
            return {
                "direction": "transformed_to_original",
                "state": s,
                "event": e,
                "unmatched_transition": asdict(tr),
                "original_outgoing": [asdict(t) for t in out1],
                "transformed_outgoing": [asdict(t) for t in out2],
            }

    return None


def verify_refactoring(
    before: RuleBase,
    after: RuleBase,
    domain: Domain,
) -> VerificationResult:
    """
    Algorithm 1: Verification of Correctness-Preserving Rule Refactorings.

    Detects the transformation, identifies changed rules, checks the applicable
    obligations, constructs C_Ref, and returns witnesses plus a behavioural
    counterexample when one is found.
    """
    structural_errors = {
        "before": validate_rulebase(before),
        "after": validate_rulebase(after),
    }
    if structural_errors["before"] or structural_errors["after"]:
        return VerificationResult(
            status="Fail",
            transformation="IllFormed",
            failed=[
                FailureRecord("WellFormedness", structural_errors)
            ],
            counterexample=None,
            changed_rules=identify_changed_rules(before, after),
            correspondence=set(),
            domain_size=len(domain),
        )

    t = detect_refactoring(before, after)
    changed = identify_changed_rules(before, after)

    if t == UNSUPPORTED:
        return VerificationResult(
            status="Unsupported",
            transformation=t,
            failed=[
                FailureRecord(
                    "UnsupportedRefactoring",
                    {"changed_rules": changed},
                )
            ],
            counterexample=None,
            changed_rules=changed,
            correspondence=set(),
            domain_size=len(domain),
        )

    failures: List[FailureRecord] = []
    # For decomposition/merge/elimination, retained rules and retained-to-retained
    # priority relations are frame conditions. For PriorityAdjustment, changing
    # the priority relation is the transformation itself, so only the rule set
    # and rule definitions must remain unchanged (already enforced by detection).
    if t != PRIORITY_ADJUSTMENT:
        failures.extend(check_frame_preservation(before, after, changed))

    b = before.by_name()
    a = after.by_name()

    if t == DECOMPOSITION:
        original_name = changed["removed"][0]
        part_names = changed["added"]
        original = b[original_name]
        parts = [a[n] for n in part_names]

        failures.extend(check_guard_partition(original, parts, domain))
        failures.extend(check_action_preservation(original, parts))
        failures.extend(
            check_priority_inheritance(
                before, after, original_name, part_names
            )
        )

    elif t == MERGE:
        original_names = changed["removed"]
        merged_name = changed["added"][0]
        originals = [b[n] for n in original_names]
        merged = a[merged_name]

        failures.extend(check_merge_guards(originals, merged, domain))
        failures.extend(check_common_action(originals, merged))
        failures.extend(
            check_priority_compatibility(
                before, after, original_names, merged_name
            )
        )

    elif t == ELIMINATION:
        eliminated_name = changed["removed"][0]
        failures.extend(check_elimination(before, eliminated_name, domain))

    elif t == PRIORITY_ADJUSTMENT:
        failures.extend(
            check_maximal_rule_preservation(before, after, domain)
        )

    corr = build_correspondence(t, before, after, changed)

    if not failures:
        return VerificationResult(
            status="Pass",
            transformation=t,
            failed=[],
            counterexample=None,
            changed_rules=changed,
            correspondence=corr,
            domain_size=len(domain),
        )

    cex = generate_counterexample(before, after, domain, corr)

    return VerificationResult(
        status="Fail",
        transformation=t,
        failed=failures,
        counterexample=cex,
        changed_rules=changed,
        correspondence=corr,
        domain_size=len(domain),
    )


# ============================================================
# PART 5. EXPERIMENT DEFINITIONS
# ============================================================

EXPERIMENTS = {
    "Priority adjustment": (ORIGINAL, PRIORITY_ADJUSTED),
    "Merging": (PRIORITY_ADJUSTED, MERGED),
    "Decomposition": (MERGED, DECOMPOSED),
    "Elimination": (ELIM_ORIGINAL, ELIMINATED),
    "Invalid merge": (ORIGINAL, INVALID_MERGE),
    "Invalid priority adjustment": (ORIGINAL, INVALID_PRIORITY),
    "Unsafe decomposition": (ORIGINAL, UNSAFE_DECOMPOSITION),
}


def correspondence_for(before: RuleBase, after: RuleBase) -> Set[Tuple[str, str]]:
    t = detect_refactoring(before, after)
    changed = identify_changed_rules(before, after)
    return build_correspondence(t, before, after, changed)


CASES = [
    (name, before, after, correspondence_for(before, after))
    for name, (before, after) in EXPERIMENTS.items()
]


def proof_obligations() -> Dict[str, VerificationResult]:
    return {
        name: verify_refactoring(before, after, DOMAINS[name])
        for name, (before, after) in EXPERIMENTS.items()
    }


# ============================================================
# PART 6. EXECUTION-BASED BEHAVIOURAL VALIDATION
# ============================================================

def random_state(rng: random.Random) -> State:
    s = {p: bool(rng.getrandbits(1)) for p in PREDICATES}
    s["hazardFlag"] = False
    return s


def random_events(rng: random.Random, k: int) -> List[str]:
    return [rng.choice(EVENTS) for _ in range(k)]


def behavioural_validation(
    num_traces: int = 10000,
    trace_length: int = 20,
    seed: int = 20260723,
):
    """
    Monte-Carlo behavioural validation.  The same sampled inputs are reused
    across all transformations, exactly as described in the evaluation.
    """
    rng = random.Random(seed)
    inputs = [
        (random_state(rng), random_events(rng, trace_length))
        for _ in range(num_traces)
    ]

    rows = []
    counterexamples = {}
    divergence_positions = {}

    for name, before, after, corr in CASES:
        div = 0
        positions = []
        ce = None
        choice_rng = random.Random(f"{seed}:{name}:nondeterministic-choices")
        t0 = time.perf_counter()

        for idx, (initial, events) in enumerate(inputs):
            if not is_initial_state(initial):
                raise AssertionError("Sampled state is outside initial-state set I")
            if not is_admissible_event_word(events):
                raise AssertionError("Sampled word is outside event language L")
            a, b, p, direction = run_corresponding_trace_pair(
                before, after, initial, events, corr, choice_rng
            )
            if p is not None:
                div += 1
                positions.append(p)
                if ce is None:
                    ce = {
                        "sample": idx,
                        "initial_state": initial,
                        "events": events,
                        "divergence_position": p,
                        "direction": direction,
                        "original_transition": asdict(a[p - 1]),
                        "transformed_transition": asdict(b[p - 1]),
                    }

        rows.append(
            {
                "transformation": name,
                "executions": num_traces,
                "divergences": div,
                "rate_percent": round(100 * div / num_traces, 4),
                "elapsed_s": round(time.perf_counter() - t0, 6),
            }
        )
        counterexamples[name] = ce
        divergence_positions[name] = positions

    return rows, counterexamples, divergence_positions


# ============================================================
# PART 7. SCALABILITY: FULL BEHAVIOURAL COMPARISON
# ============================================================

def scalability(
    sizes=(100, 500, 1000, 2000, 5000, 10000),
    trace_length: int = 20,
    repetitions: int = 30,
    base_seed: int = 20260723,
):
    """
    Measure the complete correspondence-based behavioural-validation procedure.

    The timed region invokes run_corresponding_trace_pair for the valid
    decomposition MERGED -> DECOMPOSED.  Thus each run includes rule enabling,
    maximal-rule computation, bidirectional outgoing-set correspondence checking,
    action/state comparison, and matched nondeterministic continuation.

    Input generation is intentionally outside the timed region. Only the number
    of sampled traces varies; rule-base structure and trace length remain fixed.

    Returns (aggregate_rows, raw_rows).  The raw per-repetition timings are saved
    so that every value used to compute manuscript Table 6 is auditable.
    """
    corr = correspondence_for(MERGED, DECOMPOSED)
    aggregate_rows = []
    raw_rows = []

    for n in sizes:
        times = []

        for rep in range(repetitions):
            seed = base_seed + rep
            rng = random.Random(seed)
            choice_rng = random.Random(
                f"{seed}:scalability:nondeterministic-choices"
            )
            inputs = [
                (random_state(rng), random_events(rng, trace_length))
                for _ in range(n)
            ]

            t0 = time.perf_counter()
            divergences = 0
            for state, events in inputs:
                _, _, p, _direction = run_corresponding_trace_pair(
                    MERGED, DECOMPOSED, state, events, corr, choice_rng
                )
                if p is not None:
                    divergences += 1
            elapsed = time.perf_counter() - t0

            if divergences != 0:
                raise AssertionError(
                    f"Valid decomposition diverged in scalability run: {divergences}"
                )

            times.append(elapsed)
            raw_rows.append({
                "traces": n,
                "trace_length": trace_length,
                "repetition": rep + 1,
                "seed": seed,
                "elapsed_s": round(elapsed, 9),
            })

        aggregate_rows.append({
            "traces": n,
            "trace_length": trace_length,
            "repetitions": repetitions,
            "mean_time_s": round(statistics.mean(times), 6),
            "sd_time_s": round(
                statistics.stdev(times) if len(times) > 1 else 0.0, 6
            ),
            "min_time_s": round(min(times), 6),
            "max_time_s": round(max(times), 6),
            "measured_operation": "bidirectional_outgoing_set_validation",
        })

    return aggregate_rows, raw_rows



# ============================================================
# PART 8. REPRODUCIBLE OUTPUT
# ============================================================

OUT = Path("results")
OUT.mkdir(exist_ok=True)


def write_csv(path: Path, rows: List[dict]):
    if not rows:
        return
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)


def plot_divergence_positions(
    divergence_positions: Dict[str, List[int]],
    trace_length: int = 20,
):
    import matplotlib.pyplot as plt
    from collections import Counter

    invalid_cases = [
        "Invalid merge",
        "Invalid priority adjustment",
        "Unsafe decomposition",
    ]
    positions = list(range(1, trace_length + 1))

    plt.figure(figsize=(8, 5))
    for name in invalid_cases:
        counts = Counter(divergence_positions.get(name, []))
        frequencies = [counts.get(pos, 0) for pos in positions]
        plt.plot(
            positions,
            frequencies,
            marker="o",
            linewidth=1.8,
            label=name,
        )

    plt.xlabel("First-divergence position")
    plt.ylabel("Number of divergent executions")
    plt.xticks(positions)
    plt.legend()
    plt.grid(True, linestyle="--", alpha=0.3)
    plt.tight_layout()
    output_path = OUT / "figure3_divergence_positions.png"
    output_pdf = OUT / "figure3_divergence_positions.pdf"
    plt.savefig(output_path, dpi=300, bbox_inches="tight")
    plt.savefig(output_pdf, bbox_inches="tight")
    plt.close()
    return output_path


def structural_summary() -> List[dict]:
    """Table-2-ready structural summary of the true sequential refactoring."""
    return [
        {
            "stage": "Original",
            "rules": len(ORIGINAL.rules),
            "priority_relations": len(ORIGINAL.priority),
            "structural_change": "-",
            "formal_basis": "-",
        },
        {
            "stage": "Priority adjustment",
            "rules": len(PRIORITY_ADJUSTED.rules),
            "priority_relations": len(PRIORITY_ADJUSTED.priority),
            "structural_change": "Add r6 < r4",
            "formal_basis": "Lemma 4",
        },
        {
            "stage": "Merging",
            "rules": len(MERGED.rules),
            "priority_relations": len(MERGED.priority),
            "structural_change": "r11,r4 -> r15",
            "formal_basis": "Lemma 2",
        },
        {
            "stage": "Decomposition",
            "rules": len(DECOMPOSED.rules),
            "priority_relations": len(DECOMPOSED.priority),
            "structural_change": "r3 -> {r3a,r3b}",
            "formal_basis": "Lemma 1",
        },
    ]


def compose_correspondence(
    left: Set[Tuple[str, str]],
    right: Set[Tuple[str, str]],
) -> Set[Tuple[str, str]]:
    """Relational composition used by Theorem 2."""
    return {(x, z) for x, y1 in left for y2, z in right if y1 == y2}


def main_sequence_summary() -> dict:
    """Machine-check the three preservation-valid stages in Table 2."""
    r1 = verify_refactoring(ORIGINAL, PRIORITY_ADJUSTED, FULL_DOMAIN)
    r2 = verify_refactoring(PRIORITY_ADJUSTED, MERGED, FULL_DOMAIN)
    r3 = verify_refactoring(MERGED, DECOMPOSED, FULL_DOMAIN)
    composed = compose_correspondence(
        compose_correspondence(r1.correspondence, r2.correspondence),
        r3.correspondence,
    )
    return {
        "all_stages_pass": all(r.status == "Pass" for r in (r1, r2, r3)),
        "stage_status": [r1.status, r2.status, r3.status],
        "composed_correspondence": sorted([list(x) for x in composed]),
    }


OBLIGATION_CODES = {
    "PriorityCompatibility": "PC",
    "MaximalRulePreservation": "MRP",
    "GuardPartition": "GP",
    "ActionPreservation": "AP",
    "PriorityInheritance": "PI",
    "MergeGuards": "MG",
    "CommonAction": "CA",
    "EliminationCondition": "EC",
    "FramePreservation": "FP",
    "WellFormedness": "WF",
}


def _failed_codes(result: VerificationResult) -> str:
    obligations = []
    for failure in result.failed:
        if failure.obligation not in obligations:
            obligations.append(failure.obligation)
    return ", ".join(OBLIGATION_CODES.get(x, x) for x in obligations)


def run_self_tests() -> None:
    """Fast semantic regression checks executed before every experiment run."""
    for rb in (
        ORIGINAL, PRIORITY_ADJUSTED, MERGED, DECOMPOSED,
        ELIM_ORIGINAL, ELIMINATED, UNSAFE_DECOMPOSITION,
        INVALID_PRIORITY, INVALID_MERGE,
    ):
        errors = validate_rulebase(rb)
        if errors:
            raise AssertionError(f"Ill-formed built-in rule base: {errors}")

    # Stored graph edges are interpreted through their transitive closure G+.
    chain = RuleBase(
        [Rule("x", "True", "a"), Rule("y", "True", "a"), Rule("z", "True", "a")],
        {("x", "y"), ("y", "z")},
    )
    if ("x", "z") not in transitive_closure(chain.priority):
        raise AssertionError("Priority semantics did not compute G+")

    # Incomparable maximal rules must induce separate outgoing transitions.
    nondet = RuleBase(
        [Rule("x", "True", "left"), Rule("y", "True", "right")],
        set(),
    )
    outs = outgoing_transitions(nondet, {}, "sensor")
    if {t.rule for t in outs} != {"x", "y"}:
        raise AssertionError("Nondeterministic outgoing-transition set is incomplete")

    # The idle rule is represented by exactly one tau transition.
    idle = RuleBase([Rule("x", "False", "a")], set())
    idle_out = outgoing_transitions(idle, {}, "sensor")
    if len(idle_out) != 1 or idle_out[0].rule is not None or idle_out[0].action != "tau":
        raise AssertionError("Idle-transition semantics is incorrect")

    if not is_initial_state({"hazardFlag": False}):
        raise AssertionError("Initial-state predicate rejected a valid state")
    if is_initial_state({"hazardFlag": True}):
        raise AssertionError("Initial-state predicate accepted an invalid state")
    if not is_admissible_event_word(EVENTS * 2):
        raise AssertionError("Event-language recogniser rejected a word in E*")


def main(
    num_traces: int = 10000,
    trace_length: int = 20,
    seed: int = 20260723,
    scalability_sizes=(100, 500, 1000, 2000, 5000, 10000),
    scalability_repetitions: int = 30,
):
    run_self_tests()
    checks = proof_obligations()

    proof_rows = []
    algorithm_results = {}
    for name, result in checks.items():
        obligations = []
        for f in result.failed:
            if f.obligation not in obligations:
                obligations.append(f.obligation)
        proof_rows.append({
            "transformation": name,
            "detected_type": result.transformation,
            "status": result.status,
            "domain_size": result.domain_size,
            "failed_obligations": "; ".join(obligations),
            "counterexample_found": result.counterexample is not None,
        })
        algorithm_results[name] = result.to_jsonable()

    write_csv(OUT / "proof_obligations.csv", proof_rows)
    (OUT / "algorithm_results.json").write_text(
        json.dumps(algorithm_results, indent=2), encoding="utf-8"
    )

    behavioural_rows, sampled_cex, divergence_positions = behavioural_validation(
        num_traces=num_traces, trace_length=trace_length, seed=seed
    )
    write_csv(OUT / "behavioural_validation.csv", behavioural_rows)

    combined_cex = {
        name: {
            "algorithm1_counterexample": checks[name].counterexample,
            "sampled_counterexample": sampled_cex[name],
        }
        for name in checks
    }
    (OUT / "counterexamples.json").write_text(
        json.dumps(combined_cex, indent=2), encoding="utf-8"
    )
    (OUT / "divergence_positions.json").write_text(
        json.dumps(divergence_positions, indent=2), encoding="utf-8"
    )
    figure_path = plot_divergence_positions(
        divergence_positions, trace_length=trace_length
    )

    scale_rows, raw_scale_rows = scalability(
        sizes=scalability_sizes,
        trace_length=trace_length,
        repetitions=scalability_repetitions,
        base_seed=seed,
    )
    write_csv(OUT / "scalability.csv", scale_rows)
    write_csv(OUT / "scalability_runs.csv", raw_scale_rows)

    table2 = structural_summary()
    write_csv(OUT / "table2_structural_changes.csv", table2)

    behavioural_by_name = {r["transformation"]: r for r in behavioural_rows}
    valid_names = ["Decomposition", "Merging", "Elimination", "Priority adjustment"]
    invalid_names = ["Invalid merge", "Invalid priority adjustment", "Unsafe decomposition"]

    table3 = [
        {
            "transformation": name,
            "proof_obligation_result": checks[name].status,
            "divergences": behavioural_by_name[name]["divergences"],
            "rate_percent": behavioural_by_name[name]["rate_percent"],
        }
        for name in valid_names
    ]
    write_csv(OUT / "table3_valid_transformations.csv", table3)

    table4 = [
        {
            "transformation": name,
            "failed_proof_obligations": _failed_codes(checks[name]),
            "divergences": behavioural_by_name[name]["divergences"],
            "rate_percent": behavioural_by_name[name]["rate_percent"],
        }
        for name in invalid_names
    ]
    write_csv(OUT / "table4_invalid_transformations.csv", table4)

    table5 = [
        {
            "transformation": name,
            "proof_obligations": checks[name].status,
            "violated_condition": "; ".join(
                dict.fromkeys(f.obligation for f in checks[name].failed)
            ),
            "counterexample": "Found" if checks[name].counterexample else "None",
        }
        for name in invalid_names
    ]
    write_csv(OUT / "table5_counterexamples.csv", table5)

    write_csv(OUT / "table6_scalability.csv", scale_rows)

    sequence = main_sequence_summary()
    (OUT / "main_sequence.json").write_text(
        json.dumps(sequence, indent=2), encoding="utf-8"
    )

    metadata = {
        "verification_domain": {
            "state_predicates": PREDICATES,
            "events": EVENTS,
            "states": 2 ** len(PREDICATES),
            "contexts": len(FULL_DOMAIN),
            "kind": "complete_S_cross_E",
        },
        "behavioural_validation": {
            "num_traces": num_traces,
            "trace_length": trace_length,
            "seed": seed,
        },
        "scalability": {
            "sizes": list(scalability_sizes),
            "repetitions": scalability_repetitions,
            "measured_operation": "bidirectional_outgoing_set_validation",
            "input_generation_timed": False,
        },
        "semantics": {
            "stored_priority": "acyclic graph G",
            "semantic_priority": "transitive closure G+",
            "initial_state_set": "I = {s in S | hazardFlag = false}",
            "event_language": EVENT_LANGUAGE_DESCRIPTION,
            "trace_kind": "finite",
            "choice_model": "step-wise nondeterministic maximal-rule choice",
            "comparison": "bidirectional outgoing-transition-set correspondence",
        },
        "figure3": str(figure_path),
    }
    (OUT / "experiment_metadata.json").write_text(
        json.dumps(metadata, indent=2), encoding="utf-8"
    )

    print("Structural summary / Table 2")
    for row in table2:
        print(row)
    print("\nProof obligations / Algorithm 1")
    for row in proof_rows:
        print(row)
    print("\nBehavioural validation")
    for row in behavioural_rows:
        print(row)
    print("\nScalability / Table 6")
    for row in scale_rows:
        print(row)


def show_results():
    """Colab/Jupyter preview of every manuscript-facing output, including Figure 3."""
    try:
        import pandas as pd
        from IPython.display import display, Image

        csv_files = [
            "table2_structural_changes.csv",
            "proof_obligations.csv",
            "table3_valid_transformations.csv",
            "table4_invalid_transformations.csv",
            "table5_counterexamples.csv",
            "table6_scalability.csv",
            "behavioural_validation.csv",
            "scalability_runs.csv",
        ]

        for filename in csv_files:
            path = OUT / filename
            if path.exists():
                print("\n" + "=" * 70)
                print(filename)
                print("=" * 70)
                display(pd.read_csv(path))

        fig = OUT / "figure3_divergence_positions.png"
        if fig.exists():
            print("\n" + "=" * 70)
            print("Figure 3: first-divergence-position distribution")
            print("=" * 70)
            display(Image(filename=str(fig)))

        print("\nGenerated artifact files:")
        for path in sorted(OUT.iterdir()):
            print(" -", path.name)

    except Exception as exc:
        print("Result preview skipped:", exc)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Reproduce the RRAI refactoring verification experiments."
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Run a small smoke test instead of the manuscript configuration.",
    )
    # Jupyter/Google Colab injects its own kernel arguments, e.g.
    #   -f /root/.local/share/jupyter/runtime/kernel-....json
    # parse_known_args() safely ignores those notebook-only arguments while
    # still honoring the artifact's own --quick option.
    args, _unknown = parser.parse_known_args()

    if args.quick:
        main(
            num_traces=200,
            trace_length=20,
            seed=20260723,
            scalability_sizes=(100, 500),
            scalability_repetitions=2,
        )
    else:
        main()
    show_results()
