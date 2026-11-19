"""Exact executable examples; scope and exclusions are in README.md."""
from fractions import Fraction as F
from itertools import product
import argparse
import json
import sys

def check(condition, message=""):
    """Keep checks active even when Python optimisation removes assert statements."""
    if not condition:
        raise AssertionError(message)

def decoder(readings, verdicts):
    if len(readings) != len(verdicts):
        raise ValueError("different carriers")
    out = {}
    for reading, verdict in zip(readings, verdicts):
        if reading in out and out[reading] != verdict:
            return None
        out[reading] = verdict
    return out


def lifts(root, target_path, edges, image):
    if not target_path or image[root] != target_path[0]:
        return False
    frontier = {root}
    for target in target_path[1:]:
        frontier = {v for u, v in edges if u in frontier and image[v] == target}
    return bool(frontier)


def common_witness(obligations):
    if not obligations:
        raise ValueError("explicit witness carrier required for zero obligations")
    return set.intersection(*map(set, obligations))


def recurrent(prefix, cycle):
    if not cycle:
        raise ValueError("nonempty periodic tail required")
    return any(cycle)


def finite_prefix(prefix, cycle, size):
    if not cycle or size < 0:
        raise ValueError("invalid ultimately periodic word")
    return tuple(prefix[k] if k < len(prefix) else cycle[(k-len(prefix)) % len(cycle)] for k in range(size))


def total_cost(values):
    return sum(values)


def residual_accepts(budget, charged_prefix, future):
    remaining = budget - total_cost(charged_prefix)
    return remaining >= 0 and total_cost(future) <= remaining


def restarts(capable, request):
    """Restart at the completion phase from capability and an external request.

    This is the two-input slice of the Proposition M10 law, without the blocking input;
    the complete three-signal law is executed in deep/suite.py by t_M05_full_restart_automaton
    and t_M09_capability_channels.
    """
    return capable or request


def upkeep(steps):
    # witness p_n=2^(-n); upkeep cost at event n is p_n, n starts at1.
    witness = F(1, 2**steps)
    spent = sum((F(1, 2**n) for n in range(1, steps+1)), F(0))
    return witness, spent


def event_charge(c, sigma):
    """Declared maintenance law: an event with witness sigma costs c|sigma|, with c > 0."""
    if c <= 0:
        raise ValueError("positive maintenance constant required")
    return c * abs(sigma)


def word_charge(c, sigmas):
    return sum((event_charge(c, sigma) for sigma in sigmas), F(0))


def paid_events(c, sigmas, budget):
    """Number of leading events paid from one budget: the longest prefix whose charge fits."""
    if budget < 0:
        raise ValueError("nonnegative budget required")
    count = 0
    while count < len(sigmas) and word_charge(c, sigmas[:count + 1]) <= budget:
        count += 1
    return count


def shares(theta, pad):
    return pad, theta ^ pad


def t_M01_fibre_decoder():
    for readings in product(range(2), repeat=3):
        for verdicts in product(range(2), repeat=3):
            expected = all(readings[i] != readings[j] or verdicts[i] == verdicts[j] for i in range(3) for j in range(3))
            result = decoder(readings, verdicts)
            check((result is not None) == expected, (readings, verdicts, result))
            if result is not None:
                check(tuple(result[x] for x in readings) == verdicts)
    check(decoder((), ()) == {})


def t_M02_rooted_lifting():
    a, b = "a", "b"
    image = {"r": a, "s": a, "t": b}
    edges = {("s", "t")}
    check(not lifts("r", (a, b), edges, image))
    check(lifts("s", (a, b), edges, image))
    check(lifts("r", (a,), edges, image))
    check(not lifts("s", (a, a), edges, image), "the edge exists, but its destination has the wrong image")
    check(not lifts("s", (b,), edges, image), "the root's image must be the first target state")


def t_M03_common_witness():
    separate = [{"a"}, {"b"}]
    check(all(separate) and common_witness(separate) == set())
    check(common_witness([{1, 2}, {2, 3}]) == {2})


def t_M04_finite_prefix_whole_tail():
    for n in (1, 2, 5, 17, 64):
        prefix = (1,) + (0,) * n
        # The first word reads n of its n+1 symbols from its tail: equal finite prefixes are compared
        # here, not one prefix with itself.
        check(finite_prefix((1,), (0,), n+1) == finite_prefix(prefix, (1, 0), n+1), ("word read from its tail", n))
        check(not recurrent(prefix, (0,)))
        check(recurrent(prefix, (1, 0)))
        # Past the shared prefix the tails differ, and a recurrent tail may begin with zero.
        check(finite_prefix(prefix, (0,), n+5)[n+1:] == (0, 0, 0, 0), n)
        check(finite_prefix(prefix, (1, 0), n+5)[n+1:] == (1, 0, 1, 0), n)
        observed = finite_prefix(prefix, (0, 1), n+5)
        check(len(observed) == n+5 and observed == prefix + (0, 1, 0, 1), (n, observed))
        check(recurrent(prefix, (0, 1)), "a recurrent tail may begin with zero")
    # Both continuations satisfy the no-adjacent-ones constraint in M5.
    word = finite_prefix((1, 0, 0), (1, 0), 20)
    check(all(not (a and b) for a, b in zip(word, word[1:])))


def t_M05_charged_residual():
    check(residual_accepts(4, (1,), (2,)))
    check(not residual_accepts(4, (3,), (2,)))
    check(residual_accepts(4, (1, 2), (1,)))
    check(not residual_accepts(4, (5,), ()))
    for cost in range(6):
        direct = cost <= 1
        check(residual_accepts(4, (1, 2), (cost,)) == direct)


def t_M06_restart_intervention():
    check(tuple(restarts(c, p) for c, p in product((False, True), repeat=2)) == (False, True, True, True))
    check(restarts(False, True) == restarts(True, True))
    check(restarts(False, False) != restarts(True, False))


def t_M07_witness_floor_budget():
    check([upkeep(n)[0] >= F(1, 8) for n in range(1, 6)] == [True, True, True, False, False])
    for n in (1, 2, 3, 4, 32, 100):
        witness, spent = upkeep(n)
        check(0 < witness and spent < 1 and witness + spent == 1)
    # Exact fractions avoid cancellation in 1-(1-2^-n).
    check(upkeep(100)[0] == F(1, 1267650600228229401496703205376))
    # The same witnesses as events under the declared law with c=1 and budget 1: every
    # executed horizon is paid and the remaining balance is the witness. Payment for an
    # infinite horizon (Proposition M15(d)) is not executed; it remains analytic.
    for horizon in (1, 2, 3, 4, 8, 32, 100):
        sigmas = tuple(upkeep(n)[0] for n in range(1, horizon + 1))
        check(paid_events(1, sigmas, 1) == horizon, horizon)
        check(1 - word_charge(1, sigmas) == upkeep(horizon)[0], horizon)
    # Exact cap with mixed signs; at a zero balance a further event is refused, and the
    # first unaffordable event ends the paid prefix although later events are cheaper.
    check(paid_events(F(1, 2), (1, -1, 1), F(3, 2)) == 3 and word_charge(F(1, 2), (1, -1, 1)) == F(3, 2))
    check(paid_events(F(1, 2), (1, -1, 1, F(-1, 3)), F(3, 2)) == 3)
    check(paid_events(1, (1, 2, 0, F(1, 3)), 2) == 1)
    # Declared rational floors s and budgets R (Proposition M15(a); s=1 with integer
    # amplitudes is M15(c)): amplitudes of at least s are paid for at most R/(cs) events;
    # a held floor of either sign is refused at the first event past floor(R/(cs)), the
    # first whose charge no longer fits.
    for c, budget, s, cap in ((F(1, 2), F(3, 2), F(1, 3), 9), (F(1), F(2), F(3, 2), 1), (F(3, 2), F(9, 2), 1, 3)):
        held = ((s,) * 12, (-s,) * 12, (s, -s) * 6)
        for word in held + ((2 * s, -s) * 6,):
            paid = paid_events(c, word, budget)
            check(paid * c * s <= budget, (c, budget, s, word, paid))
            check(word_charge(c, word[:paid]) <= budget < word_charge(c, word[:paid + 1]), (c, budget, word, paid))
            if word in held:
                check(paid == cap, (c, budget, s, word, paid))
        if cap * c * s == budget:
            check(word_charge(c, (s,) * cap) == budget, (c, budget, s))
    # Every word of up to three events over integer and rational amplitudes of both signs:
    # the balance is debited here step by step without the model, and each running charge
    # and the paid prefix must agree with it.
    amplitudes = (-2, -1, F(-1, 3), 0, F(1, 3), 1, F(3, 2))
    for c, budget in ((F(1, 2), F(3, 2)), (F(1), F(2)), (F(3, 2), F(9, 2))):
        for length in range(4):
            for sigmas in product(amplitudes, repeat=length):
                balance, paid = budget, 0
                for sigma in sigmas:
                    cost = c * sigma if sigma >= 0 else c * -sigma
                    if cost > balance:
                        break
                    balance, paid = balance - cost, paid + 1
                    check(word_charge(c, sigmas[:paid]) == budget - balance, (c, budget, sigmas, paid))
                check(paid_events(c, sigmas, budget) == paid, (c, budget, sigmas, paid))


def t_M08_joint_shares():
    rows = [(theta, *shares(theta, pad)) for theta, pad in product((0, 1), repeat=2)]
    for index in (1, 2):
        for observed in (0, 1):
            check(sorted(row[0] for row in rows if row[index] == observed) == [0, 1])
    check(all(theta == (left ^ right) for theta, left, right in rows))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--teeth", action="store_true", help="the default action; kept for the documented commands")
    parser.add_argument("--json", type=str, help="write named outcomes to this file")
    args = parser.parse_args()
    tests = sorted((n, f) for n, f in globals().items() if n.startswith("t_") and callable(f))
    results = []
    for name, test in tests:
        try:
            test()
        except AssertionError as exc:
            results.append({"name": name, "status": "FAIL", "detail": str(exc)})
            print("FAIL " + name + ": " + str(exc))
        except Exception as exc:
            results.append({"name": name, "status": "ERROR", "detail": repr(exc)})
            print("ERROR " + name + ": " + repr(exc))
        else:
            results.append({"name": name, "status": "PASS"})
    passed = sum(r["status"] == "PASS" for r in results)
    print("teeth: %d/%d" % (passed, len(tests)))
    if args.json:
        from pathlib import Path
        Path(args.json).write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    return 0 if tests and passed == len(tests) else 1

if __name__ == "__main__":
    sys.exit(main())
