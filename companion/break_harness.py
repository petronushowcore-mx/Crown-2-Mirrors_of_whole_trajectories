"""Mutate isolated copies of the harness and compare each first failure with its named expectation.

A marker t_* is the one scientific model mutation of that named check. REACH:<site> is a further
damaging transformation whose first failure must be REACH_TARGETS[<site>]. SURVIVE:<site> is an
equivalent transformation at the same site that must leave every check passing."""
MUTATIONS = [
    ('t_M01_fibre_decoder', 'if reading in out and out[reading] != verdict:', 'if False and reading in out and out[reading] != verdict:', 'miss mixed observation fibre'),
    ('t_M02_rooted_lifting', 'frontier = {root}', 'frontier = {x for x in image if image[x] == target_path[0]}', 'replace declared root by arbitrary preimage'),
    ('t_M03_common_witness', 'return set.intersection(*map(set, obligations))', 'return set.union(*map(set, obligations))', 'confuse common witness with individual witnesses'),
    ('t_M04_finite_prefix_whole_tail', 'return any(cycle)', 'return any(prefix) or any(cycle)', 'mistake a past event for recurrence'),
    ('t_M05_charged_residual', 'remaining = budget - total_cost(charged_prefix)', 'remaining = budget', 'reset accumulated load'),
    ('t_M06_restart_intervention', 'return capable or request', 'return request', 'lose intrinsic restart capability'),
    ('t_M07_witness_floor_budget', 'witness = F(1, 2**steps)', 'witness = max(F(1, 8), F(1, 2**steps))', 'claim a persistent witness floor under the same cost schedule'),
    ('t_M08_joint_shares', 'return pad, theta ^ pad', 'return pad, theta', 'leak the hidden bit through one share'),
    ('SURVIVE:rename', 'def total_cost(values):\n    return sum(values)', 'def total_cost(items):\n    return sum(items)', 'rename local parameter'),
    ('REACH:rename', 'def total_cost(values):\n    return sum(values)', 'def total_cost(values):\n    return 0', 'destroy same computation site'),
    ('REACH:lift-step', 'frontier = {v for u, v in edges if u in frontier and image[v] == target}', 'frontier = {v for u, v in edges if u in frontier}', 'drop the destination-image condition of a lifted step'),
    ('REACH:lift-root', 'if not target_path or image[root] != target_path[0]:', 'if not target_path:', 'drop the root-image condition of a lift'),
    ('SURVIVE:labels', 'a, b = "a", "b"', 'a, b = "b", "a"', 'swap the target states in the image and in every target path'),
    ('REACH:labels', 'image = {"r": a, "s": a, "t": b}', 'image = {"r": b, "s": b, "t": a}', 'swap the target states in the image only'),
    ('SURVIVE:tail', 'return tuple(prefix[k] if k < len(prefix) else cycle[(k-len(prefix)) % len(cycle)] for k in range(size))', 'cycle = cycle + cycle\n    return tuple(prefix[k] if k < len(prefix) else cycle[(k-len(prefix)) % len(cycle)] for k in range(size))', 'represent the same tail with a doubled period'),
    ('REACH:tail', 'return tuple(prefix[k] if k < len(prefix) else cycle[(k-len(prefix)) % len(cycle)] for k in range(size))', 'return tuple(prefix[:size])', 'slice the prefix in place of continuing with the tail'),
    ('SURVIVE:recurrence', 'return any(cycle)', 'return any(cycle + cycle)', 'decide recurrence on a doubled period'),
    ('REACH:recurrence', 'return any(cycle)', 'return cycle[0] == 1', 'decide recurrence by the first symbol of the period'),
    ('REACH:charge', 'return c * abs(sigma)', 'return c * sigma', 'let signed charges cancel'),
    ('SURVIVE:total', 'return sum((event_charge(c, sigma) for sigma in sigmas), F(0))', 'return sum((event_charge(c, sigma) for sigma in reversed(sigmas)), F(0))', 'add the same absolute charges in reverse order'),
    ('REACH:total', 'return sum((event_charge(c, sigma) for sigma in sigmas), F(0))', 'return sum((event_charge(c, sigma) for sigma in sigmas[-1:]), F(0))', 'charge only the final amplitude'),
]
REACH_TARGETS = {
    'rename': 't_M05_charged_residual',
    'lift-step': 't_M02_rooted_lifting',
    'lift-root': 't_M02_rooted_lifting',
    'labels': 't_M02_rooted_lifting',
    'tail': 't_M04_finite_prefix_whole_tail',
    'recurrence': 't_M04_finite_prefix_whole_tail',
    'charge': 't_M07_witness_floor_budget',
    'total': 't_M07_witness_floor_budget',
}

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import re


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(source, folder):
    program = folder / "harness.py"
    output = folder / "outcomes.json"
    program.write_text(source, encoding="utf-8", newline="\n")
    if output.exists():
        output.unlink()
    try:
        proc = subprocess.run([sys.executable, "-B", *(["-O"] * sys.flags.optimize), str(program), "--teeth", "--json", str(output)], capture_output=True, text=True, encoding="utf-8", timeout=30)
    except subprocess.TimeoutExpired:
        return {"rc": "TIMEOUT", "rows": [], "stdout": "", "stderr": "timeout after 30 s"}
    rows = json.loads(output.read_text(encoding="utf-8")) if output.exists() else []
    return {"rc": proc.returncode, "rows": rows, "stdout": proc.stdout, "stderr": proc.stderr}


def streams_clean(result, rows):
    """Every stdout line is the summary or the FAIL line of a failing check, and stderr is empty;
    an unrecognised line or any stderr output fails the case."""
    if result["stderr"].strip():
        return False
    failing = {row["name"] for row in rows if row["status"] == "FAIL"}
    summary = "teeth: %d/%d" % (len(rows) - len(failing), len(rows))
    for line in result["stdout"].splitlines():
        match = re.match(r"^FAIL (t_\w+):( |$)", line)
        if line != summary and not (match and match.group(1) in failing):
            return False
    return True


def verdict_controls():
    """The streams check accepts clean output and refuses a stray stdout line, a stderr line and the
    FAIL line of a passing check."""
    rows = [{"name": "t_a", "status": "PASS"}, {"name": "t_b", "status": "FAIL"}]
    clean = {"rc": 1, "rows": rows, "stdout": "FAIL t_b: detail\nteeth: 1/2\n", "stderr": ""}
    if not streams_clean(clean, rows):
        raise SystemExit("VERDICT_CONTROL: clean streams refused")
    if not streams_clean(dict(clean, stdout="FAIL t_b:\nteeth: 1/2\n"), rows):
        raise SystemExit("VERDICT_CONTROL: a bare FAIL line refused")
    for name, broken in (("a stray stdout line", dict(clean, stdout=clean["stdout"] + "stray\n")),
                         ("a stderr line", dict(clean, stderr="warning\n")),
                         ("the FAIL line of a passing check", dict(clean, stdout="FAIL t_a: x\n" + clean["stdout"]))):
        if streams_clean(broken, rows):
            raise SystemExit("VERDICT_CONTROL: " + name + " accepted")


def verdict(result, marker, expected):
    rows = result["rows"]
    names = [row["name"] for row in rows]
    if marker.startswith("REACH:"):
        marker = REACH_TARGETS.get(marker[len("REACH:"):], "")
    if names != expected or any(row["status"] not in ("PASS", "FAIL") for row in rows):
        return False
    bad = [row["name"] for row in rows if row["status"] != "PASS"]
    summary = "teeth: %d/%d" % (len(rows)-len(bad), len(rows))
    if summary not in result["stdout"].splitlines():
        return False
    if not streams_clean(result, rows):
        return False
    if marker == "BASE" or marker.startswith("SURVIVE:"):
        return result["rc"] == 0 and not bad
    return result["rc"] == 1 and bool(bad) and bad[0] == marker and ("FAIL " + marker + ":") in result["stdout"]


def main():
    verdict_controls()
    here = Path(__file__).resolve().parent
    raw = (here / "harness.py").read_bytes()
    source = raw.decode("utf-8")
    expected = sorted(re.findall(r"^def (t_\w+)\(\):", source, re.M))
    markers = [m[0] for m in MUTATIONS if m[0].startswith("t_")]
    if sorted(markers) != expected or len(markers) != len(set(markers)):
        raise SystemExit("mutation registry does not cover the exact named check set")
    reach = [m[0][len("REACH:"):] for m in MUTATIONS if m[0].startswith("REACH:")]
    survive = [m[0][len("SURVIVE:"):] for m in MUTATIONS if m[0].startswith("SURVIVE:")]
    if (len(markers) + len(reach) + len(survive) != len(MUTATIONS) or sorted(reach) != sorted(REACH_TARGETS)
            or len(reach) != len(set(reach)) or len(survive) != len(set(survive))
            or not set(survive) <= set(reach) or not set(REACH_TARGETS.values()) <= set(expected)):
        raise SystemExit("mutation registry has an unknown, duplicate or unpaired control")
    report = {"harness_sha256": sha(raw), "breaker_sha256": sha(Path(__file__).read_bytes()), "python": sys.version, "optimisation": sys.flags.optimize, "expected_checks": expected, "cases": [], "status": "INCOMPLETE"}
    out = here / ("mutation-report-optimised.json" if sys.flags.optimize else "mutation-report.json")
    def save():
        out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    save()
    with tempfile.TemporaryDirectory(prefix="triad-model-") as temporary:
        folder = Path(temporary)
        base = run(source, folder)
        if not verdict(base, "BASE", expected):
            report["base"] = base
            save()
            raise SystemExit("BASE FAILED: " + base["stdout"] + base["stderr"])
        for marker, old, new, why in MUTATIONS:
            if source.count(old) != 1 or old == new:
                raise SystemExit("mutation anchor not unique or ineffective: " + marker)
            changed = source.replace(old, new)
            result = run(changed, folder)
            ok = verdict(result, marker, expected)
            report["cases"].append({"expected": marker, "reason": why, "ok": ok, "mutant_sha256": sha(changed.encode("utf-8")), **result})
            save()
    passed = sum(case["ok"] for case in report["cases"])
    report["status"] = "PASS" if passed == len(MUTATIONS) else "FAIL"
    save()
    for case in report["cases"]:
        if not case["ok"]:
            print("FAIL mutation " + case["expected"] + ": " + case["stdout"].replace("\n", " | ") + case["stderr"])
    print("mutations: %d/%d; source %s; report %s" % (passed, len(MUTATIONS), report["harness_sha256"][:12], out.name))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
