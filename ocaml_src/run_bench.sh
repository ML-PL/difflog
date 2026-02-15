#!/usr/bin/env bash
#
# run_bench.sh — Systematic benchmark of Difflog evaluators across all test cases
#
# Usage:
#   ./run_bench.sh [options]
#
# Options:
#   --evaluators LIST   Comma-separated evaluators (default: all four)
#   --tests LIST        Comma-separated test names (default: all found)
#   --learner NAME      Learner to use (default: HybridAnnealingLearner)
#   --scorer NAME       Scorer to use (default: L2Scorer)
#   --tgt-loss FLOAT    Target loss (default: 0.01)
#   --max-iters INT     Max iterations (default: 1000)
#   --timeout INT       Per-test timeout in seconds (default: 120)
#   --output FILE       Output JSONL file (default: bench_results.jsonl)
#   --summary           Print summary table after completion
#   --help              Show this help
#
# Requires: the difflog binary built via `dune build` in ocaml_src/
#

set -euo pipefail

# ── Defaults ──────────────────────────────────────────────────────────
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DATA_DIR="$REPO_ROOT/src/test/resources/ALPS/data"
TMPL_DIR="$REPO_ROOT/src/test/resources/ALPS/templates"

EVALUATORS="NaiveEvaluator,SeminaiveEvaluator,TrieEvaluator,TrieSemiEvaluator"
TESTS=""
LEARNER="HybridAnnealingLearner"
SCORER="L2Scorer"
TGT_LOSS="0.01"
MAX_ITERS="1000"
TIMEOUT=120
OUTPUT="bench_results.jsonl"
SHOW_SUMMARY=false

# ── Parse arguments ──────────────────────────────────────────────────
while [[ $# -gt 0 ]]; do
  case "$1" in
    --evaluators) EVALUATORS="$2"; shift 2 ;;
    --tests)      TESTS="$2"; shift 2 ;;
    --learner)    LEARNER="$2"; shift 2 ;;
    --scorer)     SCORER="$2"; shift 2 ;;
    --tgt-loss)   TGT_LOSS="$2"; shift 2 ;;
    --max-iters)  MAX_ITERS="$2"; shift 2 ;;
    --timeout)    TIMEOUT="$2"; shift 2 ;;
    --output)     OUTPUT="$2"; shift 2 ;;
    --summary)    SHOW_SUMMARY=true; shift ;;
    --help)
      head -n 18 "$0" | tail -n +2 | sed 's/^# \?//'
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      exit 1
      ;;
  esac
done

# ── Locate binary ────────────────────────────────────────────────────
DIFFLOG="$SCRIPT_DIR/_build/default/main.exe"
if [[ ! -x "$DIFFLOG" ]]; then
  echo "Binary not found at $DIFFLOG"
  echo "Please run 'dune build' in $SCRIPT_DIR first."
  exit 1
fi

# ── Discover tests ───────────────────────────────────────────────────
if [[ -z "$TESTS" ]]; then
  # Auto-discover: find all .d files that have matching .tp files
  TESTS=""
  for dfile in "$DATA_DIR"/*.d; do
    name="$(basename "$dfile" .d)"
    if [[ -f "$TMPL_DIR/$name.tp" ]]; then
      if [[ -n "$TESTS" ]]; then TESTS="$TESTS,"; fi
      TESTS="$TESTS$name"
    fi
  done
fi

# ── Convert comma-separated lists to arrays ──────────────────────────
IFS=',' read -ra EVAL_ARR <<< "$EVALUATORS"
IFS=',' read -ra TEST_ARR <<< "$TESTS"

N_EVALS=${#EVAL_ARR[@]}
N_TESTS=${#TEST_ARR[@]}
TOTAL=$((N_EVALS * N_TESTS))

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  Difflog Benchmark Suite                                    ║"
echo "╠══════════════════════════════════════════════════════════════╣"
echo "║  Tests:      $N_TESTS"
echo "║  Evaluators: $N_EVALS (${EVALUATORS})"
echo "║  Learner:    $LEARNER"
echo "║  Scorer:     $SCORER"
echo "║  Target:     loss < $TGT_LOSS, max $MAX_ITERS iterations"
echo "║  Timeout:    ${TIMEOUT}s per test"
echo "║  Output:     $OUTPUT"
echo "║  Total runs: $TOTAL"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# ── Clear output file ────────────────────────────────────────────────
> "$OUTPUT"

# ── Run benchmarks ───────────────────────────────────────────────────
COUNT=0
PASSED=0
FAILED=0
TIMED_OUT=0

for test_name in "${TEST_ARR[@]}"; do
  DATA_FILE="$DATA_DIR/$test_name.d"
  TMPL_FILE="$TMPL_DIR/$test_name.tp"

  for eval_name in "${EVAL_ARR[@]}"; do
    COUNT=$((COUNT + 1))
    printf "[%3d/%3d] %-25s %-22s ... " "$COUNT" "$TOTAL" "$test_name" "$eval_name"

    # Run with timeout, capture stdout (JSON) separately from stderr
    # Use perl-based timeout for macOS compatibility (no coreutils `timeout`)
    JSON_LINE=""
    EXITCODE=0
    if command -v gtimeout &>/dev/null; then
      TIMEOUT_CMD="gtimeout"
    elif command -v timeout &>/dev/null; then
      TIMEOUT_CMD="timeout"
    else
      TIMEOUT_CMD=""
    fi

    if [[ -n "$TIMEOUT_CMD" ]]; then
      JSON_LINE=$($TIMEOUT_CMD "${TIMEOUT}s" "$DIFFLOG" bench \
          "$DATA_FILE" "$TMPL_FILE" \
          "$LEARNER" "$eval_name" "$SCORER" \
          "$TGT_LOSS" "$MAX_ITERS" \
          2>/dev/null) || EXITCODE=$?
    else
      # No timeout command available; run without timeout
      JSON_LINE=$("$DIFFLOG" bench \
          "$DATA_FILE" "$TMPL_FILE" \
          "$LEARNER" "$eval_name" "$SCORER" \
          "$TGT_LOSS" "$MAX_ITERS" \
          2>/dev/null) || EXITCODE=$?
    fi

    if [[ $EXITCODE -eq 124 ]]; then
      # timeout
      TIMED_OUT=$((TIMED_OUT + 1))
      printf "TIMEOUT\n"
      # Write a timeout JSON record
      echo "{\"test\": \"$test_name\", \"evaluator\": \"$eval_name\", \"learner\": \"$LEARNER\", \"scorer\": \"$SCORER\", \"status\": \"timeout\", \"timeout_s\": $TIMEOUT}" >> "$OUTPUT"
    elif [[ $EXITCODE -ne 0 ]] || [[ -z "$JSON_LINE" ]]; then
      FAILED=$((FAILED + 1))
      printf "FAIL (exit %d)\n" "$EXITCODE"
      echo "{\"test\": \"$test_name\", \"evaluator\": \"$eval_name\", \"learner\": \"$LEARNER\", \"scorer\": \"$SCORER\", \"status\": \"error\", \"exit_code\": $EXITCODE}" >> "$OUTPUT"
    else
      # Parse key stats from JSON for summary line (macOS-compatible)
      extract_json() { python3 -c "import json,sys; d=json.loads(sys.argv[1]); print(d.get(sys.argv[2],'?'))" "$1" "$2" 2>/dev/null || echo "?"; }
      LOSS=$(extract_json "$JSON_LINE" "loss")
      ITERS=$(extract_json "$JSON_LINE" "iterations")
      TIME=$(extract_json "$JSON_LINE" "time_s")
      NRULES=$(extract_json "$JSON_LINE" "learned_rules_count")
      CONV=$(extract_json "$JSON_LINE" "converged")

      PASSED=$((PASSED + 1))
      if [[ "$CONV" == "true" ]] || [[ "$CONV" == "True" ]]; then
        STATUS_STR="OK"
      else
        STATUS_STR="UNCONVERGED"
      fi
      printf "%-12s loss=%-10s iters=%-5s rules=%-3s time=%ss\n" "$STATUS_STR" "$LOSS" "$ITERS" "$NRULES" "$TIME"
      echo "$JSON_LINE" >> "$OUTPUT"
    fi
  done
done

echo ""
echo "════════════════════════════════════════════════════════════════"
echo "  Completed: $COUNT runs  |  Passed: $PASSED  |  Failed: $FAILED  |  Timeout: $TIMED_OUT"
echo "  Results written to: $OUTPUT"
echo "════════════════════════════════════════════════════════════════"

# ── Summary table ────────────────────────────────────────────────────
if [[ "$SHOW_SUMMARY" == true ]] && command -v python3 &>/dev/null; then
  echo ""
  echo "Summary Table:"
  echo ""
  python3 - "$OUTPUT" <<'PYEOF'
import json, sys

results = []
with open(sys.argv[1]) as f:
    for line in f:
        line = line.strip()
        if line:
            results.append(json.loads(line))

if not results:
    print("  (no results)")
    sys.exit(0)

# Collect evaluator names and test names
evaluators = sorted(set(r.get("evaluator", "?") for r in results))
tests = []
seen = set()
for r in results:
    t = r.get("test", "?")
    if t not in seen:
        tests.append(t)
        seen.add(t)

# Build lookup
lookup = {}
for r in results:
    key = (r.get("test"), r.get("evaluator"))
    lookup[key] = r

# Print header
eval_short = {e: e.replace("Evaluator", "") for e in evaluators}
hdr = f"{'Test':<25s}"
for e in evaluators:
    hdr += f" | {eval_short[e]:>18s}"
print(hdr)
print("-" * len(hdr))

for t in tests:
    row = f"{t:<25s}"
    for e in evaluators:
        r = lookup.get((t, e))
        if r is None:
            cell = "---"
        elif r.get("status") == "timeout":
            cell = "TIMEOUT"
        elif r.get("status", "").startswith("error"):
            cell = "ERROR"
        else:
            loss = r.get("loss", -1)
            iters = r.get("iterations", -1)
            time_s = r.get("time_s", -1)
            conv = r.get("converged", False)
            mark = "+" if conv else "-"
            cell = f"{mark} {loss:.4f} {iters:>4d}i {time_s:.2f}s"
        row += f" | {cell:>18s}"
    print(row)

# Aggregate stats per evaluator
print("")
print(f"{'Aggregate':<25s}", end="")
for e in evaluators:
    ev_results = [r for r in results if r.get("evaluator") == e and r.get("status") == "ok"]
    n_conv = sum(1 for r in ev_results if r.get("converged"))
    n_total = len(ev_results)
    avg_time = sum(r.get("time_s", 0) for r in ev_results) / max(n_total, 1)
    avg_iters = sum(r.get("iterations", 0) for r in ev_results) / max(n_total, 1)
    cell = f"{n_conv}/{n_total} {avg_time:.2f}s"
    print(f" | {cell:>18s}", end="")
print()
PYEOF
fi
