#!/usr/bin/env bash
# Build the standalone, student-facing coqdoc site into ./site
#
#   - includes shared / lecture / exercises / summary for every chapter
#   - OMITS solutions and instructor guides
#   - orders chapters by the dependency chain (AE -> ... -> RSEMon)
#   - themes coqdoc's output and writes a custom landing page
#
# Requires a built development (.glob files): run `make` first.
# (Future: an Alectryon pass over the *lecture* files would slot in here,
#  once a Rocq-9.x-compatible engine is available.)

set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

SRC=docs-src
OUT=site

# chapter table: dir | stem | group | title | one-line description
#                (kept in dependency order)
read -r -d '' TABLE <<'EOF' || true
AE|ae|Expressions & binding|Arithmetic Expressions|The AE language and its evaluator — the starting point.
ABE|abe|Expressions & binding|Adding Booleans|Booleans, a conditional, and a first type checker.
IDs|ids|Expressions & binding|Adding Identifiers|Immutable bindings and substitution.
Env|env|Expressions & binding|Adding Environments|Deferred substitution via environments.
Func|func|Functions & recursion|Adding Functions|Closures, scoping, strict vs lazy, and elaboration.
Rec|rec|Functions & recursion|Untyped Recursion|Recursion with no new construct: the Y and Z combinators.
TFun|tfun|Types|Typed Functions|A typed language with its type checker.
TRec|trec|Types|Typed Recursion|A typed fix: type safety with recursion restored.
DS|ds|Types|Data Structures|Products, sums, and lists as first-class types with a type checker and evaluator.
RMon|rmon|Monadic type checkers|Reader Monad|Refactoring the checker with a Reader monad (agreement theorem).
EMon|emon|Monadic type checkers|Reader + Either|Descriptive error messages and a refinement theorem.
State|state|Mutable state|Mutable State|Reference cells and an explicitly threaded store.
SMon|smon|Mutable state|State Monad|Hiding the store threading behind a State monad.
RSMon|rsmon|Combining effects|Reader + State|One monad hiding both the environment and the store.
RSEMon|rsemon|Combining effects|Reader + State + Either|The capstone: three effects in one monad.
EOF

# --- guard: coqdoc needs globalization info from a build ---
if ! ls AE/*.glob >/dev/null 2>&1; then
  echo "error: no .glob files found — run 'make' first." >&2
  exit 1
fi

rm -rf "$OUT"; mkdir -p "$OUT"

# --- assemble coqdoc args in dependency order (student-facing files only) ---
QARGS=(); FILES=()
while IFS='|' read -r dir stem group title desc; do
  [ -z "${dir:-}" ] && continue
  QARGS+=(-Q "$dir" "")
  FILES+=("$dir/plih_rocq_${stem}_shared.v"
          "$dir/plih_${stem}_lecture.v"
          "$dir/plih_${stem}_exercises.v"
          "$dir/plih_${stem}_summary.v")
done <<< "$TABLE"

echo "coqdoc: rendering ${#FILES[@]} student-facing files -> $OUT/"
rocq doc --html --toc --no-index --utf8 --interpolate --parse-comments --no-externals --no-lib-name \
  --with-header "$SRC/header.html" --with-footer "$SRC/footer.html" \
  -d "$OUT" "${QARGS[@]}" "${FILES[@]}"

# --- layer the theme on top of coqdoc's default stylesheet ---
# Drop coqdoc's stock `#header {...}` rules: our nav is `#topnav`, so those
# selectors are dead here and their bare border-style trips CSS linters.
perl -0pi -e 's/#header[^{}]*\{[^{}]*\}\s*//g' "$OUT/coqdoc.css"
cat "$SRC/theme.css" >> "$OUT/coqdoc.css"

# --- landing page (index.html) ---
{
  cat "$SRC/index-head.html"
  prev_group=""
  while IFS='|' read -r dir stem group title desc; do
    [ -z "${dir:-}" ] && continue
    if [ "$group" != "$prev_group" ]; then
      printf '  <div class="grp">%s</div>\n' "$group"
      prev_group="$group"
    fi
    printf '  <a class="item" href="plih_%s_lecture.html"><span class="tag">%s</span><span class="desc"><b>%s</b> — %s</span></a>\n' \
      "$stem" "$dir" "$title" "$desc"
  done <<< "$TABLE"
  cat "$SRC/index-foot.html"
} > "$OUT/index.html"

echo "done -> $OUT/index.html"
