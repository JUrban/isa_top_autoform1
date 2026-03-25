# Rules for Working on the Isabelle/HOL Formalization (Top1) - autoformalization of general tpology in top1.tex

## ABSOLUTE RULE: New proof code workflow

When writing ANY new proof code (skeleton, step, or edit):
1. The ONLY tactic allowed in new code is `sorry`
2. NO EXCEPTIONS — not `by fast`, not `by linarith`, not `by simp`,
   not `by (rule ...)`, not even `done`
3. After writing sorry-only code: compile, verify timing unchanged
4. Then replace sorry's via sledgehammer in batches of 3-5. If sledgehammer fails, you can very cautiosly experiment (e.g. by trying a subproof or the restricted apply (rule ...), apply (erule ...), apply (drule ...) ).
5. If you catch yourself typing anything other than `sorry`
     for a new step — STOP and replace with sorry

Note: The apply (rule ...), apply (erule ...), apply (drule ...) style
  restricts the search to specific rules, avoiding the exponential
  blowup that blast/auto cause in large contexts. Use this approach
  instead of by blast on complex goals -- use explicit apply chains.


## These rules describe how to work in **this Isabelle project**, whose main theory is:

- **Theory:** `Top1`
- **Imports:** `Complex_Main` (full import; do **not** add a separate “background” section inside `Top1.thy`)

The project is split into two sessions for faster incremental builds:
1. **Top0** (in `tst/i/`): Contains Chapters 2, 3, and 4. Built once and cached.
2. **Top1** (in `tst/`): Contains the main `Top1` theory and Chapters 5-8.

- **Build command (authoritative):**
  ```bash
cd /project/tst &&  /project/bin/isabelle build -D .
  ```

This will only build `Top0` once and cache it in an image; subsequent changes to `Top1` (Chapters 5-8) will not rebuild the first 3 chapters.

### Faster Incremental Workflows with Sessions
The project is split into `Top0` (Chapters 2-4 in `tst/i/`) and `Top1` (Main + Chapters 5-8 in `tst/`).
Build `Top0` once to cache it, then work on `Top1` to avoid rebuilding everything.

*   **Build/Cache Top0:** `/project/bin/isabelle build  -D . Top0`
*   **Build Top1 (incremental):** `/project/bin/isabelle build  -D . Top1`

The intended workflow is **gradual formalization** of /project/top1.tex : state results early, use `sorry` frequently, and keep the project building while steadily replacing `sorry` with real proofs.


Important: until further notice focus exclusively on sections 12-50 in
top1.tex and do not do exercises and examples unless really needed for
other lemmas. Note that sections 12-36 may be quite finished by
now. Your ultimate major goals should be important theorems such as
in sections 18-50.

Backups (bckXXXX) accompanied by descriptions of changes (CHNGESXXXX) must be done frequently (they are like commits).

Proofs have to be as structured as possible, introduce as many smaller helper lemmas as possible. Avoid complex long proofs as much as possible.


---

## 1. Build and sanity checks (do these often)

### Always build with
```bash
cd /project/tst && /project/bin/isabelle build -D .
```

### When to build
Build early and often:
- after adding/changing any definition
- after adding/changing any lemma/theorem statement
- after finishing any proof (or partial proof)
- after refactoring imports, locales, or file structure

### What “success” means
A successful build means Isabelle reports no errors for the session(s) in the directory.
Using `sorry` is acceptable (and expected), but the theory must still parse and build.

### Keep the run time low
Please run /project/bin/isabelle eval_at -t Top1_Ch5_8.thy [second-to-last-line] > timing_info_XXX 
and then grep the slowest tactics from the output and refactor; use
this often to decrease the run time - best below 30s or even less

---

###  Using process_theories + sledgehammer for proof development and speed optimization

Key principle: Use process_theories (not build) during proof development. It runs to completion without the session
timeout, so you can iterate freely.

Workflow for developing new proofs:
1. Write the proof structure with sledgehammer [timeout = 10] followed by sorry on each step.
2. Run: `/project/bin/isabelle process_theories -d . -l Top1 -O -o quick_and_dirty -M "Try this|No proof" -f Top1_Ch5_8.thy`
3. Collect all Try this: suggestions. Pick the fastest (lowest ms) for each step.
4. Replace all sledgehammer ... sorry blocks with the found proofs.
5. Run process_theories again (without -M) to verify and measure total time.
6. Only run isabelle build -D . for final verification against the session timeout.

Workflow for speeding up slow proofs:
1. Put sledgehammer [timeout = 10] + sorry on EVERY step of the slow proof (bulk, not one-by-one).
2. Run process_theories with -M "Try this|No proof" once.
3. Replace each step with the fastest suggested tactic.
4. Verify total time with process_theories. If still too slow, restructure the proof (merge/split steps) and repeat.

Critical lesson: A tactic that sledgehammer reports as "1 ms" can still cause a 100s slowdown in the kernel if it
triggers expensive unfolding. Always verify the actual wall-clock time with process_theories after substituting. If a
 step is slow, ask sledgehammer for alternatives — often a different lemma or approach (e.g., simp add: double_diff
vs metis ... closedin_on_def) makes a 100x difference.

Never: Run sledgehammer one step at a time in a loop — that wastes hours. Always bulk-annotate all steps, run once,
collect all results.


Also: The apply (rule ...), apply (erule ...), apply (drule ...) style
  restricts the search to specific rules, avoiding the exponential
  blowup that blast/auto cause in large contexts. Use this approach
  instead of by blast on complex goals -- use explicit apply chains.
                                  
### Using CLI tools with sessions
Specify the logic session with `-l` and the directory with `-d .` to leverage the cached heap images:

*   **process_theories**: `/project/bin/isabelle process_theories -d . -l Top1 -o quick_and_dirty -f Top1_Ch5_8.thy`
*   **eval_at**: `/project/bin/isabelle eval_at -d . -l Top1 Top1_Ch5_8.thy 100 'thm conjI'`

---

## 2. File and theory structure

### Main theory: `Top1.thy`
- `Top1` **imports `Complex_Main`** and should remain the main entry point.
- Note that some initial defs and theorems may need various fixing you might have to work on fixing them first.
- Many defs and theorems from top1.tex need to be added - work hard but carefully on adding them.
- Keep the file readable and structured with Isabelle sections (e.g. `section`, `subsection`, `text`), but **do not** create a separate explicit “Background” section in `Top1.thy`.

### Adding auxiliary theories (optional, only if it helps)
If `Top1.thy` becomes too large, you may split into helper theories (e.g. `Top1_Basics`, `Top1_Lemmas`, …), but:
- keep `Top1` as the canonical top-level theory,
- ensure `Top1` still imports everything needed (directly or indirectly),
- update the session build files appropriately so `/project/bin/isabelle build -D .` continues to work.

---

## 3. Gradual formalization policy (use `sorry` strategically)

### Allowed and encouraged
- Use `sorry` to keep momentum.
- Add intermediate lemmas with `sorry` rather than getting stuck inside a large proof.
- Replace one `sorry` at a time with real proofs, keeping the build green.
- Always improve badly stated lemmas and definitions - - having the correctly stated and faithful to top1.tex is critical.

### Preferred pattern
1. Write the *right statement* first (even with `sorry`).
2. Add minimal helper lemmas (possibly also with `sorry`).
3. Prove easy pieces immediately.
4. Chip away at the remaining `sorry`s until the file becomes mostly admit-free.

### Avoid
- Leaving large unstructured blocks of `sorry` without a plan.
- “Proving” by changing the statement to something weaker unless clearly justified.
- Duplicating facts that already exist in `Complex_Main` / Isabelle libraries.

---

## Figuring out proof state at various points
- Here is the general method how you can detect the proof state
  at several lines (e.g. XXX, YYY, ZZZ) of interest:
  `/project/bin/isabelle process_theories -O -o show_states -l Top1 -f 'Top1_Ch5_8.thy' | grep -A10 '\b\(XXX\|YYY\|ZZZ\)'`
- Please use this abundantly to figure out things.

## Figuring out errors:
- Try this:
`/project/bin/isabelle process_theories -l Top1 -f Top1_Ch5_8.thy -o quick_and_dirty`

## 4. Documentation and change logging

### Document changes in the source
- Use `text ‹ … ›` for prose explanations.
- Add short explanations before major definitions/theorems:
  - why the definition is chosen,
  - intended use,
  - key dependencies (e.g. “uses continuity results from Complex_Main”).

### Keep a running changelog (recommended)
Maintain a simple `CHANGES.md` (or similar) in the project root with:
- buildable milestones (date + short bullet list),
- notable new definitions/lemmas,
- which `sorry`s were removed or introduced and why.

Update: you should make numbered backup files (bckXXXX) and
  corresponding CHANGES files (CHANGESXXXX) after reasonable amount of
  work.

Ensure the build command above is used to validate each bckXXXX file.

---

## 5. Proof engineering guidelines (Isabelle/HOL)

### Use existing library facts first
Before proving something from scratch:
- browse `Complex_Main` facts - you can grep all of src/HOL/ theories
- prefer standard lemmas and simp rules over custom rewrite systems.

### Structure proofs for maintainability
- Split big theorems into named helper lemmas.
- Use `have`/`show` blocks and local facts to keep context clear.
- Prefer `simp`, `auto`, `blast`, `metis`, `linarith`, `field_simps`, etc., where appropriate.
- When automation is brittle, switch to structured proofs (`proof -`, `qed`) and add intermediate steps.

### Keep simp sets under control
- Add simp rules deliberately (`simp` attribute) and avoid global simp explosions.
- Prefer local `simp` calls with `simp add:` / `simp del:` when needed.

### Naming conventions
- Definitions: `top1_...` (or another consistent prefix used in the project)
- Lemmas/theorems: descriptive names; use suffixes like `_intro`, `_elim`, `_simp`, `_iff` when conventional.

---

## 6. Quality bar and progression targets

### The project must always build
At every stage, the directory should build with:
```bash
cd /project/tst && /project/bin/isabelle build -D .
```

### Progress targets
- Reduce the number of `sorry`s steadily over time.
- Prioritize the main results first, then corollaries/examples.
- Don’t leave “easy” holes behind if they block later work.

### If something is hard
Do **not** stall:
- isolate the hard part into one or more lemmas (with `sorry` temporarily),
- add notes in `text ‹ … ›` about intended proof strategy,
- continue with downstream development, then return to discharge the `sorry`s.

## ⚠ Careful Use of Potentially Exploding Tactics (Timeout Discipline)

When working in `Top1` (importing `Complex_Main`), automation can easily explode.
We must proceed in a way that makes **the failing tactic immediately identifiable**.

### 1. Treat these tactics as *high-risk*

Avoid using them in one-shot `by (...)` proofs:

* `simp`, `simp_all`
* `auto`, `force`, `fastforce`
* `blast`
* `meson`
* `metis`
* `smt`

Never stack them blindly. Never write:

```isabelle
by (auto simp: ...)
```

---

### 2. Always split automation into visible steps

Instead of:

```isabelle
by (auto simp: A B intro: C)
```

Write:

```isabelle
apply (simp add: A B)
apply (intro C)
apply blast
done
```

This ensures that if a timeout happens, we know **exactly which tactic** caused it.

---

### 3. Prefer restricted simplification

Never call raw `simp` on large goals.

Use:

```isabelle
apply (simp only: lemma1 lemma2)
```

or

```isabelle
apply (simp add: lemma1 del: problematic_rule)
```

Keep the simp set small and controlled.

---

### 4. Build proofs gradually using `sorry`

When developing:

* First create the lemma statement.
* Insert `sorry`.
* Compile.
* Replace `sorry` by **one small tactic step at a time**.
* Compile again.

Never introduce multiple heavy automation steps before recompiling.

* Try to reasonably follow the informal proofs from top1.tex . Look at
  them often when in doubt. You can deviate from them if needed.

* Do not increase the timeout of 120 seconds in the ROOT file unless
  absolutely necessary. The file needs to always compile fast. If you
  do increase it temporarily, you have to put it back to 120s ASAP. No
  high timeouts!

---

### 5. Debugging rule

If a build times out:

1. Replace the last automation step by `sorry`.
2. Recompile.
3. Reintroduce the step in smaller pieces.
4. If needed, replace:

   * `auto` → `simp` + `blast`
   * `blast` → structured `intro` / `elim`
   * `metis` → explicit lemma chain

Goal: **No opaque proof steps. Every automation must be locally attributable.**

---


### 6b. Diagnostic tools (`try0`, `sledgehammer`) — disciplined use

Use these **only to diagnose missing steps**, never as final proof code.

Typical local pattern:

```isabelle
have hU_open: "X - closure_on X TX ?V \<in> TX"
  sledgehammer [timeout = 10]
  sorry

have hA_disj_cl_D: "\<forall>D\<in>?\<DD>. \<forall>x\<in>A. x \<notin> closure_on X TX D"
  try0
  sorry
```

Run with live output:

```bash
/project/bin/isabelle process_theories -d . -l Top1 -O -o quick_and_dirty \
  -M "Trying|Found proof|Try this|No proof found|Sledgehammering|Timed out|Gave up" \
  -f Top1_Ch5_8.thy
```

Interpretation:

- `try0`: cheap portfolio (`simp`, `auto`, `blast`, …). If it reports *No proof found*, **do not increase effort** — restructure.
- `sledgehammer`: stronger search. On success prints `Try this: ...` → **replace the whole block with that proof**.

Example:

```
Sledgehammering...
cvc5: Try this: using closedin_on_def hclV_closed by blast
```

→ replace with:

```isabelle
using closedin_on_def hclV_closed by blast
```

Rules:

- Always follow with `sorry` (requires `-o quick_and_dirty`).
#### Performance note

These tools can help **speed up slow proofs indirectly**:

- Use `sledgehammer` to replace slow `auto`/`metis`/`blast` calls with simpler ones.
- Prefer the suggested minimal `using ... by blast` (smaller context = faster).
- If `try0`/`sledgehammer` fail, **do not increase timeouts** — restructure the proof.

They do **not** speed up existing proofs; they only help you find better ones.

- Remove `try0` / `sledgehammer` immediately after extracting the proof.
- Do not crank up timeouts; prefer **smaller subgoals** (`fix`/`assume`) and **reduced context** (`using ...`).
- Keep consistency with the timeout discipline: no opaque, all-in-one automation.


### 6. Golden rule

If a tactic touches:

* quantifiers,
* large disjunctions,
* many rewrite rules from `Complex_Main`,
* algebraic normalization,

assume it can explode.

Proceed minimally, explicitly, and incrementally.

