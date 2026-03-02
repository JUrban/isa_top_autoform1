# Rules for Working on the Isabelle/HOL Formalization (Top1)

These rules describe how to work in **this Isabelle project**, whose main theory is:

- **Theory:** `Top1`
- **Imports:** `Complex_Main` (full import; do **not** add a separate “background” section inside `Top1.thy`)
- **Build command (authoritative):**
  ```bash
cd /project/tst &&  /project/bin/isabelle build -D .
  ```

The intended workflow is **gradual formalization** of /project/top1.tex : state results early, use `sorry` frequently, and keep the project building while steadily replacing `sorry` with real proofs.

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

---

## 2. File and theory structure

### Main theory: `Top1.thy`
- `Top1` **imports `Complex_Main`** and should remain the main entry point.
- Note that some initial defs and theorems are using broken syntax and you might have to work on fixing them first
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

### 6. Golden rule

If a tactic touches:

* quantifiers,
* large disjunctions,
* many rewrite rules from `Complex_Main`,
* algebraic normalization,

assume it can explode.

Proceed minimally, explicitly, and incrementally.

