# JSP-000301: consecutive powerful non-squares

Lean 4 formalization of the catalog yes/no question

> If two consecutive positive integers are powerful, must at least one be a perfect square?

as recorded in [The Justin Sun Prize](https://github.com/TheJustinSunPrize/awards) entry [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301).

The answer is **no**. The catalog already cites Golomb's pair

\[
12167 = 23^3, \qquad 12168 = 2^3 \cdot 3^2 \cdot 13^2.
\]

This repository machine-checks that both numbers are powerful and that neither is a square. It does **not** claim mathematical discovery. Solver credit remains with S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–855, as already recorded in the prize catalog. Walker (1976) later produced infinitely many further pairs; that infinitude result, and the counting question in [Erdős problem #365](https://www.erdosproblems.com/365), are out of scope.

## Theorems

| Name | Statement |
| --- | --- |
| `JSP000301.golomb_pair` | `12167` and `12168` are consecutive, both powerful, and neither a square |
| `JSP000301.jsp_000301` | `∃ n, Powerful n ∧ Powerful (n+1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n+1)` |
| `JSP000301.question_false` | negation of the universally quantified catalog question |

`Powerful n` means `n > 0` and every prime divisor `p` of `n` satisfies `p² ∣ n`, matching the catalog review note.

## Toolchain

- Lean `v4.34.0` (see `lean-toolchain`)
- **No Mathlib, Batteries, or other packages**
- No `sorry`, `admit`, `native_decide`, or project-declared axioms

Local axiom audit (`lake env lean Audit.lean`) reports only `[propext, Quot.sound]` on all three headline theorems.

## Reproduce

```sh
lake build
lake env lean Audit.lean
```

Requires [elan](https://github.com/leanprover/elan). The GitHub Actions workflow in `.github/workflows/lean.yml` rebuilds the same targets on every push.

## Attribution and priority

Formalization by [@golfyx](https://github.com/golfyx), with AI assistance (Cursor Grok 4.6). This submission is later than several independent public formalizations of the same catalog entry. It does not claim first-formalization priority. Maintainers should order submissions under the prize selection rules.

## License

The Lean source in this repository is released under Apache-2.0. The mathematical counterexample is classical literature.
