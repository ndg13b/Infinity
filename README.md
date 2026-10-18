# Infinity

**On Completed Infinity** — a short position note on the foundations of
mathematics: the distinction between potential and actual infinity, the status
of the Axiom of Infinity, and why disputing a premise is not the same as
alleging an error.

> Cantor's diagonal argument is a valid derivation within ZFC. I deny one of its
> premises, so I do not accept its conclusion. This is not a claim that the
> derivation contains an error.

**Read it:**

- The note — <https://ndg13b.github.io/Infinity/>
- A machine-checked companion — <https://ndg13b.github.io/Infinity/formal.html>

## What's here

| Path | What it is |
| --- | --- |
| [`on-completed-infinity.md`](on-completed-infinity.md) | The note in plain Markdown. This is the canonical text. |
| [`index.html`](index.html) | The same text, typeset for the web. |
| [`formal.html`](formal.html) | The companion page: what the Lean developments check, and what they cannot. |
| [`assets/style.css`](assets/style.css) | Design tokens and layout shared by both pages. |
| [`formal/`](formal/) | Two Lean 4 developments — `Digits.lean` on the digit argument, `HF.lean` on the finite universe — with [`formal/README.md`](formal/README.md) stating their limits. |
| [`.github/workflows/pages.yml`](.github/workflows/pages.yml) | Publishes both pages on every push to `main`. |

No build step and no dependencies: the pages are plain HTML over one
stylesheet, and the proof needs only a Lean toolchain.

The note's two copies are kept in step by hand — if you edit the Markdown,
carry the same edit into `index.html`.

The companion page and `formal/` were written by Claude, not by the note's
author. The note makes no claim to machine-checked support, and the companion
says plainly which of its claims a proof can and cannot reach.

## Publishing the page

The workflow in `.github/workflows/pages.yml` deploys the repository root to
GitHub Pages whenever `main` changes, and turns Pages on itself the first time
it runs. Once it has run, the note is live at
<https://ndg13b.github.io/Infinity/>.

Two things worth knowing:

- **If Pages was never enabled**, the workflow enables it. Nothing to do —
  just merge to `main` and watch the run under the **Actions** tab.
- **If Pages is already set to "Deploy from a branch"**, the workflow's deploy
  step will fail, because that setting and Actions-based deployment are
  mutually exclusive. Either switch **Settings → Pages → Source** to
  **GitHub Actions**, or keep the branch setting (pointed at `main` / `root`,
  which serves `index.html` correctly on its own) and delete the workflow.

The `.nojekyll` file stops GitHub from running the page through Jekyll under
either setting.

## Licence

The MIT licence in [`LICENSE`](LICENSE) covers the code in this repository.
The text of the note is the author's own.
