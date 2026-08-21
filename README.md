# Infinity

**On Completed Infinity** — a short position note on the foundations of
mathematics: the distinction between potential and actual infinity, the status
of the Axiom of Infinity, and why disputing a premise is not the same as
alleging an error.

> Cantor's diagonal argument is a valid derivation within ZFC. I deny one of its
> premises, so I do not accept its conclusion. This is not a claim that the
> derivation contains an error.

**Read it:** <https://ndg13b.github.io/Infinity/>

## What's here

| Path | What it is |
| --- | --- |
| [`on-completed-infinity.md`](on-completed-infinity.md) | The note in plain Markdown. This is the canonical text. |
| [`index.html`](index.html) | The same text, typeset for the web. No build step, no dependencies. |
| [`.github/workflows/pages.yml`](.github/workflows/pages.yml) | Publishes the page on every push to `main`. |

The two copies are kept in step by hand: if you edit the Markdown, carry the
same edit into `index.html`.

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
