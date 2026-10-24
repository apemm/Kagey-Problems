# Automatic paper PDFs

After a source edit is committed to a branch on GitHub, **Update paper PDFs**
compiles the affected documents and adds a `Rebuild paper PDFs` commit on that
same branch. This works for edits made on the website or pushed from a computer.
Wait for the green check in the repository's **Actions** tab before downloading
the PDF. Pull the bot's commit before making further local edits.

The workflow builds Papers A, C, D, E and F, the S1-S3 notes, Problem 001 and its
expository notes, and both Problem 137 papers. Archived Paper B and removed
drafts are excluded. D's journal PDF, Online Resource and combined arXiv PDF are
all maintained. C and D are compiled with their supplements until references
stabilize. S3 builds C first because it imports C's theorem numbers.

Edit a main `.tex` file or any of its section/appendix files as usual. Included
figures, bibliography files, and local styles also trigger a rebuild. The
workflow checks source fingerprints against the last successful build, so rapid
successive edits are not lost. It only commits the configured PDFs and its build
state, never manuscript sources, auxiliary files, or proof computations. It does
not run Python enumerations, regenerate figures, or build Lean.

## Problem 001's single-file export

`pemmasani.tex` plus `sections/` is one source document. `pemmasani_jis.tex` is
another, standalone document. Both PDFs are compiled, but the workflow does not
overwrite either source. **Changes in `sections/` update `pemmasani.pdf`, not
the text of `pemmasani_jis.tex`.** The latter has also received direct edits.
When a fresh single-file export is wanted, first reconcile any direct edits and
then run `scripts/make_jis_single_file.py` in the `jis` directory and commit its
output. That commit triggers the corresponding PDF build.

## Failures and manual builds

A TeX error, unresolved reference, or duplicate label fails the build and leaves
the last committed PDFs intact. Open the failed run in **Actions** for the error
and downloadable logs. Fix the source and commit again. If another source commit
arrives while compilation is running, the older run does not publish over it;
the queued run uses the latest sources. No force pushes are used.

To rebuild all documents without editing a file, open **Actions → Update paper
PDFs → Run workflow**, select the branch, leave **Rebuild all** checked, and run.
The workflow also saves PDFs and logs as downloadable artifacts for fourteen days.
GitHub's built-in token makes the PDF commit without starting another push run.
No personal access token or repository secret is needed. The workflow requests
`contents: write`; protected branches must permit the bot's ordinary push if
branch protection is enabled in the future.

## Maintenance

`.github/papers.json` lists the main documents and cross-paper dependencies.
Add new paper folders there. Each group watches its directory recursively,
excluding archived drafts and configured output PDFs. Put shared input paths in
`extra_inputs` and groups whose auxiliary files are needed in `depends_on`.
Use pdfLaTeX with the pinned TeX Live container. Update the image digest in the
workflow deliberately when a newer distribution is needed. Bibliographies are
currently inline; adding BibTeX/Biber would require extending the build command.

Local checks, from the repository root:

```sh
python -m unittest discover -s scripts/tests -v
python scripts/paper_pdfs.py plan --all
python scripts/paper_pdfs.py build
```

The local build needs pdfLaTeX on PATH. It updates local PDFs but does not commit
or push. The `publish` subcommand is restricted to the Actions environment.

Implementation references: [workflow permissions](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#permissions),
[token-triggered events](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/trigger-a-workflow),
and the [TeX Live action](https://github.com/xu-cheng/texlive-action).
