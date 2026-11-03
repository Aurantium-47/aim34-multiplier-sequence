# Publication snapshot and evidence map

Prepared 3 November 2026. This presentation preserves the supplied proof source, audit evidence and historic manifests, except that one large public audit log is distributed as a lossless gzip file under `source/`. All other original files retain their bytes. Restore the log as described in COMPRESSION.md before using the historical manifests or reproduction scripts. `README.original.md` is an exact duplicate of `source/README.md`. The outer README, illustration and license-status notice are newly prepared presentation material.

## Verification boundaries

The current checks cover byte integrity, actual final theorem statements and definitions, evidence correspondence, ordinary arithmetic where supplied, public-content screening, local-link integrity and visual inspection. **Lean was not recompiled in this packaging pass.** The full Lean compilation and semantic-audit claims refer to the dated historical records inside `source/`, not a new execution. Independent AI-assisted review is not human peer review, journal acceptance or priority certification.

The outer `PUBLICATION_MANIFEST.json` covers every selected publication file except itself. `PUBLIC_FILES.txt` is the explicit allowlist (excluding the self-referential manifest). Historical manifests retain their original scope and must not be used to validate new presentation files.

## Reproduction and dependencies

Enter `source/` and follow its original reproduction instructions. Lean 4.19.0, the pinned mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b and recorded transitive dependency revisions must be provisioned separately. No compiler, mathlib source tree, compiled dependency object, third-party paper PDF or private original review archive is included. Source reproduction scripts are offline validators, not dependency installers.

## Source links

The historical AIM URL https://aimath.org/WWN/polyaschurlax/polyaschurlax.pdf returned HTTP 404 during current retrieval. Historical source-alignment records remain intact and hash-bound. Current primary-source cross-checks used https://math.hawaii.edu/~tom/mathfiles/czdssurvey.pdf (Problem 4.16, PDF p29) for AIM23 and https://math.hawaii.edu/home/talks/thesis.pdf (Problem 58, PDF p37) for AIM34. Those texts are linked, not redistributed.

## Rights

Publication is distinct from a new reuse license. No new license has been assigned. Preserve the credited authors, reused results and external dependency terms. See `LICENSE_STATUS.md`.

## AIM34 mapping

- Actual formal statements: `source/FullAIM34.lean`; scope and semantics: `source/AIM34Definitions.lean`, `source/independent_review/INDEPENDENT_REVIEW.md`.
- Historic replay and dependency identities: `source/PINS.json`, `source/verify_frozen.sh` and `source/independent_review/`.
- Original package hashes: `source/SHA256SUMS`.
- Six independent warning logs are normalized public copies: JensenIdentities, NonnegativeRootGeometry, JensenPositivity, RealRootGeometry, IntegerZeroUniqueness and SchwarzHalfPlane. Recorded original log hashes are intentionally distinct from public log hashes; `source/independent_review/PUBLIC_COPY_MAP.json` bridges them. The author-log mapping is retained separately in `source/AUTHOR_LOG_COPY_MAP.json`. Do not describe normalized logs as untouched originals.
- The original 247-file package is represented without data loss: 246 files are byte-identical and one log is losslessly compressed. Its original and compressed identities are recorded in COMPRESSED_LOG.json. The distribution tree is not a byte-identical copy until restored.
