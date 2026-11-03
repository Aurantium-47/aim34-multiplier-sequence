# Lossless distribution of the large semantic-audit log

Only `source/independent_review/logs/023_IndependentSemanticAudit.log` changes storage representation: its original 28,573,132 bytes are distributed as a 3,713,906-byte `.log.gz`. No lines, records or mathematical evidence were removed. All other original source-package files are unchanged. This distributed source tree is not byte-identical to the original until restored.

`COMPRESSED_LOG.json` records the original path, byte count and SHA-256, the gzip identity and reproducible settings: gzip level 9, empty embedded filename and timestamp zero. Recompressing identical input with the recorded Python gzip/zlib implementation settings reproduces the selected bytes in the tested environment; the decompressed hash is the portable content identity.

Verify the compressed file, decompressed bytes and every original package/review manifest entry without altering this distribution:

    python3 restore_source.py

Restore the original source layout into a new directory (the command refuses an existing destination):

    python3 restore_source.py --restore ../aim34-restored-source

Then run the original checks and instructions inside that restored source directory. `source/SHA256SUMS`, `source/independent_review/SHA256SUMS.json` and the original replay script still refer to original decompressed paths and bytes; their historical contents are not rewritten to hide the packaging change. This new publication's manifest instead covers the gzip representation and restoration material.

The six previously normalized public warning logs and their original/public hash mapping in `source/independent_review/PUBLIC_COPY_MAP.json` remain unchanged. Compression of the semantic-audit log is a separate packaging operation, not an additional normalization of those six logs. Original replay records retain their original historical meaning.

Restoration uses Python's standard library, copies the source tree, reconstructs and verifies the one log, then removes only the copied gzip representation from the new restored directory. The compressed distribution and retained earlier original package are not changed. The current packaging checks and restoration do not compile Lean or establish new mathematical correctness, priority or human peer review.
