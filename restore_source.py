#!/usr/bin/env python3
"""Verify a losslessly compressed log; optionally restore the original source tree."""
from pathlib import Path
import argparse, gzip, hashlib, json, shutil

ROOT = Path(__file__).resolve().parent

def digest(data):
    return hashlib.sha256(data).hexdigest()

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def safe_path(root, rel):
    p = Path(rel)
    require(not p.is_absolute() and '..' not in p.parts, 'Unsafe manifest path')
    return root / p

def verify_historical(source, virtual_rel=None, virtual_bytes=None):
    def read(rel):
        return virtual_bytes if rel == virtual_rel else safe_path(source, rel).read_bytes()
    for line in (source / 'SHA256SUMS').read_text().splitlines():
        if not line.strip():
            continue
        expected, rel = line.split(maxsplit=1)
        rel = rel.lstrip('*')
        require(digest(read(rel)) == expected, 'Historical hash mismatch: ' + rel)
    review = source / 'independent_review'
    for rel, expected in json.loads((review / 'SHA256SUMS.json').read_text()).items():
        full = 'independent_review/' + rel
        require(digest(read(full)) == expected, 'Historical review hash mismatch: ' + rel)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--restore', type=Path, help='Create a new directory with the restored original source tree; refuses existing paths.')
    args = ap.parse_args()
    mapping = json.loads((ROOT / 'COMPRESSED_LOG.json').read_text())
    compressed = safe_path(ROOT, mapping['compressed_path']).read_bytes()
    require(len(compressed) == mapping['compressed_size'] and digest(compressed) == mapping['gzip_sha256'], 'Compressed log mismatch')
    raw = gzip.decompress(compressed)
    require(len(raw) == mapping['original_size'] and digest(raw) == mapping['original_sha256'], 'Decompressed log mismatch')
    source_rel = str(Path(mapping['original_path']).relative_to('source'))
    verify_historical(ROOT / 'source', source_rel, raw)
    print('PASS: compressed identity, decompressed identity, original package and review manifests')
    if args.restore is not None:
        target = args.restore.resolve()
        require(not target.exists(), 'Restore destination already exists; nothing overwritten')
        shutil.copytree(ROOT / 'source', target)
        safe_path(target, source_rel).write_bytes(raw)
        packed_rel = str(Path(mapping['compressed_path']).relative_to('source'))
        safe_path(target, packed_rel).unlink()
        verify_historical(target)
        print('PASS: restored original source tree at ' + str(target))
    print('No Lean compilation was performed.')

if __name__ == '__main__':
    main()
