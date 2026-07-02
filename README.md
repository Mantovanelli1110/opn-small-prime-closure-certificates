# Certified Minimal-Prime Branch Closures for Odd Perfect Numbers

This repository contains the source and machine-readable certificate release for
the paper

`Certified Minimal-Prime Branch Closures for Odd Perfect Numbers`.

The frozen certificate release is

`C_small = C^{(2026-07)}_{5,7,11,13,17}`

where `C_small` denotes `C_{\mathrm{small}}` in the paper.

The corresponding Git release tag is `C-small-2026-07`.

The GitHub release page for this tag is
<https://github.com/Mantovanelli1110/opn-small-prime-closure-certificates/releases/tag/C-small-2026-07>.

The verifier scripts were tested with Python 3.14.4.
They use only the Python standard library.

## Contents

- `arxiv_q5_q17_closure.tex`: main arXiv source.
- `arxiv_q5_expanded_detail.tex`: expanded q=5 detail included by the main source.
- `references.bib`: bibliography.
- `q*_master_bundle.jsonl`: branch certificate bundles.
- `q*_branch_closure_verifier*.py`: verifier scripts listed in the paper.
- `cert_verifier_q5_strict.py`, `cert_verifier_q7_strict.py`,
  `cert_verifier_domain_extension_parametric_q5_all_q5n.py`: local verifier
  modules imported by the q=5 and q=7 wrapper scripts.
- `RELEASE_MANIFEST.tsv`: complete frozen file list, including entry-point
  artifacts and imported dependency modules.
- `SHA256SUMS.txt`: SHA256 manifest for the release files.

The paper's Table 6 lists the entry-point bundles and verifier scripts used in
the proof.  The complete frozen release is described by `RELEASE_MANIFEST.tsv`;
the corresponding file hashes are duplicated in `SHA256SUMS.txt`.

## Hash Check

Before running the verifiers, check the frozen release hashes:

```bash
sha256sum -c SHA256SUMS.txt
```

The release check for this revision is: first verify that all entries in
`SHA256SUMS.txt` match, then run the five verifier commands below.  The frozen
release was checked in that order.

## Clone and Verify the Frozen Release

From a fresh checkout, reproduce the frozen release state with:

```bash
git clone https://github.com/Mantovanelli1110/opn-small-prime-closure-certificates.git
cd opn-small-prime-closure-certificates
git checkout C-small-2026-07
sha256sum -c SHA256SUMS.txt
```

## Reproduction Commands

Run these commands from the repository root:

```bash
python q5_branch_closure_verifier_strict.py q5_master_bundle.jsonl
python q7_branch_closure_verifier.py q7_master_bundle.jsonl
python q11_branch_closure_verifier.py q11_master_bundle.jsonl
python q13_branch_closure_verifier.py q13_master_bundle.jsonl
python q17_branch_closure_verifier.py q17_master_bundle.jsonl
```

Each command should produce the branch-exhaustion terminal output stated in
Table 6 of the paper.

## Citation

Please cite the accompanying paper:

Marco Mantovanelli, *Certified Minimal-Prime Branch Closures for Odd Perfect
Numbers*, July 2026.

## License

This repository is released under the MIT License; see `LICENSE`.
