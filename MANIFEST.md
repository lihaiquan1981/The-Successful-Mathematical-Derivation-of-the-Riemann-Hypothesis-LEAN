Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn

# MANIFEST

Master directory and integrity table of the delivered folder. Every file
carries a SHA-256 checksum so that re-checkers can verify — via `sha256sum`
comparison — that the files are untampered and bit-identical to the sources
that passed compilation.

- Toolchain: Lean 4.34.0-rc2 (commit 6a10ac8) + mathlib v4.34.0-rc2
- Reproduction: see `reproduce_build.sh`; complete per-module build logs in
  `build_logs/`

## 1. Lean sources (11 modules)

| File | Module / namespace | Paper section | SHA-256 |
|---|---|---|---|
| `MotherEquation_CoreVerification.lean` | single file (zero mathlib) | Algebraic heart of the Mother Equation | `9b01ead8…72fcb570` |
| `Theorem_9_3A.lean` | `RH93` (standalone) | Theorem 9.3A | `9ab78bce…39265d55` |
| `Lemma_9_5C.lean` | `RH95C` | Lemma 9.5C (¶593–627) | `2e4e009c…5d387234` |
| `Unitarity_Assembly.lean` | `RH95U` | Theorems 9.5/10 (¶8.1 free-v replica) | `366153ea…1217dcd6` |
| `Lemma_9_4.lean` | `RH94` | Lemma 9.4 (¶467–536) | `50999ed5…b25eab4a` |
| `Theorem_9_5_Closure.lean` | `RH95Final` | Theorems 9.5/10 closed loop (per-f premise `SatisfiesUnitarity`) | `056e4615…e9cc8c45` |
| `Lemma_11_3.lean` | `RH113` | Lemma 11.3 (¶973–996) + the 12.1 usage | `18f6b78d…44cf42c6` |
| `Final_Assembly.lean` | `RHFinal` | `RH_general` / `RH_xi` / `RH_xi_zeros` | `6f929343…6c4fbd26` |
| `Note_9_5B_mJet.lean` | `RHM` | Note 9.5B (¶666–698) / Note 11.2.3 | `abf40336…c40240ee` |
| `Final_Assembly_Unconditional.lean` | `RHFinalM` | `RH_xi_unconditional` (hE_pos with zero witness) | `c37f387e…9a4d1ea4` |
| `Lemma_9_5C_TaylorRemainder.lean` | `RHT` | Lemma 9.5C Taylor-remainder upgrade | `3db25458…f8d7c2ff` |
Full 64-digit checksums in Section 4.

## 2. Auxiliary files

| File | Description |
|---|---|
| `README.md` | Build instructions, module chain, explicit premise list |
| `Verification_Report.md` | Master verification report (incl. the premise table ↔ the paper's "two conditions" verbatim correspondence) |
| `reproduce_build.sh` | One-command reproduction script (topological-order compilation) |
| `MANIFEST.md` | This manifest |
| `*.lean.txt` (11) | Plain-text copies of the `.lean` sources, for reviewers without a Lean environment |
| `build_logs/*.log` (11) | Complete per-module `lake env lean` output (incl. `#print axioms` audits), for re-checker comparison |

## 3. Build-log directory

| Log | Module | Exit code |
|---|---|---|
| `build_logs/Lemma_9_5C.log` | RH95C | 0 |
| `build_logs/Unitarity_Assembly.log` | RH95U | 0 |
| `build_logs/Lemma_9_4.log` | RH94 | 0 |
| `build_logs/Theorem_9_5_Closure.log` | RH95Final | 0 |
| `build_logs/Lemma_11_3.log` | RH113 | 0 |
| `build_logs/Final_Assembly.log` | RHFinal | 0 |
| `build_logs/Note_9_5B_mJet.log` | RHM | 0 |
| `build_logs/Final_Assembly_Unconditional.log` | RHFinalM | 0 |
| `build_logs/Lemma_9_5C_TaylorRemainder.log` | RHT | 0 |
| `build_logs/Theorem_9_3A.log` | RH93 | 0 |
| `build_logs/MotherEquation_CoreVerification.log` | single file | 0 |

## 4. Full SHA-256 table

```
6f929343c4c771267514a50f3869bc674a51afc25029dc5322c7b4956c4fbd26  Final_Assembly.lean
c37f387e3ad0f91ccb0906e6ff904cd00e9a4715f9c67448571ac69e9a4d1ea4  Final_Assembly_Unconditional.lean
18f6b78d1d8ed6111585c9a28b99779a762c40c787ea5f0dd33ff64144cf42c6  Lemma_11_3.lean
50999ed5f77d5ec1b636c1b0ae826d7a818921a9d9b226187b94b0b0b25eab4a  Lemma_9_4.lean
2e4e009c89af132ba032e96406dd56560fe0a53b1424afe9a6a93d225d387234  Lemma_9_5C.lean
3db25458843c8305f4af0f79f25d09b51368b3f4a2387de54ee5cadef8d7c2ff  Lemma_9_5C_TaylorRemainder.lean
9b01ead8329ecd2a447d7cd0346501aa6fc4d89a8d7b210524b4b31272fcb570  MotherEquation_CoreVerification.lean
abf403369b4a07f705678a85950a38791979a844d06204e7dc5f26bec40240ee  Note_9_5B_mJet.lean
9ab78bcef382706708ac9b9618ef8e54b950d065cdd960b578df030639265d55  Theorem_9_3A.lean
056e461585fbfcf967e2d9aff2ac8cff7612c1b3d9cfe4259e6fa5ebe9cc8c45  Theorem_9_5_Closure.lean
366153ea627e2c6d962afd3110ccbc8e1ca2766e36daa1ffd0ee7d941217dcd6  Unitarity_Assembly.lean
```

(Each `.lean.txt` copy is bit-identical to its `.lean` source and shares the
same checksum.)
