# Compact-cover technical foundations

`CompactCoverTechnical.lean` closes the representation-independent technical
facts needed by `compact-cover.md`.

Lean proves:

- every exact globally decodable cover encoding is injective and cannot reduce
  finite cardinality;
- the complete function-space cover has cardinality `|R|^|Gamma|`;
- every nonempty partial frontier retains an injective full base-ring fixed
  embedding;
- public restriction, duplication, and reindexing preserve addition and
  multiplication;
- scheduled relabeling by coordinate-dependent public automorphisms preserves
  ring operations;
- relabeling transports the fixed embedding by public composition of labels;
- ciphertext storage is monotone in frontier width; and
- the extracted target schedule has peak width 368, with checked full and
  scheduled residue counts.

The corresponding executable schedule extractor is
`Parameter-Selection/python/proof/compact_cover_schedule.py`. For the
degree-65536 thin BGV target it verifies that 362 distinct switch
automorphisms generate the full group of order 65536, while the native
baby-step/giant-step evaluator keeps at most 368 ciphertexts live.

These results show that exact global compression is impossible but scheduled
partial covers are materially smaller. The remaining theorem is cryptographic:
jointly simulate every branch-creation, frontier-rebasing, and cyclic-return
transition from one ordinary Binary-NTT RLWE source.

Principal declarations:

- `exactCompression_card_le`
- `exactFullCover_power_le`
- `restrictedFixedEmbedding_injective`
- `reindex_add`
- `reindex_mul`
- `relabel_add`
- `relabel_mul`
- `relabel_restrictedFixedEmbedding`
- `scheduled_peak_le_full`
- `target_badDimensionPeakWidth`
- `target_fullCiphertextResidues`
- `target_scheduledCiphertextResidues`
