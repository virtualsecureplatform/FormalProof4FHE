# Modified HasteBoots proof implementation

The target is complete protocol 12, schedule 5, non-hiding Brakedown, Goldilocks
first and BabyBear second. Preserve native degree 1024, LWE dimension 728,
public evaluation keys and output keys. The final target is application
soundness/knowledge and 128-bit expected work per false acceptance in an
explicit classical ideal-oracle model. Encryption privacy and zero knowledge
are separate claims.

## Implemented definitions and proofs

The `FormalProof4FHE.HasteBoots` namespace contains:

| Component | Mathematical statement | Source correspondence | Boundary |
| --- | --- | --- | --- |
| `MatrixOpening` | Ordered left aggregation followed by right folding equals direct MW-MLE evaluation | `HasteBoots/pcs/src/matrix_weighted.rs`; 2025/719 Appendix B.2 | Algebra only; authentication is an explicit premise |
| `MatrixFold` | Least-significant-variable-first Boolean folding equals the ordered full weight sum | `HasteBoots/algebra/src/matrix_weighted.rs` | Semantic cube indexing; the flat address adapter is supplied below, while Rust memory refinement remains open |
| `BlockCode` | For unpadded coordinate degree bound m and symbol width b, the semantic code has dimension b*m below saturation and block distance L-m+1 | ArkLib interleaved RS; `HasteBoots/docs/block-rs.md` | Layout and proximity bridges are supplied below; Rust NTT equivalence and availability remain open |
| `BlockEncoder` | Direct coordinate evaluation lies in the semantic code, is base-linear, and is injective when m <= L | Coordinate-polynomial phase of `encode_row` | Exact-field padded butterfly encoding is identified below by `NTTBlockEncoder`; optimized integer/Rust refinement remains open; flat layout and zero padding are covered by `RowLayout` |
| `RowLayout` | Flat addresses are block*b+lane; zero-padding is recoverable; padded encoding remains injective and lies in the semantic code | Rust gather/scatter layout in `encode_row` | Does not identify direct evaluation with the NTT implementation |
| `NativePublic` | Native NAND input addition, exact rounding, configured-stride LUT, initial accumulator and rotation bounds | `packed_pbs::public_inputs` and `packed_monomial` | Native trace composition is supplied by NativePBS; Rust equivalence remains open |
| `NativeBlindRotation` | Explicit negacyclic multiplication, rotation, radix external product, binary recurrence, trace generation and unique trace output; zero rounds are identity | Binary blind rotation and RGSW multiplication | NTT/key-format refinement and gadget parameter instantiation remain open |
| `NativeKeySwitch` | One-block gadget-product subtraction and partial sample extraction, with valid trace generation and unique output | Native equal-ring-dimension branch | Other dimension branches and NTT/key-format equivalence remain open |
| `NativePBS` | Complete coefficient-domain reference evaluation and independent trace relation; witness existence iff correct reference output; concrete public extractor and exact failure-measure identity | Composition of public preprocessing, binary rotation, bias, switching, extraction | Does not yet prove Rust equivalence or verifier enforcement |
| `CommonSource` | Unique common decoding of whole-column matrices; one total decoder with explicit far-word zero fallback; false coded responses differ in at least distance-minus-radius columns | Fixed-word PCS interpretation | No Merkle availability or efficient decoding claim |
| `RowSpanProximity` | Checked AHIV22 row-span proximity bound in the min-distance interface | ArkLib AHIV22 Lemma 4.5 | Uniform row-span law; sampler and symbol lifting are supplied below, while production XOF freshness remains open |
| `SymbolLift` | Basis assembly preserves distances and encodings, combines base test rows, and maps uniform full-width matrices to uniform symbol coefficients; alphabet size is card(F)^b | Block-symbol analysis; independent of lookup extension | Still conditional on fresh uniform production coins |
| `UniformImage` / `RowSpanSampling` | Surjective additive maps have uniform images; coefficient sampling induces uniform row-span sampling even for dependent rows; matrix proximity bound has denominator card(F)^b | AHIV22 sampler bridge | Fixed available word; shared-query bounds are supplied below, while transcript/Merkle arguments remain open |
| `CodeCorrespondence` / `BaseMatrixProximity` | Exact base-block/scalar-RS membership equivalence; packing preserves whole-column distance and common-source existence; matrix proximity bound takes the base-layout far premise | Complete symbol-field analysis bridge | Positive degree bound and symbol width; fresh production coins and Merkle availability remain open |
| `ColumnSampling` | Deduplication preserves the miss event; exactly good.card^Q ordered outcomes miss bad columns | Schedule-5 `sample_columns` | Counting only; stream freshness remains open |
| `ColumnOpening` | Exact uniform ordered-draw avoidance probability; deduplication preserves checks; false-response distance gives the query bound; shared checks and challenge-dependent responses need no independence assumption | Schedule-5 shared columns | Fresh later uniform draws are explicit; production XOF linkage remains open |
| `StructuredOpening` | A common coded source gives coded structured responses with the same error columns; false finished values satisfy the near-branch bound, including adaptive response choices | Near-source PCS argument | Abstract finishing map; the semantic native finishing adapter is supplied below, while Rust refinement remains open |
| `ProximityOpening` / `CommonSourceOpening` | Far-word bound for arbitrary challenge-dependent coded responses; one decoder and one shared query sample yield proximity loss plus the maximum of near/far column losses | Interactive fixed-available-word opening core | Native semantic response and finishing adapters are supplied below; Merkle availability and transcript compilation remain open |
| `ResponseAssembly` / `ResponseCoefficients` | Native base-field lane checks imply the scalar analysis check; encoded responses are coded by construction; coefficient inversion commutes with aggregation and truncation; zero padding commutes with honest aggregation | `structured`, `aggregate`, and `encode_responses` semantic layout | Inverse is information-theoretic; native NTT and Rust refinement remain open |
| `MatrixResponse` | Query-independent source extraction truncates to original message coordinates; structured response recovery equals ordered left aggregation; finishing equals matrix evaluation; honest encoded tables recover exactly | Native channel/left/right roles and padding | Flat index/fold adapter is supplied below; native NTT and Rust memory refinement remain open |
| `MatrixOpeningSecurity` / `MatrixOpeningCompleteness` | Fixed-word soundness takes native base-field response arrays and coordinate checks; honest semantic responses always pass checks and finish correctly; extraction returns the original honest table under the unique-decoding margin | Native semantic matrix opening | Explicit fresh interactive coins; flat fold semantics are supplied below; Merkle/XOF, native fields, NTT, and Rust/byte refinements remain open |
| `FlatMatrixFold` / `MatrixQuerySplit` | Cube/flat bijection puts the first bit low; every fold reads 2*i and 2*i+1; complete folds equal ordered tensor evaluation; prefix/suffix addresses are left+2^left_vars*right; weight expansion multiplies later matrices on the left | `PackedTable::fold_in_place`, `matrix_weights`, and native aggregation split | Mathematical loop semantics; Rust in-place memory and machine-integer refinement remain open |
| `FlatOpeningSecurity` / `FlatOpeningCompleteness` | Opening bound compares the native suffix fold directly with the complete query on one extracted flat table; honest finishing and extraction preserve that same layout | Complete semantic flat matrix query | Interactive fixed available word; native field/NTT, authentication, transcript and Rust refinements remain open |
| `MerkleOracle` / `MerklePayload` | Unaddressed node model and whole-payload prefix resolver use one common input domain; overlapping role images, arbitrary queries and repeated log entries are allowed | Native shared hash interface | Native path and byte-framing adapters are supplied below; concrete column serialization and Rust refinement remain open |
| `MerkleAvailability` | One frozen total word per prefix cache/root; log presentation is irrelevant without collisions; later authenticated payload disagreement reduces to a prefix collision or a later hit on a fixed root-wide target list of at most 2*L-1 labels | VCVio deterministic extraction kernel extended to column payloads | Native path interpretation is supplied below; Native freeze-point selection and full-protocol linkage remain open; generic accumulated hash losses are supplied below |
| `MerkleAvailabilityProbability` | Exact first-hit event for one fresh cache update; uniform-answer availability hazard is at most (2*L-1)/card(Digest) | Fresh lazy-oracle response | One-step law only; no whole-execution or expected-work claim yet |
| `NativeMerklePath` / `NativeMerklePathM` | Native low-bit direction, fixed-index counter loop and bit-dropping recursion agree; reversing bottom-up siblings gives the typed perfect-tree proof; ordered oracle computations are equal | Native `MerkleTree::check` loop | Typed path length; machine-size bounds, raw vector validation and Rust memory refinement remain open |
| `NativeMerkleVerifier` | Whole-payload hash check and native sibling loop establish a leaf cache entry and authentication chain; accepted frozen-word disagreement exposes the same root-wide exceptions; checker uses at most height+1 oracle calls | Native column authentication | Common-domain oracle and serializer contract; placement in the adaptive full execution remains open |
| `MerkleBytes` | Native fixed-width digest concatenation is injective; leaf prefix preserves serializer injectivity; no artificial node tag or role separation | `hash_column` domain string and raw node bytes | Concrete field-column serializer injectivity and Rust/byte decoding refinement remain open |
| `MerklePayloadEvolution` / `MerklePayloadCheckpoints` | Cached repeats and answers outside reached-label targets preserve whole payload sources; VCVio checkpoint state records adaptive roots and preserves one source per root/configuration; whole suffixes can change sources only through fresh fixed-union target hits | Shared cumulative hash transcript | Generic execution below accumulates hash losses; native phase/checkpoint instantiation and physical cost coupling remain open |
| `MerkleCheckpointProbability` | Shared live target hazard is bounded by min(total checkpoint nodes, 2*cached keys + checkpoint count)/card(Digest); labels are deduplicated across roots | VCVio shared target union | One-step bound from the actual current log/cache-key cover; native full-history instantiation remains open |
| `ExpectedHazard` | State-dependent additive drift bounds terminal risk by initial risk plus expected accumulated charge, without a query budget; constant charged-query losses equal VCVio expected charged-query counts | Unrestricted accumulation foundation | Concrete fixed-checkpoint hash-handler instantiation is supplied below; full primitive composition and physical work coupling remain open; no final 128-bit theorem yet |
| `CachedHashHandler` | One canonical lazy-oracle step with passive ordered-log/key accounting; exact cache/log/key coherence holds for arbitrary adaptive hash programs; projection of every run is exactly VCVio's canonical oracle run | Shared cached hash execution | Hash-only core; private-sampling and checkpoint-recording interleaving are supplied by `CheckpointExecution`; native protocol phase placement remains open |
| `CachedHashCheckpoint` | Cached queries have zero stability loss; fresh queries pay the shared current-log/key-cover hazard; terminal instability of fixed recorded sources after an adaptive hash suffix is bounded by expected accumulated fresh-answer charges, without a query cutoff | Concrete handler instantiation of checkpoint hazards | Fixed checkpoint family during the suffix; adaptive recording and collision composition are supplied below; transcript compilation and physical-work coupling remain open |
| `CheckpointExecution` | Private computations, canonical shared hash calls and adaptively recorded roots interleave in one execution; a persistent monitor detects source instability and cannot be reset; its probability is bounded by the expected accumulated fresh-answer charge with no query cutoff; erasing bookkeeping exactly recovers the canonical execution | Concrete shared-log checkpoint execution | Shared-cache collision losses and root-wide payload availability are supplied below; native phase placement, transcript compilation and physical-work coupling remain open |
| `CachedHashCollision` | Fresh-answer collision hazard is at most cached keys/card(Digest); cached repeats have zero loss; the cache grows monotonically and preserves earlier collisions, with no finite-input-domain premise | Canonical shared cached hash; VCVio birthday counting | One-step law is composed below; physical-work coupling remains open |
| `CheckpointCollision` | One persistent event combines any source failure with any shared-cache collision; the expected accumulated union charge bounds its probability over arbitrary adaptive private/hash/root-recording interleavings | Same actual execution and cache as `CheckpointExecution` | No independence or query cap; native phase placement and physical-work accounting remain open |
| `CheckpointAvailability` | Every cached authenticated payload of every recorded root agrees with its immutable source unless the combined exception occurs; one unrestricted expected-charge bound covers all configurations, positions, paths and payloads | Root-wide mathematical oracle availability | Single-opening native verification linkage is supplied below; native phase placement, the column-verification loop, production XOF, field serializer and Rust refinement remain open |
| `NativeMerkleExecution` | Native verifier hashes route to the actual shared cached oracle; canonical-run projection and support inclusion establish the leaf entry and authentication chain from acceptance; later adaptive runs preserve both | Native whole-column and bottom-up sibling verifier inside the checkpoint execution | Typed paths; raw decoding, machine sizes and Rust execution refinement remain open |
| `NativeOpeningAvailability` | An arbitrary adaptive private/hash/checkpoint prefix chooses a typed opening; actual native accepted disagreement implies the root-wide availability event and inherits its expected-charge bound, counting the prefix and checker calls; total frozen-word disagreement is a subevent | Checked native single-opening game | Authentication component only; interleaved-column hashing is supplied below; phase placement, PCS coordinate/challenge/response composition, production XOF and physical work remain open |
| `CachedVerifierReplay` / `InterleavedMerkleWorker` | Successful final-cache reading reproduces native verifier acceptance and its leaf/path chain; operational workers may pause for arbitrary actual shared execution between primitive hash calls; completed workers replay from the final cache | Rayon column workers and the same canonical shared hash | Operational trace semantics; native Rayon/Rust refinement remains open; whole workers are not assumed atomic |
| `ParallelColumnAvailability` | One root-wide expected-charge bound covers any listed native column whose verifier accepts from the final cache; every completed interleaved worker satisfies that replay condition; no per-column union loss or early cancellation assumption | Native parallel column authentication | Global oracle program includes all actual calls; coordinate transport is supplied below; native scheduling refinement, transcript/phase placement and physical-work coupling remain open |
| `NativeColumnLayout` | Weight, payload and response addresses match native strides; literal row-product folds equal semantic combinations; sorted/deduplicated indices zipped to equally many proof columns cover every original draw; native Boolean acceptance is exactly both coordinate-check families | `matrix_weighted::verify` array indices and nested lane/coordinate checks | Packing and code-block widths remain separate; typed shapes and field operations, with Rust memory/field and NTT refinement open |
| `AuthenticatedColumnChecks` | Packed list payloads recover at each context's typed dimension; outside the joint availability event both native coordinate families imply `MatrixOpeningSecurity.Checks` on one immutable word in the equal-width default; coordinate transport failure has the same expected hash charge | Native column authentication connected to fixed-word PCS checks | No production coin law or final PCS soundness claim; commitment/challenge order, full probability composition, field/byte serializer and native NTT/Rust refinement remain open |
| `AdaptiveResponse` | A probabilistic response procedure depending on the earlier challenge cannot inflate an earlier-event probability; later failure composition adds one event without independence | Response/private-state probability interface | No losslessness, finite-response-space or fixed-random-tape premise; production transcript law remains open |
| `CommonSourceOpeningKernel` / `MatrixOpeningKernel` | Randomized adaptive responses and arbitrary retained state preserve the common-source near/far bound and its maximum of column losses; native padded responses supply code membership automatically and finish against one extracted table | Interactive stochastic-response PCS soundness | Fixed available word; shared-handler composition and adaptive commitment-prefix averaging are supplied below; production transcript freshness and physical-work coupling remain open |
| `PrivateSampling` / `CheckpointHistory` | Private subprograms keep their original law and carry one unchanged complete shared state; arbitrary later activity retains every earlier immutable root snapshot | Actual private/hash/checkpoint signature | Private ideal coins; production transcript freshness and Rust refinement remain open |
| `InteractiveSampling` / `SharedMatrixSampling` | Actual private test, shared-oracle response and private column draw have exactly the stochastic-response kernel law with the full response state retained; arbitrary later shared work preserves the earlier arithmetic bound | Same cached-hash execution used for authentication | No independent response law or discarded post-response work; production transcript and physical work remain open |
| `InteractiveAuthenticatedOpening` | From a recorded safe snapshot, typed native accepted wrong evaluations have probability at most the PCS arithmetic error plus the expected hash charge of the same complete adaptive response/column execution; one immutable source and one availability event suffice | Conditional private-coin interactive authenticated matrix opening | Empty-cache prefix composition is supplied below; production Fiat–Shamir, concrete 128-bit parameters, native NTT/byte/Rust refinement and physical-work coupling remain open |
| `CommitmentPrefix` / `CommittedMatrixOpening` | Arbitrary adaptive commitment work selects the root before the private test; retaining its actual snapshot only for analysis projects exactly to the original shared execution; averaging gives false-acceptance probability at most the PCS arithmetic error plus the expected hash charge of the entire run from empty initialization | Empty-cache private-coin authenticated matrix opening, including commitment work | No safe-prefix certificate or hash query cutoff; production Fiat–Shamir, native stage enforcement, concrete parameters, Rust/byte refinement and physical work remain open |
| `PackedSumcheckRound` | Interpolation of the 2*k Boolean/lane values gives the honest scalar round; adjacent-node checks equal the current hypercube sums; its values equal the next matrix-folded sums; degree is at most (2*k-1)*productDegree, with repeated factor indices allowed | `sumcheck/src/packed.rs::round_evaluations`, `challenge_pair`, `check_round` and `PackedTable::fold_in_place` | Typed field semantics; native optimized interpolation and forward-difference/Rust refinement remain open |
| `PackedSumcheckProbability` / `NativePackedInterpolation` | Distinct round polynomials agree at at most D field points; all k fresh lane challenges heal a false claim with probability at most (D/card(F))^k; consecutive nodes below the characteristic, interleaved addresses, literal Lagrange weights and received D+1-entry message checks provide the native degree bound automatically | One scalar packed round evaluated at independent lane challenges | Private uniform challenges; production transcript freshness and native field representation/refinement remain open |
| `PackedSumcheckExecution` | Arbitrary probabilistic messages and post-challenge callback state compose over n rounds to bound false-sum acceptance by n*(D/card(F))^k, with the same repeatedly folded factor sources and a truthful terminal factor obligation; native evaluation-vector messages instantiate the degree bound | Interactive packed sumcheck and its per-challenge callback schedule | Terminal authenticated-opening obligation, shared-oracle execution adapter, full stage relations, production Fiat–Shamir and Rust refinement remain open |
| `PackedZeroFirst` / `NativePackedZeroFirst` | Equality-weighted first polynomials have degree D and recover original constraint slices at all Boolean/lane nodes; zero relations satisfy the boundary; native Boolean checking of every row's first 2*k entries is exactly polynomial boundary checking; truthful mixing reduces to the folded expression times the mixed public EQ table; appending EQ gives `reduced_shape` | `packed_zero::{first_evaluations,check_first,reduce,mixed_equality,reduced_shape}` | Typed first-message and field semantics; native suffix layout and public-EQ terminal evaluation are supplied below; optimized interpolation/Rust refinement remains open |
| `PackedZeroEquality` / `PackedZeroMixing` | One fixed nonzero slice has a nonzero multilinear extension of total degree at most n; k independent equality points miss it with probability at most (n/card(F))^k; fresh row/challenge mixing hides a nonzero degree-D polynomial family with probability at most ((D+1)/card(F))^k, without assuming an invertible matrix | Equality-point and jointly sampled mixing/row-challenge phases | Private ideal coin geometry; shared-execution linkage is supplied below; production XOF law remains open |
| `PackedZeroReduction` | A false source relation yields a boundary-valid first message with a truthful reduced claim with probability at most (n/card(F))^k+((D+1)/card(F))^k; the first-message distribution may depend arbitrarily on earlier equality points; native D+1-entry vectors automatically supply degrees | Adaptive interactive special-first-round reduction | n is the suffix-variable count and D=(2*k-1)*productDegree; remaining-sumcheck composition and native suffix layout are supplied below; terminal authenticated sources and production Fiat–Shamir/Rust refinement remain open |
| `PackedEqualityCube` / `NativeEqualityTable` | Cube coordinates equal the Boolean suffix variables without permutation; native addresses are the little-endian bit sum; the typed two-block EQ-table construction equals the multilinear equality kernel in that order | `packed_zero::equality_table` and the first-bit-first factor fold | Typed fixed-size arrays; machine-index/allocation and Rust memory refinement remain open |
| `PackedPublicEquality` / `PackedZeroTerminal` | The verifier's ordered column recurrence equals folding the actual native constructed mixed EQ table, including zero rounds and noncommuting matrices; native Boolean terminal acceptance is exactly the reduced sum-of-products identity when original factor vectors are their true source folds | `evaluate_public_equality` and `ZeroSubclaim::check` | Original factor values still require cryptographic authentication; full transcript/shared-run and Rust refinement remain open |
| `PackedZeroCube` / `PackedZeroExecution` | Reindexing the special first round retains the original factor sources and point coordinates; its truthful reduced claim is the sum on the once-folded factors plus the mixed public EQ source; composing the remaining n rounds gives the private-coin bound (n/q)^k+(((2*k-1)*d+1)/q)^k+n*(((2*k-1)*(d+1))/q)^k for a false relation on n+1 variables | Composed interactive packed ZeroCheck soundness against truthful terminal factors; q=card(F) and d bounds original product arities | Native evaluation vectors supply both degree bounds; shared authenticated ZeroCheck is supplied below; production Fiat–Shamir and Rust refinement remain open; honest-run completeness is supplied below |
| `PackedHonestMessages` | Sampling a polynomial of degree at most D at the native D+1 nodes and applying the soundness message interpreter recovers that exact polynomial, including zero and maximum-degree messages | Honest evaluation-vector encoding | Node injectivity follows from the checked characteristic bound; optimized interpolation/forward-difference and Rust refinement remain open |
| `PackedSumcheckCompleteness` / `PackedZeroCompleteness` | Concrete honest states store and fold the same source tables as the verifiers; every supported existing sumcheck/ZeroCheck execution accepts truthful sums or valid zero relations, hence acceptance probability is one; native codecs are proved and literal adjacent-entry/first-boundary checks always pass | The same `PackedSumcheckExecution.run` and `PackedZeroExecution.run` used by soundness | Truthful terminal factor obligation remains; cryptographic opening composition, production transcript, honest callback/optimized-prover linkage and Rust refinement remain open |
| `PackedSumcheckSubclaim` / `PackedSumcheckOracle` | A source-independent verifier returns an indexed ordered matrix query and expected terminal vector; list projection preserves low-bit source addresses; each message precedes its private lane draw; actual message and callback hash calls use one shared state, including rejection calls | Native packed-sumcheck subclaim and callback order over the cached private/hash/checkpoint signature | Typed oracle program; the shared-oracle ZeroCheck adapter is supplied below; production transcript and Rust refinement remain open |
| `SharedContinuation` / `PackedSumcheckSharedSoundness` | A false fixed source sum yields a truthful returned subclaim with probability at most n*(D/card(F))^k on the actual shared execution, for arbitrary adaptive message/callback programs; retaining that claim through arbitrary later opening work preserves the bound while all later calls remain in the complete program | Same cached hash, logs, checkpoints and prover state across sumcheck and continuation | Private ideal coins; no initial hash-safety or query-cutoff premise; production Fiat–Shamir and physical-cost coupling remain open |
| `PackedSumcheckTerminalOracle` | Operational terminal opening and Boolean expression checks use the returned subclaim without inspecting sources; false-sum acceptance is bounded by the arithmetic error plus the actual joint event that some supplied factor differs from its source query-fold, on this same complete execution; native evaluation vectors discharge message-degree bounds | Source-independent sumcheck followed by factor opening and terminal checking | The joint wrong-factor probability remains explicit and unbounded here; instantiate it with the cryptographic PCS opening theorem before claiming authenticated sumcheck security |
| `SubclaimSourceLayout` | A source fixed by the trusted front/suffix dimensions has the same query fold as the PCS two-half matrix evaluation for every subsequently returned sumcheck query; the native low-address front and later-left matrix order are preserved; the actual PCS decoder supplies this source without receiving the query | Sumcheck subclaim to single-factor PCS geometry, including empty halves | Deterministic bridge; the joint factor-opening event still needs cryptographic composition on the full stage execution |
| `AdaptiveMatrixOpening` / `SharedContinuation` / `StatefulCommitmentPrefix` | Arbitrary shared work selects a query after the root snapshot and before private matrix/column sampling, retaining arbitrary private commitment memory; only the root enters the checkpoint query; the conditional arithmetic bound averages over its real retained state; one expected hash charge covers commitment, query selection and complete authenticated opening from empty initialization | Single-factor private-coin opening after an adaptive sumcheck/query prefix | One source remains frozen before query selection; homogeneous multiple-factor composition is supplied below; heterogeneous layouts, actual stage orchestration, production Fiat–Shamir, physical-work coupling and Rust refinement remain open |
| `SharedSequence` / `JointMatrixOpening` | Sequential factor checks carry the actual private memory and shared cache; local arithmetic losses sum without independence; final-cache native coordinate/authentication checks reduce any accepted wrong factor to the arithmetic union or one root-wide disagreement | Sequential native factor loop with potentially interleaved column workers inside each opening | Homogeneous PCS layout and private ideal coins; incoming-root safety is removed by the prefix theorem below; operational terminal-value/ZeroCheck linkage is supplied below; Rust refinement remains open |
| `RecordRoots` / `MultiCommitmentPrefix` / `CommittedJointMatrixOpening` | An arbitrary shared commitment emits a family of roots and private memory; recording freezes every root at the real prefix log without hashing; arbitrary shared query selection precedes sequential openings; from empty initialization the joint loss is the sum of per-factor PCS arithmetic errors plus one expected hash charge for commitment, query selection and every opening | Multi-root private-coin joint authenticated opening with exact erasure of analysis snapshots | No safe-prefix certificate, assumed PCS security or query cutoff; concrete operational sumcheck/ZeroCheck adapters are supplied below; heterogeneous layouts, production Fiat–Shamir, physical-work coupling and Rust refinement remain open |
| `ShortCircuitSequence` | A failed step retains its result, private memory and actual final shared state, and skips the suffix at the oracle-program level; successful runs cover the trusted factor list and enforce every literal check; arithmetic errors still sum without independence | Native sequential early-return schedule | Generic operational loop; no padded later verifier coins or hash calls; native step/worker refinement remains separate |
| `StoppingJointMatrixOpening` / `CommittedStoppingMatrixOpening` | The joint PCS bound applies from empty initialization to a terminal-gated factor loop that stops on first failure; source-independent response checks add no oracle calls; one whole-run expected charge includes exactly the issued commitment/query/opening work | Private-coin joint opening with actual terminal disablement and factor early return | Homogeneous layout; worker flags are instantiated by the concrete pool below; terminal/ZeroCheck composition is supplied below; Fiat–Shamir and Rust/physical-cost refinement remain open |
| `GuardedSumcheckTerminal` | Values are checked before the binding callback and every factor opening; rejection keeps receive-work and private memory; accepted false sums imply the earlier arithmetic event or an accepted wrong supplied factor on this same guarded, short-circuit execution; native evaluation vectors supply degree bounds | Source-independent packed-sumcheck terminal schedule matching the native check-before-opening order | Preparation and concrete authenticated sumcheck composition are supplied below; authenticated ZeroCheck is supplied below; full-stage integration remains open; rejected wrong proposals are excluded from the event |
| `NativeFactorChecks` | Executable coverage, both coordinate families and the final claimed-value comparison are enforced literally; successful actual loops supply coverage and all response checks; with completed worker replay, a wrong supplied factor implies the joint PCS event for the same fixed decoded sources | Supplied terminal factor values to native PCS checking and common-source geometry | Replay is an operational interface now discharged by the concrete computed-flag pool below; full verifier orchestration remains open |
| `HashWorkerPool` | An executable scheduler advances one primitive worker hash at a time, with arbitrary shared work between advances; acceptance is computed from residual programs; original/residual equivalence holds in every larger cache and yields final-cache replay for every accepted worker | Non-atomic native column-worker execution on the canonical cached handler | Finite advances concern verifier-owned worker steps, not adversary hash calls; concrete honest completion bounds and Rayon/Rust refinement remain open |
| `NativeColumnWorkerPool` | Each actual worker hashes its whole column, verifies the bottom-up path and then checks both coordinate families; the computed pool flag entails all native replay and coordinate checks, retained through any later cache extension | Native column authentication/coordinate worker bodies, including independent packing and code-block widths | Cancellation retains issued work; no supplied worker flag or trace certificate; native scheduling completion, field/byte/Rust refinement and production transcript remain open |
| `NativeMatrixVerifier` | The column provider returns columns and private memory only; an actual worker pool computes acceptance; literal response/value checks gate sequential factors; successful loops carry every factor's authentication/checks to the final cache, and a wrong supplied value implies the joint PCS bad event | Concrete typed native opening steps and stopping factor loop | No caller-supplied replay premise; authenticated sumcheck/ZeroCheck composition is supplied below; full-stage orchestration, honest scheduling completion, production Fiat–Shamir and Rust refinement remain open |
| `NativeCommittedOpening` | Trusted public encoding/domain/roots/query override prover behavior; from empty initialization a successful concrete stopped opening loop with any wrong supplied value has probability at most the PCS arithmetic sum plus one expected hash charge for the actually executed commitment, query, scheduler and worker work | Concrete multi-root private-coin opening soundness against supplied factor values | No assumed PCS security, worker flag, replay certificate or adversary query cutoff; homogeneous PCS layout; authenticated sumcheck/ZeroCheck composition is supplied below; full-stage integration, Fiat–Shamir, honest scheduling completeness and physical/Rust refinement remain open |
| `PreparedTerminal` | Separating receive/check/bind work from the factor loop is an equality of oracle programs with the existing guarded terminal adapter; actual earlier subclaims and private memory are retained; enabled preparations prove the literal terminal identity; earlier truth events cannot gain probability | Guarded-terminal preparation for concrete native openings | Rejected query/value placeholders never enable opening; no padded calls or probability-only equivalence; shared ZeroCheck preparation remains separate |
| `AuthenticatedSumcheck` | One complete committed program runs packed sumcheck, guarded terminal preparation and concrete native interleaved openings; accepting a false sum on the prefix's fixed decoded sources has probability at most n*(D/card(F))^b + the PCS arithmetic sum + one expected hash charge for that exact run; native evaluation-vector messages supply nodes/interpreter and degree automatically | Authenticated private-coin packed sumcheck, including source geometry, terminal values, first-failure stopping and computed worker flags | No residual wrong-opening event, false-prefix certificate, replay/PCS certificate or query cutoff; homogeneous PCS layout; authenticated ZeroCheck is supplied below; full PBS stages, honest scheduling completeness, Fiat–Shamir and Rust/work refinement remain open |
| `IndexedPublicEquality` / `PackedZeroOracle` | Source-independent ZeroCheck samples points, receives an adaptive first message, rejects its boundary before mixing/callbacks, and returns the full original-factor query plus the computed public EQ terminal; indexed EQ evaluation equals the ordered mixed-source fold; a checked terminal is truthful or supplies a wrong original-factor value | Shared private-coin ZeroCheck, including first-message and ordinary-round hash work | Native static preflight occurs before transcript-derived points, whereas the interactive first message may depend on sampled points; Fiat–Shamir/Rust refinement must connect those interfaces; no extra EQ commitment is introduced |
| `PackedZeroSharedSoundness` | On the actual shared handler, a false zero relation on n+1 variables returns a truthful subclaim with probability at most (n/q)^b+(((2*b-1)*d+1)/q)^b+n*(((2*b-1)*(d+1))/q)^b; native evaluation vectors provide both degree bounds; arbitrary later work retains the bound and actual state | Shared-execution arithmetic soundness of the special first round and remaining packed rounds | Fixed original sources; concrete committed native openings, full stage composition, production Fiat–Shamir and Rust/work refinement remain open |
| `PreparedZeroTerminal` | Receives and binds only original-factor values, checks the computed public EQ identity before binding, preserves received memory on rejection and retains the earlier ZeroCheck subclaim; enabled supported packets contain the actual checked subclaim; terminal truth or a wrong original factor follows | Shared ZeroCheck terminal preparation for concrete openings | Concrete composition with fixed decoded sources and the native stopped opening loop is supplied below |
| `QueryReindex` / `AuthenticatedZeroCheck` | Trusted dimension equality transports the full query and fixed decoded source together, preserving evaluation and matrix order; one complete committed shared execution checks the computed public EQ terminal and opens only original factors; false zero-relation acceptance is bounded by the three ZeroCheck terms, PCS arithmetic sum and one whole-run expected hash charge; native vectors discharge both degree bounds; erasing the analysis prefix recovers the actual program exactly | Authenticated private-coin ZeroCheck with concrete interleaved native workers and first-failure stopping | No residual wrong-opening event, EQ commitment, false-prefix certificate, replay certificate or query cutoff; homogeneous PCS layouts; complete PBS stage orchestration, native honest scheduling, production Fiat–Shamir and Rust/physical-work refinement remain open |
| `PBSHadamard` | Fixes the canonical complete-PBS relation sum_i evaluation[i]*key[i]-output, degree two, coefficient signs and native evaluation/key/output factor order; typed roles biject with the 2*count+1 native slots; the zero relation is exactly the pointwise sum-of-products identity; authenticating this trusted stage has the specialized three ZeroCheck terms plus PCS arithmetic sum and one full-run expected hash charge | `packed_pbs/canonical.rs::{shape,verify_inner}` Hadamard relation with count=2*d | This is the committed evaluation-domain relation; public-key preprocessing/root binding, NTT equivalence, other PBS stages, sequential stage composition, Fiat–Shamir and Rust refinement remain open |
| `NTTRowCheck` | Tensor-folded rows commute with a trusted linear transform; a fixed false block relation passes k independent Boolean-MLE row points with probability at most (r/card(F))^k, including repeated points and r=0; passing proposed-row checks implies that miss event or a wrong coefficient/evaluation row; polynomial evaluation at ordered nodes is a concrete linear map | `packed_ntt::{tensor,fold_rows,check_folded}` algebra and row-detection phase | Compression/authentication and exact-field bit-reversed butterflies are supplied below; retained native roots, optimized integer kernels and Rust refinement remain open |
| `NTTRowOracle` | Actual private row sampling, adaptive row reception, shared binding-before-check, computed transform flag and private memory retention; the row-miss bound survives arbitrary actual proposer/binder/later work; accepted local prefixes reduce to row miss or the exact accepted wrong-row event | Native NTT prefix through `check_folded`; bind calls remain even after local rejection | The accepted wrong-row event is deliberately still explicit; later independent compression and concrete batch openings must bound it; native preflight/Fiat–Shamir and Rust refinement remain open |
| `NTTSourceQuery` | Appending scalar identity row matrices after arbitrary coefficient-compression matrices evaluates the original source exactly as compressing its tensor-folded polynomial; native address is coefficient+2^c*row; ordered lists and noncommuting prefix matrices are preserved | `packed_ntt::{source_query,compressed_value}`, without committing an intermediate folded view | Deterministic geometry; probabilistic compression detection, concrete PCS batch/source decoder linkage, native NTT and Rust refinement remain open |
| `MatrixCompression` / `GuardedCompression` | One nonzero table survives c sequential fresh native matrix folds except with loss c*((2*b-1)/card(F))^b; all fixed coefficient/evaluation rows may share that query without a family-size union loss; arbitrary adaptive earlier shared work fixes the family and rejected prefixes skip all compression draws/callbacks | `packed_ntt::coefficient_query` and fresh private-coin matrix compression; also the detection core needed by packed linear identities | Fresh private coins only; production transcript, concrete batch authentication and Rust refinement remain open |
| `NTTCompression` | Checked adaptive rows, binding-before-check and one gated fresh compression query compose on the actual shared handler; truthful computed terminal values at the exact original-source queries for a false transform relation occur with probability at most (r/card(F))^k+c*((2*b-1)/card(F))^b; all row/side queries share the same compression | NTT arithmetic stage through its original-source terminal obligations; native repetition count is k=b | The polynomial-row residual is discharged up to compression error; terminal authentication and exact-field butterflies/order are supplied below; retained native roots, optimized kernels, full stage orchestration, Fiat–Shamir and Rust refinement remain open |
| `BatchMatrixSampling` | All fixed query/value claims share one actual uniform random test, arbitrary shared response work and one later column draw; selecting one false pre-test value bounds the entire accepted batch arithmetic event by one PCS error, with no query-count factor; later actual worker work retains that bound | Brakedown `matrix_weighted::verify_many` arithmetic under shared sampling | Fixed source word and trusted query/value family; native grouped finish checks and committed batch composition are supplied below; NTT linkage remains open |
| `BatchGrouping` / `BatchQueryLayout` | Stable first-match grouping computes representative keys and typed group indices; every group reads back its original key; group equality iff raw ordered left-prefix equality; representatives recover first original source positions; the selected representative has exactly the query's trusted left weights | Native `query_groups` with actual matrix-prefix keys, not just equal aggregate weights | Key-level deterministic semantics; native vector/index storage, field equality/Rust refinement and full batch-check orchestration remain open |
| `BatchColumnChecks` / `NativeBatchColumnWorkerPool` | One native Merkle authentication per column precedes one random-test check and all grouped response checks; actual cooperative hash-step workers compute acceptance, replay on the final cache and preserve calls through cancellation/later work; empty groups retain the test obligation | Native shared-column batch authentication and nested coordinate loop | No caller-supplied worker flag or per-group reauthentication; coverage/grouped finishes and committed PCS/availability composition are supplied below; NTT terminal linkage, honest scheduling and Rust refinement remain open |
| `NativeBatchChecks` / `NativeBatchVerifier` | Computes exact nonempty sorted/deduplicated column attachment before worker hashes; checks coverage, every grouped coordinate and every original query's suffix finish, including nonrepresentatives; a per-root shared binding prelude precedes its fresh test; successful actual steps supply final-cache replay and reduce wrong supplied values to batch arithmetic or one availability disagreement | Typed native `verify_many`, including per-root bind-before-test and early invalid-column rejection | Concrete homogeneous PCS layout; from-empty multi-root composition is supplied below; raw preflight, native NTT/field/encoding and Rust/scheduling refinement remain open |
| `CommittedBatchOpening` | Freezes all roots at the actual commitment prefix, performs adaptive query selection, then enabled native batches with first-failure stopping; false accepted supplied values are bounded by the sum of one PCS error per listed root batch plus one expected hash charge for the exact whole execution; erasing analysis snapshots recovers the actual program | Complete private-coin multi-root batch opening from empty initialization, with computed grouping/worker/finish checks and root-specific preludes | No residual wrong-opening event, per-query multiplier, safety/replay/PCS certificate or query cutoff; NTT factory claim protection is supplied below; concrete fields/NTT, full PBS stages, Fiat–Shamir and Rust/physical-work refinement remain open |
| `AuthenticatedNTT` | Runs actual adaptive row reception/binding, computed local transform checks and one gated fresh compression, then two stopped native batches; trusted computed queries/values override factory claims; a false prefix-frozen decoded-source transform relation is accepted with probability at most (r/card(F))^k+c*((2*b-1)/card(F))^b+2*PCSerror+one whole-run expected hash charge; projection erases the analysis prefix exactly | Shared private-coin NTT relation against its two original commitments, with native batch grouping/coverage/finish/worker enforcement | Public linear-transform semantics and homogeneous PCS layout; no truthful-terminal or wrong-opening residual, per-repetition multiplier, safe-prefix/replay certificate or adversary query budget; exact-field butterflies/order are supplied below; retained native roots, optimized kernels, field representation, remaining PBS stages, honest scheduling, Fiat–Shamir and Rust/work refinement remain open |
| `NTTButterfly` | Recursive field butterflies read coefficient halves and emit contiguous output halves; correctness is proved by polynomial half-splitting at each branch; the output-address/exponent permutation is explicit bit reversal; primitive psi of order 2*N yields evaluation at psi^(2*reverse(i)+1), distinct nodes and node^N=-1 | Exact field radix-two negacyclic NTT, with native output ordering | Primitive-root premise is explicit; no transform-correctness certificate; native retained-root validation, breadth-first/optimized concrete-ntt kernels, lazy integer residues and Rust/word/memory refinement remain open |
| `PackedNTT` | Polynomial addresses are lane+b*coefficientBlock; flatten/unflatten are inverse; butterflies equal a concrete public linear map; literal pair checks agree; the authenticated scheme overrides any factory transform and runs the actual field butterflies; from-empty soundness applies to false butterfly relations on the same frozen sources with unchanged row/compression/PCS/hash losses | Canonical packed NTT relation and source packing, specialized beyond an abstract supplied linear transform | Packing size 2^c*b=2^n is separate from PCS code-block width; primitive-root and PCS parameter conditions remain explicit; native roots/optimized kernel/field/Rust refinement and full PBS orchestration remain open |
| `NTTBlockEncoder` | Initializing an N-element zero buffer and copying m<=N coefficients preserves each lane's polynomial; transforming all lane buffers and interleaving outputs equals `BlockEncoder.encode` on the injective native-order domain, hence lands in the actual PCS distance code | `pcs::utils::code::block::encode_row` exact-field gather/zero-pad/transform/scatter layout | Concrete native retained roots, canonical/lazy integer representations, zero shortcut implementation and optimized Rust/concrete-ntt refinement remain open |
| `NTTRootCheck` | In odd characteristic, root^(2^n)=-1 is equivalent to primitive order 2^(n+1); the literal native nonzero/half-power Boolean check is exactly that condition | Goldilocks/BabyBear `is_primitive_root` helper for public power-of-two degree >1 | Odd characteristic is necessary; default concrete-ntt instead constructs roots through modular square roots; its Tonelli–Shanks/integer/plan/cache refinement remains open |
| `NativeFields` | Lucas certificates with complete factorizations of p-1 prove Goldilocks p=18446744069414584321 and BabyBear p=2013265921 prime; exports actual fields, cardinalities and oddness; fast modular exponentiation certificates check top/main root arithmetic | Native field moduli and mathematical scalar domains | Kernel-checked arithmetic, no assumed primality; native Goldilocks lazy residues and BabyBear Montgomery representation/serialization/Rust refinement remain open |
| `NativeNTTRoots` | Checked top roots have orders 2^32/2^27; powering supplies every admissible mathematical N=2^logSize domain (logSize<=31/26); main roots 455906449640507599/812423803 have order 2048 and pass the actual typed root check; concrete N=1024 schemes force widths/repetitions 4/8 and c=8/7 | Mathematical root towers and the main canonical packed NTT profiles; main literal residues match an existing native-plan probe | No caller-supplied root certificate for the main schemes; arithmetic certificates do not prove native Tonelli–Shanks, plan/cache return values, optimized kernels, field representation or Rust equivalence |
| `NativeNTTSecurity` | Concrete Goldilocks/BabyBear from-empty NTT soundness has arithmetic terms (r/p)^4+8*(7/p)^4 or (r/p)^8+7*(15/p)^8, respectively, plus two PCS errors and one expected hash charge for the exact complete execution; checked fields, roots, dimensions and field-butterfly transforms supply those conditions internally | N=1024, k=b main profile NTT relations on prefix-frozen decoded original sources | PCS extension/basis and code parameters remain explicit; no primality/root/transform/terminal-safety certificate or adversary query cutoff; native construction/cache/kernel/Rust refinement, remaining PBS stages, honest scheduling, Fiat–Shamir and total 128-bit work theorem remain open |
| `PCSAnalysisField` | Constructs `GaloisField p b`, its finite alphabet, a fixed Fin-b basis over ZMod p and auxiliary uniform sampler; positive degree gives dimension b and cardinality p^b; presets supply Goldilocks p^4 and BabyBear p^8 alphabets/bases | The field alphabet needed by AHIV22 row-span analysis and symbol lifting | Analysis-only construction; no protocol calls/coins are added; lookup degrees 3/6 stay separate; base-modulus primality comes from checked native field certificates |
| `PCSParameters` | Both lifted scalar RS and base block RS distances equal delta=L-m+1 with Nat truncation for positive message/symbol widths; the exact PCS loss is delta/q^b plus max(((L-(delta-radius))/L)^Q,((L-(radius+1))/L)^Q); finite-real coercion preserves every term when q is nonzero and proves the arithmetic loss finite | Explicit algebra-free PCS arithmetic parameters for actual shared-test/shared-column openings | Positive-width conditions are essential for distance; nonzero q is essential for finite-real conversion; Q is the public ordered sampling quota, not an adversary work limit; numeric 128-bit parameter certification remains open |
| `ConcreteNTTSecurity` | Constructs the degree-4/8 PCS alphabets/bases internally and expands code distances and all arithmetic losses in the concrete main NTT bounds; the same from-empty verifier program pays NTT arithmetic plus twice the explicit PCS error and one whole-run hash charge | Concrete N=1024 Goldilocks/BabyBear NTT statements with numeric layout/code/radius conditions | No extension/basis, root, transform, decoded-terminal safety or query-budget certificate; m<=L, source capacity, radius<delta/3 and fresh private coins remain explicit; native Rust refinement, remaining PBS stages, honest scheduling, Fiat–Shamir and total 128-bit work theorem remain open |
| `SingletonOpening` | One-claim batch grouping has exactly one representative; constant structured coordinate checks, actual worker programs, pool programs and full opening transitions equal the typed single-opening path; retains per-root prepare before test and exact sampled-column attachment before workers | Typed native single-opening execution through the proved one-claim batch arithmetic/availability interface | Equality of oracle computations includes rejected paths and hashes; raw proof-shape preflight, backend normalization, integer/byte/Rayon/Rust refinement and physical work coupling remain open |
| `PackedLinear` | Ordered scalar/source lists preserve native left-to-right residual accumulation; matrix folding preserves linear combinations even with noncommuting matrices; checked truthful values imply compressed residual zero; one false fixed relation in a whole family survives the shared query with probability at most n*((2*b-1)/card(F))^b | `packed_linear::{Relation,check,query}` field algebra and common-query detection | Typed factor indices and trusted coefficients; repeated indices and zero coefficients are supported; source authentication supplied below; concrete PBS coefficient/role instantiations remain open |
| `PackedLinearOracle` | Enabled trusted shapes bind relation context before one fresh common query, receive values/memory, then compute the local check; disabled shapes skip bind/coins/receive; arbitrary shared before/receive work retains the truthful-value bound for false fixed sources | Interactive ordered linear-stage prefix; no extra all-values binding before the native local check | Private verifier coins; no source tables are inspected operationally; original-source authentication supplied below; production transcript and Rust refinement remain open |
| `AuthenticatedLinear` | Trusted preflight rejects empty source/relation/term families and insufficient field size before relation binding; checked query/values/root/code context override the factory; original sources open in native index order via proved single transitions; false prefix-frozen decoded linear relations are bounded from empty by one compression term, PCS sum over sources and one complete-run expected hash charge; native consecutive-node specialization and witness erasure are proved | Complete shared private-coin canonical packed-linear stage with computed local/opening flags and first-failure stopping | No relation-count error multiplier, terminal-truthfulness, worker flag, replay, root-safety, PCS-security or query-cutoff premise; homogeneous typed layout; raw counts/dimensions/normalization, native field/byte/Rust/scheduling, canonical PBS relation instances and whole-stage composition remain open |
| `ConcreteLinearSecurity` | Constructs the degree-b analysis field/basis for prime p and proves the native-node linear-stage bound n*((2*b-1)/p)^b+count*PCSerror(p,b,L,m,Q,radius)+one whole-run hash charge with explicit numeric distance/radius conditions | Concrete-field common-query linear stage, directly applicable to checked Goldilocks/BabyBear moduli | Public interpolation/code/layout conditions and fresh private coins remain; no supplied auxiliary field/basis or opening-security certificate; complete 128-bit parameter certification, native/Rust refinement, remaining PBS stages and Fiat–Shamir remain open |
| `DecompositionLinear` | Fixes source slot 0, digit slots i+1 and borrow slots d+1+i; all 2*d+2 slots have a semantic role; three native ordered relations are equivalent to input=sum radix^i*digit_i and zero borrow endpoints; honest local completeness and trusted preflight hold; concrete from-empty soundness has one compression term, (2*d+2)*PCSerror and one full-program hash charge | `packed_decomposition::relations` and canonical/shared linear substage with original registry order | Field reconstruction only; semantic canonicity given lookup membership is supplied below; digit-range/borrow-transition verifier enforcement, checked configuration/normalization, raw/native/Rust refinement and whole-PBS/transcript composition remain open |
| `RadixCanonicity` | Literal ordered field-valued comparison-table membership gives bounded digits, borrow bits and computed transitions; weighted inequalities telescope to an integer bound below p; modulus-digit expansion and canonical digit count supply the width bound; linear reconstruction plus table membership identifies the full integer and each quotient/remainder digit with the input's canonical representative; a noncanonical active position violates the linear relation or a concrete lookup row | `packed_decomposition::{comparison_table,modulus_digit,num_digits,relations}` semantic bridge at each active scalar position, with no lookup requirement on padding | No assumed lookup-security certificate or discarded lookup loss; arithmetic witness construction supplied below; actual lookup verifier enforcement, honest cryptographic completion, checked native count/radix/normalization and integer/Rust/PBS/transcript refinement remain open |
| `RadixWitness` | Executes the low-to-high borrow recurrence and proves its final bit zero iff bounded digits plus the incoming bit are at most the public bound; computed bits and transitions give literal table memberships; canonical digits construct all 2*d+2 native registry columns, preserve the original input and zero padding, satisfy the linear relation and every public comparison membership, and pass every local linear query; witness existence is specialized to the canonical count | Arithmetic honest-witness counterpart of `packed_decomposition::prove_impl` and `packed_decomposition::canonical::borrow_tables` used by canonical shared decomposition, including zero-initialized padding borrows | No supplied digit/table/endpoint completeness certificate; honest cryptographic commitments/openings, scheduler completion, native integer/field/normalization/Rust refinement, lookup security and full-PBS/transcript/128-bit composition remain open |
| `TupleHash` | Native iterative powers, ordered zip and scalar fold equal polynomial evaluation; hashing is base-field linear; distinct base tuples give distinct extension-field polynomials of degree <=width-1; one fixed nonmember's public-table collision has loss tableSize*(width-1)/card(K); one bad fixed source controls the whole shared-source miss event without a source-count factor; ordered lists may contain duplicates | Scalar tuple compression in `packed_tuple_lookup::challenges` and `packed_extension_lookup::challenges`, with the actual hash field K | Fresh private scalar challenge and fixed pre-challenge sources/table; no coordinate-wise repetition amplification; reciprocal detection, independent-pair repetition, actual lookup acceptance/authentication, native extension-field/normalization/Rust and Fiat–Shamir refinement remain open |
| `RadixTupleHash` | Literal comparison table is the ordered product of digit and incoming-bit ranges, has length 2*radix and distinct rows under radix<p; tuple hash collision and fixed-family miss bounds specialize to (2*radix)*2/card(K) | Native radix comparison triples, retaining the public table union and the full hash-field cardinality | Hashing component only; lookup hash field cardinality must not be replaced with PCS analysis-alphabet cardinality; actual native lookup extension fields and reciprocal/lookup/PBS composition remain open |
| `TupleHashOracle` | One private scalar sample is routed through the actual shared cached handler; arbitrary preparation and later adaptive work retain the fixed-source/table family miss bound and all issued calls, including rejecting continuations | Interactive hash-challenge fragment on the same shared checkpoint execution | Sources/table are fixed before preparation/sampling; no source inspection operationally, acceptance/security certificate, query cutoff or FS freshness premise is supplied; reciprocal/algebraic/authenticated lookup execution and production transcript refinement remain open |
| `ReciprocalPolynomial` | Products retain repeated active source rows; the native r+hash denominator clears to S'*T-S*Q of degree <=L+T-1; reciprocal helper identities force nonzero source denominators and the correct inverses; matching helper/table sums imply a numerator root; a missing hashed row gives positive root multiplicity <=L<p, proving the numerator nonzero for arbitrary public multiplicities | Native active-row reciprocal sum identity in base/extension lookup, with the actual field characteristic p | L is the public active source count, not an adversary query cap; no nonzero-polynomial/multiplicity certificate is supplied; hash-collision composition, authenticated sum/identity enforcement, native field/Rust/transcript refinement remain open |
| `ReciprocalMask` | Exact residual r*h+mask*g*h-mask forces active inverses and zero inactive helpers when r!=0; honest active/inactive values satisfy it; the full helper sum equals the active-prefix reciprocal sum and implies the same numerator root, with no zero-padding premise on original sources | `packed_extension_lookup::{identity_polynomial,check_terminal}` and canonical shared identity polynomial, interpreted at Boolean positions | Public active-prefix mask; EQ/ZeroCheck enforcement, native extension-query/layout/field/Rust refinement and actual authenticated lookup composition remain open |
| `ReciprocalDetection` | Excludes zero and negative public hashes, proving accepted-domain card >=card(K)-T-1 even with repeated/overlapping poles; a strict public size guard gives nonempty domain and total ideal sampling; passing reciprocal helper/sum constraints has probability <=(L+T-1)/(card(K)-T-1) for a missing hashed source with L<p | Ideal private uniform law on the native accepted reciprocal challenge domain; source/table/multiplicities fixed before r | Empty ideal domains fail; this does not prove the native rejection loop, transcript freshness or its issued-work accounting; ideal pair composition/repetition supplied below; actual lookup checks/PCS authentication, native/Rust/FS and total 128-bit composition remain open |
| `TupleLookupPair` | Samples a fresh y then an accepted-domain r for that hashed table; one fixed nonmember gives combined loss T*(width-1)/card(K)+(L+T-1)/(card(K)-T-1) for L below the characteristic; fixed sources/table/multiplicities across fresh repetitions give the exact all-pass product law and the combined-error power bound; public domain size proves totality of single/repeated ideal sampling | Private-coin arithmetic hash/reciprocal challenge loop in `packed_extension_lookup::challenges`, with repetition count separate from packing width | No supplied hash/reciprocal soundness or independence certificate; native rejection-loop/field/transcript/work refinement, actual sumcheck/ZeroCheck/PCS acceptance enforcement and complete lookup/PBS composition remain open |
| `TupleLookupPairOracle` | Actual private routing of the complete ideal pair sampler through the shared handler retains the repeated bound through arbitrary preparation and later adaptive work, including rejection; no issued calls are removed; the event is semantic all-pair reciprocal consistency | Challenge-prefix arithmetic retained through the same cached checkpoint execution, before helper commitments/openings | Original tuples and multiplicities precede all ideal draws; actual lookup acceptance still must imply the semantic event outside sumcheck/ZeroCheck/PCS/hash-availability errors; native rejection-loop/FS/work and full-PBS refinement remain open |
| `PaddedExtension` | Basis encoding E appends zeros, decoding D ignores padding, D*E=id and E*D is a projection; native multiplication columns implement E*(a·)*D on arbitrary vectors; successful element decoding iff the vector is the exact encoding | `packed_extension::{vector,element,multiplication}` generic field semantics | Basis and packing dimensions stay separate; concrete native polynomial-basis/extension-field, coefficient normalization, machine dimensions and Rust/byte refinement remain open |
| `ExtensionQuery` | Coefficient and scalar queries evaluate the ordinary extension tensor MLE through original base vectors; empty coefficient queries post-project; empty scalar queries post-map lanes; nonempty scalar queries put the lane map on the right of the first pair; false decoded extension claims imply false original base query-fold claims | `packed_extension::{coefficients_query,scalar_query}` with ordered Boolean coordinates, native lane address equivalence and optional post-matrix | No committed-zero helper-padding premise or extension-field PCS certificate; integer bit-loop/Rust correspondence, native field certificate and actual lookup-stage composition remain open |
| `ExtensionSourceOpening` | Incorrect decoded extension terminals imply the existing base-field PCS matrix-response incorrect-evaluation event for its query-independent common-source decoder, same available word and original source layout; coefficient and scalar cases specialize this transfer | Extension terminal to `SubclaimSourceLayout` and `MatrixResponse.finishMessage` | Deterministic adapter only; the actual lookup verifier must still enforce these queries/terminals and compose its sumcheck/ZeroCheck/PCS events on one complete shared execution |
| `NativePrefixMask` | High-to-low same/out loop equals the MLE of the exact active-prefix table; the full-table shortcut, zero prefix, Boolean interpolation and original low-bit addresses are proved | `packed_extension_lookup::prefix`, with canonical bit-coordinate threshold | Exact field/address semantics; equivalence to Rust shifts/word sizes and field representations remains open |
| `ExtensionLookupIdentity` | Tuple hashing commutes with scalar MLE; verifier-computed EQ and prefix factors give the literal masked terminal; partial/full product grammars have arities at most 4/3 and corresponding checked round degrees; the full affine g+r factor commutes with folding; a fixed nonzero masked identity survives fresh EQ with probability at most n/card(K) | `packed_extension_lookup::{identity_polynomial,equality,prefix,check_terminal}` and its full/partial branches | Separate MLE factors are retained off the cube; helpers must precede EQ sampling; complete scalar sumcheck execution/authentication/transcript composition remains open |
| `LookupReciprocalEnforcement` | Truthful full helper sum and all masked Boolean identities force the active-source reciprocal event, even with arbitrary original padding; a nonpassing pair forces a false sum or nonzero identity; with truthful sum its fresh EQ reduction passes with probability at most n/card(K) | Helper-root arithmetic to the earlier hash/reciprocal-pair semantic event | r must be nonzero, as ensured by the accepted-domain sampler; no cryptographic acceptance flag or sumcheck security certificate is supplied; full shared execution and PCS error composition remain open |
| `ExtensionLookupTerminal` | Full point splits into low lane/high row coordinates; successful decoding and literal terminal equality imply the truthful factor expression or a false original source/helper base-field query fold; the tensor source interpretation preserves distinct tuple count, packing width and lookup degree | Native terminal values through scalar source and coefficient helper queries | Deterministic acceptance adapter; exact source flattening is supplied below; concrete native field/Rust refinement and complete sumcheck/batched-PCS execution composition remain open |
| `LookupSourceFlattening` | Splits low-lane/high-row Boolean coordinates and tensor weights; exact scalar addresses are lane+width*row; flattening recovers every original entry and is injective; native scalar-query values equal full scalar MLEs; tuple compression and both terminal identity grammars use these same sources | Original packed source arrays to `packed_extension_lookup` scalar hash/identity tables, including zero dimensions | No new view commitment; machine/Rust field/index refinement and scalar sumcheck/shared grouped-PCS composition remain open |
| `ScalarSumcheckQuery` | Native width-one Boolean-node Lagrange weights are 1-x and x; point extraction and ordinary low-coordinate-first scalar MLE folding agree, including zero rounds; scalar Truthful is exactly the MLE factor expression | Ordinary extension-field sumcheck inside the existing packed verifier at width one | Arbitrary 1x1 queries need not be scalar; the operational query-form invariant is supplied below; native field/transcript/Rust refinement remains open |
| `ScalarSumcheckOracle` | Every supported result of the actual shared width-one verifier has scalar query form; no certificate is supplied; ordinary MLE terminal truth inherits n*D/card(K), native D+1 message arrays supply degree bounds, and later shared work retains the event and all issued calls | Existing `PackedSumcheckOracle.program` and handler, with native Boolean nodes 0/1 and adaptive message/callback programs | Private ideal coins and fixed analysis sources; full lookup helper/source opening and total error/work composition, rejection-sampling/FS and Rust refinement remain open |
| `LookupScalarSubclaim` | Helper-sum and partial/full identity MLE events equal the literal lookup terminal formulas over original flattened sources; successfully decoded/checking partial/full terminals expose that arithmetic event or a false original source/helper opening | Lookup native scalar subclaims to original base-field query obligations, with full degree-three affine branch retained | Deterministic local acceptance adapter; concrete complete lookup sequencing, grouped PCS authentication and one full shared bound remain open |
| `LookupPairSequence` | Validates the public-table sum claim, runs native scalar helper-sum checking, draws EQ only after success, and runs the identity verifier on the same state; the joint truthful event has a false-sum or EQ-plus-identity bound without independence | Native per-pair helper-sum/EQ/identity schedule and static message degrees, with adaptive shared callbacks and early return | Analysis factors never enter the operational verifier; concrete partial/full obstruction is supplied below; helper commitments, outer repetitions and PCS authentication remain to compose |
| `LookupPairArithmetic` | Computes the public total using tuple hashes and embedded base multiplicities; a nonpassing pair gives joint arithmetic loss n/card(K)+n*D/card(K), with D=4 partial or D=3 full; the false-helper-sum branch is separately bounded by n/card(K) and covered by this casewise bound | Native partial/full arithmetic sequence for fixed original sources and a helper fixed before verifier coins | No supplied EQ/sumcheck certificate; joint truthful subclaims are still an arithmetic event, not an authenticated acceptance flag; repetitions/root composition and native/FS refinement remain open |
| `LookupPairTerminal` | Ordered source decoding and literal computed terminal equality imply the joint arithmetic event or a wrong original sum-helper, identity-helper or scalar-source opening; encoded helper claims survive the zero-variable post-projection | Native `check_terminal` and the three exact original opening families for one pair | Pure typed check/obligation adapter; no caller flag or view root; actual grouped PCS authentication remains open |
| `PreparedLookupPair` | Source-independent execution receives claims after successful scalar stages, computes its own decoder/terminal flag, binds only on success, retains reception work on rejection and skips disabled work; every returned packet matches the actual earlier subclaims and checked values | Native check-before-append/bind order on the same shared state, retaining both raw stage result and prepared obligations | No source table or supplied acceptance flag operationally; grouped helper/source authentication, commitment prefix and outer repetition/error/work composition remain open |
| `PreparedLookupSoundness` | Every supported successful preparation yields the retained joint arithmetic event or an actual original-opening failure; the concrete partial/full probability bounds survive reception and binding | Actual callbacks and prepared-packet provenance on one shared state | Does not authenticate the returned values |
| `CompletedLookupPair`, `LookupCompletionSoundness` | Final acceptance is bounded by n/card(K)+n*D/card(K) plus final accepted wrong original openings on the same complete run, D=4 partial and D=3 full; disabled preparation skips later work | Actual source-independent preparation followed by arbitrary later verifier work, retaining shared state and earlier subclaims | Later verifier security is not assumed; actual grouped PCS must bound the explicit accepted-opening failure |
| `VariableHeightBatchVerifier` | Computed accepted native batch steps with wrong original values imply arithmetic error or one global availability disagreement, with context-indexed tree heights | Actual selected-root worker-pool replay on a state containing roots of different heights | Single selected root adapter, consumed by `HeterogeneousBatchOpening`; lookup-specific family instantiation and final composition remain open |
| `DependentShortCircuitSequence` | The trusted scheduled index supplies each dependent result's sigma tag; native result, private memory, flag and shared state are preserved; successful results retain their root's checks in the final cache | Passive result packing around the existing actual early-return loop | Does not assume or manufacture a successful step |
| `HeterogeneousBatchOpening` | Full native family bound from an actual recording prefix: sum of each root's own PCS arithmetic error plus one whole-execution expected availability charge; source words freeze before adaptive selection | Root-specific front/suffix, claim count, m, query count and context height; trusted encoding/domain/root override behavior factories; shared cache, private memory, disabled gates, rejection and actual interleaved worker calls retained | Common packing width and PCS analysis field; lookup-specific helper/source family instantiation, helper-prefix ordering, outer repetitions, Rust/Fiat–Shamir and final work composition remain open |
| `StagedCommitmentPrefix` | Two actual recording times erase to the same full shared execution; adaptive middle-phase work is retained; conditional arithmetic averages over both prefixes and availability is charged once | Source recording before arbitrary middle program, helper recording after it, then actual suffix | Generic two-stage interface; pair distribution and exact algebra are separate instantiations |
| `RecordedHeterogeneousBatchOpening` | Computed accepted wrong native batches reduce to arithmetic or global availability against immutable checkpoints with potentially different recording times; uniform per-root arithmetic bound is derived | Actual adaptive native heterogeneous continuation, with root identity and initial recorded membership as bookkeeping premises | Staged adapter derives those premises; no safety, replay or PCS security certificate is assumed |
| `StagedHeterogeneousBatchOpening` | Actual source/helper emissions assemble trusted roots, snapshots use each family's original log, native helpers open before sources, and total bound is per-root arithmetic sum plus one whole-run expected availability charge | Source roots before arbitrary pair/helper middle computation, helper roots before algebra/query selection, native heterogeneous short-circuit loop on one cache | Exact lookup queries/claims, private pair law and repetition, native rejection sampling, Rust/Fiat–Shamir, full PBS and final concrete expected-work composition remain open |
| `PackedQueryArity` | Trusted equal variable counts preserve ordered matrices and fold semantics under the same Boolean coordinates | Re-expresses a query using the original root's front/suffix sum | No coordinate permutation, lane padding or replacement source root |
| `LookupOpeningFamily` | Native helper roots have exactly [sum, identity] queries/encoded values; source roots have one scalar query/raw vector per repetition; any pair's three opening failures are exactly the family's native wrong-value event | Original-root per-layout dimension transport; behavior query/value fields are overwritten by trusted construction | Analysis tables are the root's own decoded words; no finished post-map value substitutes for a raw PCS source claim |
| `LookupGroupedOpening` | Final accepted sum-helper/identity-helper/scalar-source failure of any pair has the actual staged native PCS bound: per-root arithmetic sum plus one whole-run expected availability charge | Exact direct extension-lookup opening family; sources use pre-middle snapshots, helpers use later snapshots; arbitrary actual selector/provider/worker work retained | Lookup field K and PCS analysis field L have distinct bases; actual algebra/pair/repetition selector provenance, deferred/global PBS collection, Rust/Fiat–Shamir and final work theorem remain open |
| `ShortCircuitAccumulator` | Relates actual successful trace accumulation to returned private memory through each supported accepted step | Native early-return loop; rejection excluded only when proving consequences of overall success | Pure execution invariant, not an acceptance/security assumption |
| `RepeatedLookupSelector` | Canonical pair order, real early return, successful memory carry, trusted indexed packet slots and accepted packet provenance; a preselected pair's arithmetic event costs its one local error | Actual retained raw pair results on the same shared state; fallback projection never used in accepted slots | Rejected `none` exports no new private memory, so the halted slot retains its incoming memory; actual shared work is retained regardless |
| `RepeatedLookupCompletion` | A selected actual packet inherits arithmetic-or-wrong-opening provenance; final acceptance costs the selected scalar loss plus final accepted selected-packet opening failure on the same complete run | Whole-selector computed acceptance gates arbitrary actual later opening work; no callback security is assumed | The abstract local interfaces are instantiated by `RepeatedLookupAlgebra` |
| `RepeatedLookupAlgebra` | Native repeated helper-sum/EQ/identity/reception/binding with computed public totals; concrete partial/full selected-nonpassing-pair completion bounds n/q+n*D/q, D=4/3, with no repetition multiplier | Native prepared pair factory and arbitrary actual later shared work; all support, provenance and local arithmetic facts derived internally | Index, pairs, sources and selected helper fixed before algebra; staged PCS/private-pair-vector and false-statement composition still to combine; no end-to-end 128-bit theorem yet |
| `RepeatedLookupPCS` | Runtime fixes selector gate, successful opening memory and exact packet family; final acceptance reduces to selected scalar error, native PCS arithmetic or one global availability exception | Actual canonical selector then helper-first native grouped root loop; root/query/value bindings derived | Generic local scalar interfaces are proved by `RepeatedLookupPCSAlgebra` |
| `RepeatedLookupPCSAlgebra` | Both partial/full local support and probability facts follow from native prepared pair execution, with degrees 4/3 and one selected scalar loss | Public full-length condition explicit; no supplied EQ/sumcheck/packet/PCS certificate | Typed ideal-private-coin semantics; native transcript bindings/field/byte/Rust refinement remain separate |
| `StagedRepeatedLookup` | Complete typed two-prefix bound: final acceptance outside all-pairs-pass costs one scalar error + native per-root PCS sum + one expected availability charge; total acceptance adds the explicit all-pairs-pass probability | Original sources and multiplicities precede pair/helper work; actual selector memory/packets feed native PCS; nonpassing index chosen only from fixed prefixes | Actual private pair-vector law not assumed; its all-pairs-pass term remains explicit; native rejection/transcript/FS/Rust, honest completion, deferred/global PBS and final 128-bit work theorem open |







| `ApplicationKnowledge` | Given a correct public trace-producing evaluator, accepting extraction failure has exactly the same measure as accepting an incorrect output | `HasteBoots/docs/unmasked-polyfrim.md` | Native evaluator instantiation is supplied by NativePBS; Rust refinement and verifier enforcement remain open |

ArkLib is a pinned path dependency. Root dependency resolution must retain
`vendor/VCVio`, not materialize a second incompatible oracle framework.
`HasteBootsSmoke` checks unequal matrix splits, a noncommuting matrix example,
zero-round folding and a concrete block-distance specialization.

## Completion ledger

1. Dependency foundation and initial deterministic algebra: implemented and
   compiled. Native field instantiation and encoder/Rust representation refinement
   remain open.
2. Independent NAND/PBS trace relation and native evaluator: public preprocessing
   and binary blind rotation are now modeled independently. Blind-rotation trace
   generation, arithmetic validity, unique output, and zero-round identity are
   proved. One-block key switching, extraction and complete reference trace
   composition are now implemented. `NativePBS.exists_trace_iff` and the public
   extractor's exact failure-measure identity are checked. Native NTT/key-format
   representation linkage and proof-system stage enforcement remain open.
3. Common-source PCS security: deterministic unique common decoding, total fallback
   semantics, and false-response disagreement bounds are implemented. AHIV22's
   fixed-word uniform-row-span proximity bound is imported with guarded axiom
   checks. Full-width matrix-to-symbol and coefficient-to-row-span laws, including
   dependent source rows, now give the fixed-word matrix proximity bound.
   Exact base-code/field-code correspondence and preservation of whole-column
   common-source existence are now proved; the matrix proximity bound takes the
   base-layout far premise directly. Exact shared-column probabilities, adaptive
   coded responses, and structured common-source row combinations now give an
   interactive fixed-word opening bound: proximity loss plus the maximum of
   near/far column losses. Native semantic response assembly and matrix-query
   finishing now instantiate this bound with base-field response messages and
   automatic code membership. Honest responses pass every semantic coordinate
   check and finish correctly, and honest extraction returns the original table.
   Flat low-bit indexing, adjacent-cell fold-loop semantics, prefix/suffix
   source addresses and ordered tensor expansion are now proved. The opening
   bound and honest completeness are stated directly with complete flat-query
   folds. Native NTT/field instantiation, mutable Rust memory/word-size refinement,
   production XOF freshness, and the complete Merkle availability theorem remain open.
   The new Merkle payload reduction freezes a total word at one prefix cache/root.
   It permits overlapping leaf/node oracle encodings and reduces any later
   authenticated payload disagreement to a prefix collision or a fresh response
   in one fixed root-wide target family. Its one-fresh-query hazard is proved.
   The native bottom-up path loop now equals typed verification as an ordered
   oracle computation. Accepted whole-payload checks establish the cached leaf
   and node chain and inherit the frozen-word reduction. Native node-byte framing
   is injective and checker overhead is at most height+1 queries. Concrete
   column serialization, raw path validation, machine-size/Rust refinement and
   native freeze-point selection remain open. Shared-cache collision and
   source-stability losses are composed in the mathematical execution below. Payload extraction now has an online
   invariant over VCVio's heterogeneous checkpoint state: cache hits are harmless,
   fresh answers outside the shared target union preserve every source, and
   adaptively recorded roots retain one source per root/configuration. A whole
   suffix can destabilize it only through a fresh fixed-union target hit. The
   shared one-step bound uses the actual cached-key cover and deduplicated roots.
   The concrete cached hash handler now preserves exact cache/log/key coherence
   and projects to the canonical oracle. For a fixed recorded family, source
   instability at the end of arbitrary adaptive hash suffixes is bounded by
   the expected accumulated fresh-answer charge; repeated queries contribute
   zero. `CheckpointExecution` now interleaves private computations and adaptive
   root snapshots with that same canonical hash. Its persistent first-failure
   monitor cannot be reset by later queries or recordings, and its probability
   has an unrestricted expected-charge bound. Erasing the ghost state preserves
   every answer and cache update. Shared-cache collision loss is now composed
   with source instability on that same execution. The combined persistent
   exception has an unrestricted expected-charge bound. Every cached
   authenticated payload of every recorded root equals its frozen extraction
   outside that exception; one event covers all positions, paths and payloads.
   The native verifier is now embedded into that same shared execution.
   Acceptance establishes its leaf entry and typed chain in the actual cache,
   and arbitrary later queries preserve them. A checked single-opening game
   reduces accepted disagreement after any adaptive prefix to the root-wide
   event, with prefix and verification work included in the expected charge.
   The native source uses Rayon parallel column workers. Their own hash calls
   are now modeled with arbitrary intervening shared execution. Completed
   workers replay from the final cache, and a single expected-charge bound
   covers all listed replay-accepted columns in any global call linearization,
   including work already issued on rejection. Whole workers are not assumed
   atomic. Native flat payload/weight/response addresses and row-product folds
   now match the semantic coordinate checks. Sorted/deduplicated indices zipped
   to well-sized proof columns cover every original draw. The native Boolean
   coordinate loop checks both response families, and outside the same joint
   availability event both imply the existing matrix-opening checks on one
   immutable source in the equal-width default. List-valued shared hash payloads
   permit different column sizes across contexts, with exact typed recovery
   for accepted well-sized columns. Native scheduling/field/NTT/Rust refinement,
   commitment/challenge phase placement and complete PCS probability composition
   remain open. Probabilistic response procedures and arbitrary retained state
   now fit the same fixed-word bound: the matrix is sampled first, the response
   procedure runs next, and shared columns are sampled afterward. The proximity
   term and maximum of near/far column losses are unchanged; no response-uniformity
   or finite-response-space premise is introduced. A later-event composition
   lemma preserves the earlier bound without assuming independence. The actual
   shared-handler game now has an exact private-sampling/response-state law.
   Private uniform tests and columns leave the complete shared state unchanged,
   while arbitrary response and later work run through that same cached hash.
   Earlier root snapshots remain recorded throughout. From a recorded safe
   snapshot, typed authenticated wrong evaluations are bounded by the PCS
   arithmetic error plus the expected hash charge of this same complete
   execution. Adaptive commitment-prefix averaging now removes this initial
   safety premise: the complete experiment starts with an empty cache and root
   history, freezes the actual post-commitment source, and charges commitment
   and verification work together. The analysis snapshot projects exactly to
   the original shared program and does not affect protocol answers. Production
   transcript freshness, concrete parameters and physical-work coupling remain
   open.
   Arbitrary shared query-selection work may now run after that root snapshot
   and before the private matrix test. Private commitment memory also passes
   unchanged to query selection, correlated with its original coins and cache;
   only the root enters the checkpoint query. Its actual state passes into the opening;
   the uniform arithmetic bound averages over these adaptive query outcomes.
   One expected charge covers commitment, selection and the complete opening.
   A family of roots can now be recorded at the same actual commitment log,
   with exact projection of the analysis-only snapshots. Sequential factor
   openings retain private memory from each predecessor. Their arithmetic errors
   sum, while their final-cache authentication uses one availability event and
   one expected charge for commitment, query selection and the entire opening
   loop from empty initialization. The same bound now applies to a terminal-gated
   loop with actual early return: a disabled terminal check starts no opening,
   and a failed factor skips all later factors' private draws and hash calls.
   The expected charge refers to this actual program. The current family theorem
   uses homogeneous PCS dimensions; full terminal/stage wiring and heterogeneous
   layouts remain.
   The worker-flag interface is now instantiated by an executable interleaving
   scheduler. A column provider cannot supply a trusted flag: each worker runs
   the native leaf/path verifier and both coordinate checks, and acceptance is
   computed from its actual residual program. Original/residual equivalence is
   proved in every larger cache, so later factors preserve all earlier native
   authentication. The concrete stopped verifier now bounds wrong supplied
   values from empty initialization by the arithmetic sum plus one charge for
   commitment, query selection, scheduler background work and all actual worker
   calls. Public encoding/domain/roots/query override prover-supplied behavior.
   No replay or worker-trace certificate is supplied to that theorem. Verifier
   advance counts do not bound scheduler/adversary hash work. Native scheduling
   completion and Rayon/Rust refinement remain open.
   One context/root must retain one common source throughout every stage.
4. Interactive stage soundness: partially implemented. Packed sumcheck now has
   an honest scalar-round polynomial, native adjacent-node and matrix-fold
   identities, the exact degree bound, and independent-lane root counting.
   The round error is (D/card(F))^k. Adaptive messages and arbitrary probabilistic
   post-challenge callbacks compose to n*(D/card(F))^k from a false sum, against
   a truthful terminal factor obligation on the same repeatedly folded sources.
   Native D+1-entry messages automatically supply the degree bound; consecutive
   nodes and the 2*lane+bit layout match the checked shape conditions. The
   complete native shared ZeroCheck composition and native optimized
   interpolation refinement remain open. Authenticated packed sumcheck itself
   is now composed with concrete native openings as described below. The geometry bridge now fixes a decoded
   source using trusted front/suffix dimensions alone, before receiving any query.
   Every returned query folds that same source to the existing two-half PCS
   evaluation; the wrong finished-factor event is exactly the PCS evaluation
   mismatch. Empty front/suffix halves and native low-bit order are included.
   A source-independent packed-sumcheck oracle verifier
   now returns its actual ordered query/expected vector. Its message and callback
   programs run through one shared cached handler; rejected message work remains
   in the returned state. The n*(D/card(F))^k arithmetic bound now applies to a
   truthful returned subclaim on that execution, including arbitrary later
   opening work. A source-independent terminal opener/checker gives false-sum
   acceptance at most that error plus the actual joint wrong-factor event.
   Native messages discharge the degree bound, while the cryptographic bound
   on that operational wrong-factor event still requires instantiating the new
   joint authenticated-opening theorem at the concrete checked opener. The
   shared-oracle ZeroCheck adapter is supplied below; its complete authenticated
   opening composition remains open. Native
   `snarks/src/packed_relation.rs::verify_inner` checks terminal values before
   opening any factor and returns on the first failed opening. The operational
   adapter must preserve that order and every actually issued hash call; adding
   ideal private coins on rejected paths does not justify additional transcript
   hash calls or physical-work charges. A new guarded sumcheck terminal adapter
   now performs the value check before binding/opening and stops at the first
   rejected factor. It preserves the receive-work and private memory on terminal
   rejection. Its wrong-factor event requires successful terminal checking and
   successful openings, so rejected wrong proposals do not consume a PCS error
   term. Literal native response checks enforce coverage, both coordinate
   families and equality of the finished response to the supplied factor value.
   Successful actual loops supply those checks and complete factor coverage;
   together with final-cache native worker replay, wrong supplied values imply
   the joint PCS bad-opening event for the same fixed decoded source. Connecting
   the shared ZeroCheck result, guarded terminal program and concrete native
   opening into one complete relation verifier remains open. The worker flags
   themselves are now computed and proved sound by `NativeColumnWorkerPool`;
   `NativeCommittedOpening` bounds the supplied-value error without a replay
   premise. The terminal preparation now has a program-level equality
   with the guarded receive/check/bind/open schedule. `AuthenticatedSumcheck`
   commits and records roots before running sumcheck, retains the returned
   subclaim while checking/binding supplied values, then runs the actual native
   stopping factor loop. It bounds acceptance of a false sum on the prefix's
   fixed decoded sources by n*(D/card(F))^b plus the PCS arithmetic sum and one
   expected hash charge for this same complete execution. False decoded-source
   sums are an event on actual prefix outcomes, not an input certificate. The
   native specialization fixes consecutive nodes and evaluation-message
   interpretation and proves degrees. No wrong-opening event is left unbounded
   in that theorem. This completes the private-coin authenticated sumcheck
   component. `PackedZeroOracle` now runs adaptive first-message work and the
   remaining rounds on the actual shared handler. Its returned subclaim retains
   equality points, mixing coins and the full original-factor query.
   `IndexedPublicEquality` proves its computed EQ terminal equals the ordered
   mixed-source fold. `PackedZeroSharedSoundness` proves the three-term
   arithmetic bound for that run, with native degree specialization and
   arbitrary-continuation preservation. `PreparedZeroTerminal` receives and
   binds only original-factor values, skips binding after terminal rejection
   and retains real memory/hash work. A checked terminal either is truthful or
   supplies a wrong original factor. Composing this packet with fixed decoded
   sources and concrete native stopped openings is now supplied by
   `AuthenticatedZeroCheck`: roots are frozen before equality points, the full
   query and decoded source are transported together onto the fixed PCS split,
   and only original factors are opened. Its false zero-relation event is
   bounded by the three ZeroCheck terms, the PCS arithmetic sum and one expected
   hash charge for that exact complete stopped execution. Its native
   specialization supplies both message degrees; its projection theorem erases
   the analysis-only prefix exactly. Full PBS stage composition remains open.
   `PBSHadamard` now fixes the first canonical PBS stage's actual trusted
   relation: positive evaluation/key products followed by one negative output
   term. Its typed roles biject with all native array indices, its factor loop
   uses the native pair order and its native-message theorem specializes the
   authenticated ZeroCheck error to original product degree two. A false
   pointwise aggregate identity is the bounded event; individual product terms
   are allowed to cancel exactly as in the native relation. This does not yet
   bind the key roots to public preprocessing or establish NTT meaning, nor
   compose the remaining verifier stages.
   `PackedLinear` now proves the next protocol family's trusted scalar/source
   relations: literal native residual accumulation equals vector combination,
   ordered matrix folding preserves it, and honest source tables pass the local
   check for every query. One false relation in a fixed family passes one common
   query within n*((2*b-1)/card(F))^b, without a relation-count union factor.
   `PackedLinearOracle` binds trusted relation context before that query, then
   receives all source values and computes the local flag. It adds no all-values
   binding before this check; each opening's claim binding occurs later.
   `SingletonOpening` proves one-claim batch transitions equal typed single
   openings, with their per-root prelude before test sampling and exact column
   attachment before the interleaved workers. `AuthenticatedLinear` composes
   these original-source openings in native index order and stops on failure.
   Its from-empty false decoded-source relation bound has the common-query
   compression term, PCS sum over sources and one charge for the exact complete
   shared execution. Checked fields override factory claims, and erasing the
   analysis-only prefix gives the actual program. `ConcreteLinearSecurity`
   constructs the PCS alphabet/basis and expands the PCS sum to sourceCount
   times the explicit numeric error. Raw proof-shape/normalization refinement,
   native integer/byte/Rust/scheduling, concrete canonical PBS relation instances
   and the complete stage composition remain open.
   `DecompositionLinear` now supplies the radix-decomposition instance: source,
   digit and borrow roles cover all 2*d+2 native slots, and the three trusted
   relations are exactly field reconstruction plus zero endpoint borrows.
   Honest local completeness is unconditional on the query, and the concrete
   from-empty bound authenticates every original column. This does not prove
   integer canonicity: digit-range and borrow-transition tuple lookups remain
   necessary, as demonstrated by a field-congruent out-of-range digit example.
   Deriving d/radix from checked native configuration, normalizing coefficients
   and integrating comparison lookups and subsequent PBS stages remain open.
   `RadixCanonicity` now proves the semantic canonicity link using the literal
   ordered public comparison tables. Table membership supplies bounded natural
   digits and borrow bits with the native transition rule; strict radix<p
   prevents cast aliasing. Weighted borrow inequalities telescope to an integer
   reconstruction below p. The actual digits of p-1 supply the width condition,
   and reconstruction then gives the canonical input representative and each
   individual quotient/remainder digit. The statement is per active position,
   without a lookup premise for inactive padding. A failed canonical identity
   explicitly yields a false linear relation or a missing concrete lookup row;
   lookup security is not assumed. Proving actual lookup-verifier enforcement,
   honest borrow-witness construction and native/PBS/transcript refinement
   remains necessary.
   `RadixWitness` now supplies that arithmetic witness construction. Its actual
   low-to-high sequence keeps every borrow a bit, satisfies every native step,
   and has final zero exactly when the bounded digit value plus its incoming
   bit is at most the public bound. Canonical field digits therefore produce
   all registry columns with the correct input slot, zero endpoint borrows,
   every linear constraint and literal public-table memberships. The canonical
   count derives the width condition internally. Zero input positions produce
   zero digits and borrows, agreeing with native padding initialization, and
   honest constructed tables pass the local linear check for every query.
   These are arithmetic completeness statements; full honest cryptographic
   prover/opening/scheduler completion and native/Rust/transcript refinement
   remain open.
   `TupleHash` now supplies the lookup's scalar hash component. Iteratively
   generated powers, ordered coordinate zip and native left accumulation equal
   extension-field polynomial evaluation and preserve base-field linearity.
   Distinct tuples give distinct degree-(width-1) polynomials. One fixed bad row
   can collide with the public table within tableSize*(width-1)/card(K); choosing
   one bad source before sampling avoids a source-family union. `RadixTupleHash`
   proves the actual ordered 2*radix table and its distinctness under radix<p,
   specializing this term to (2*radix)*2/card(K). The denominator is the tuple
   hash field's cardinality, independently of PCS analysis symbol width.
   `TupleHashOracle` retains this bound through arbitrary real shared preparation
   and later work. Reciprocal/rational detection, repetition, authenticated
   lookup acceptance, native extension-field/Rust and FS refinement remain open.
   `ReciprocalPolynomial` now supplies reciprocal detection for a fixed hashed
   source/table. Source products retain repeated rows and the native plus-sign
   denominator. Clearing the sum identity gives degree at most L+T-1; a missing
   row and L below the characteristic imply a nonzero numerator via its root
   multiplicity, without a supplied polynomial certificate. `ReciprocalMask`
   uses the literal partial-lookup residual r*h+mask*g*h-mask: nonzero r forces
   inactive helpers zero even for arbitrary original padding. Its full-helper
   sum therefore reduces to the active-prefix reciprocal sum. `ReciprocalDetection`
   excludes zero/public poles, retains the domain loss, proves domain
   nonemptiness/ideal-sampler totality under the public size guard, and obtains
   (L+T-1)/(card(K)-T-1). This is the ideal conditional-uniform law, not a proved
   native rejection-loop/transcript/work equivalence. Hash/reciprocal pair
   composition, repetition and actual authenticated lookup acceptance remain
   necessary.
   `TupleLookupPair` now composes the two arithmetic components in native draw
   order: sample y, hash the public table, then sample an accepted r. A fixed
   bad tuple is chosen before y; outside its table-hash collision event, the
   reciprocal theorem applies conditionally. Both losses remain in
   T*(width-1)/card(K)+(L+T-1)/(card(K)-T-1). Fixed original tuples, public table
   and multiplicities across fresh pairs give an exact independent product law
   and the combined-loss power bound. Packing/coordinate width is not a
   repetition count. Strict public domain size gives total ideal sampling;
   zero repetitions have vacuous all-pass probability one. `TupleLookupPairOracle`
   retains this arithmetic event through shared preparation and later adaptive
   work without erasing calls. Native rejection-loop/transcript/work refinement
   and actual authenticated lookup acceptance enforcement remain open.
   `PaddedExtension`, `ExtensionQuery` and `ExtensionSourceOpening` now prove
   the generic basis, padded-matrix and query bridge from `packed_extension.rs`.
   The multiplication matrices implement E*(a·)*D, with D*E=id and E*D a
   projection on arbitrary base vectors. Coefficient queries with no variables
   apply the projection after opening the original constant vector. Scalar
   queries select low-bit lanes first, placing the lane map on the right of
   the first pair or in the zero-variable post-map. No committed-zero helper
   padding is assumed. Ordered row evaluation equals the tensor MLE, and the
   canonical lane equivalence preserves native low-bit addresses. A decoded
   wrong extension claim implies a wrong base-field fold; with the actual
   PCS decoded source and response-finishing map it implies the existing
   PCS incorrect-evaluation event. Native polynomial-basis/extension-field,
   normalization, integer bit-loop/machine/Rust refinement and full lookup
   sumcheck/ZeroCheck/PCS acceptance composition remain necessary.
   `NativePrefixMask` now proves the high-to-low same/out recurrence equals
   the active-prefix MLE at arbitrary points, including empty/full-table
   branches and Boolean interpolation. `ExtensionLookupIdentity` computes
   public EQ, proves scalar tuple-hash linearity, and identifies the partial
   and full terminal formulas with the native product grammar and round
   degree bounds 4 and 3. The full-table g+r affine factor folds exactly;
   products of separate MLE factors are retained off the Boolean cube.
   `LookupReciprocalEnforcement` connects truthful helper sums and masked
   Boolean identities to the earlier reciprocal-pair event: a nonpassing
   pair forces a false sum or a false identity, whose fresh EQ miss bound is
   n/card(K) for sources/helpers fixed before that point. `ExtensionLookupTerminal`
   splits low lane/high row point coordinates and proves that successful
   decoded terminal checking implies a truthful factor expression or a false
   original source/helper base opening. Complete scalar sumcheck execution,
   grouped original-root PCS and one complete shared error/work bound still
   require composition; these are deterministic/local
   arithmetic components, not complete authenticated lookup security.
   `LookupSourceFlattening` now closes the full scalar source interpretation:
   it splits Boolean coordinates, factors tensor weights, preserves the exact
   lane+width*row address, recovers every original entry and proves flattening
   injective. The scalar query value equals the ordinary full scalar MLE;
   tuple compression equals the identity's hashed scalar-source evaluation.
   Both partial and full truthful terminal branches rewrite to their exact
   identity grammar over the same flattened sources. Zero lane/row dimensions
   are included. The remaining operational link is ordinary scalar sumcheck
   point/query semantics and its grouped original-root PCS/shared execution,
   not another source-view commitment.
   `ScalarSumcheckQuery` and `ScalarSumcheckOracle` now supply the ordinary
   scalar point/query link on the existing shared verifier. Native 1x1
   challenge matrices are exactly [1-x] and [x]. Every supported returned
   subclaim has this form, with no caller certificate, and its MLE terminal
   event inherits n*D/card(K). Native D+1 evaluation vectors supply degree
   bounds, and arbitrary later shared work retains the event and issued calls.
   `LookupScalarSubclaim` identifies helper-sum and partial/full identity
   events with the literal terminal formulas; decoded checked terminals give
   that event or a wrong original base opening. The remaining link is the
   complete sequential lookup program and grouped helper/source PCS event
   composition with one retained arithmetic/error/work bound.
   `LookupPairSequence` now implements the per-pair public sum-claim guard,
   helper-sum verifier, fresh EQ draw and identity verifier on one retained
   shared state. Sum failure skips EQ/identity work. `LookupPairArithmetic`
   computes the public total from actual tuple hashes/base multiplicities and
   derives the concrete nonpassing-pair joint bound n/card(K)+n*D/card(K),
   keeping D=4 partial and D=3 full. The fixed helper either has a false sum,
   bounded by n/card(K), or a correct sum and a nonzero identity, bounded by
   fresh EQ plus identity sumcheck; these exclusive cases need no independence.
   `LookupPairTerminal` computes source decoding and terminal equality and
   reduces successful local checking to the joint arithmetic event or the
   exact three original opening families. `PreparedLookupPair` receives actual
   values only after successful scalar stages, computes the check, binds only
   on success and proves returned-packet/earlier-subclaim provenance. Actual
   helper commitments, outer pair repetition and grouped original-root PCS
   authentication still need one complete shared error/work composition.
   `PreparedLookupSoundness` now transfers successful returned packets to the
   retained arithmetic event or original-opening failures. `CompletedLookupPair`
   and `LookupCompletionSoundness` retain the concrete bound through arbitrary
   later verifier work and gate the wrong-opening term by final acceptance on
   that same run. No security certificate is assumed for the callback.
   `VariableHeightBatchVerifier` handles selected-root authentication with
   context-indexed tree heights; computed native acceptance supplies replay.
   `DependentShortCircuitSequence` now supplies trusted root-indexed result
   packing. `HeterogeneousBatchOpening` composes the actual native family with
   its root-recording prefix, per-root arithmetic sum and one global expected
   availability charge. The staged and exact lookup adapters below provide
   commitment timing and original-opening binding; the actual repeated algebra
   selector still needs composition with `LookupCompletionSoundness`.
   `StagedCommitmentPrefix` and `StagedHeterogeneousBatchOpening` now
   preserve the two actual recording times. Sources freeze before the adaptive
   middle computation; helpers freeze after it and before algebra/query
   selection. Native grouped PCS bounds use those original snapshots directly,
   with one expected availability charge for the whole program.
   `LookupOpeningFamily` now fixes the native helper/source query and raw-value
   families and identifies their wrong-value event with the exact three pair
   opening failures. `LookupGroupedOpening` applies the staged PCS theorem to
   bound that final accepted event without a query multiplier or PCS security
   certificate. `RepeatedLookupSelector` now runs the actual canonical pair
   loop, proves each accepted projected packet comes from a successful pair
   result and skips later pairs after rejection. `RepeatedLookupAlgebra`
   derives concrete partial/full completion bounds for a preselected nonpassing
   pair without a repetition multiplier. Actual staged PCS wiring and the
   private pair-vector/false-statement composition remain to combine.
   `RepeatedLookupPCS` now fixes the actual gate, returned opening memory and
   packet projection in the native PCS continuation. `StagedRepeatedLookup`
   combines both recording times with scalar and native PCS arithmetic and
   one complete-run availability charge. Its total acceptance bound retains
   the all-pairs-pass probability explicitly; the private pair-vector law and
   application-level false-statement relation remain to discharge that term.
   The NTT row phase now has a checked tensor-fold/linear-transform identity,
   concrete ordered-node polynomial evaluation and the (r/card(F))^k row-miss
   bound. `NTTRowOracle` samples private points before arbitrary adaptive row
   proposals, binds rows on the actual shared cache before the local transform
   check, and computes its own acceptance flag. Rejected local checks retain
   both received and binding work. The bound persists through arbitrary later
   compression/opening work. Its accepted wrong-row event remains explicit.
   `NTTSourceQuery` proves that the full ordered source query compresses the
   actual tensor-folded polynomial, with coefficient bits low and row bits
   high, without an intermediate commitment. Independent compression and
   concrete batch-source authentication are supplied below. Native root/output
   order and optimized NTT equivalence, typed preflight and production
   transcript/Rust refinement remain required for the native NTT stage.
   `MatrixCompression` now bounds disappearance of a nonzero fixed table
   under c native fresh matrix folds by c*((2*b-1)/card(F))^b. Selecting one
   wrong fixed row before that query avoids a union over all coefficient and
   evaluation rows. `GuardedCompression` averages this bound over arbitrary
   earlier shared work and skips coins/callbacks after rejected row checks.
   `NTTCompression` composes both arithmetic errors on the same actual cache:
   against truthful terminal values at the exact original-source queries, a
   false block relation passes within (r/card(F))^k+c*((2*b-1)/card(F))^b,
   with native k=b. The earlier wrong-polynomial-row event no longer needs a
   row-authentication assumption; a wrong original-source compressed terminal
   is the remaining authentication obligation.
   The native non-hiding Brakedown `Parameters::verify_many` binds all queries
   and values before one shared random test, binds all structured responses
   before one shared column draw, authenticates columns once and checks every
   grouped finish value afterwards. Its concrete batch theorem must preserve
   those shared coins, response grouping and worker calls; replacing it by
   sequential independently sampled single openings is not an execution
   refinement. `BatchMatrixSampling` now proves the arithmetic bound for that
   exact common-test/common-draw experiment: a false value is selected from the
   fixed pre-test query/value family, so the entire batch pays one PCS error
   without a query-count union loss. Later actual worker work retains it.
   `BatchGrouping` computes stable first-seen representatives and bounded group
   indices, proves key recovery and precisely characterizes response aliasing.
   `BatchQueryLayout` applies it to raw ordered matrix prefixes and proves the
   representative's left weights match each query; semantically equal weights
   do not merge distinct native prefixes. `NativeBatchColumnWorkerPool` hashes
   each column only once, then checks the common test and every structured
   group. Its actual computed flags imply final-cache authentication and all
   coordinates, including preservation after later calls. The following modules
   supply concrete coverage/grouped finishes and committed PCS/availability
   composition; `AuthenticatedNTT` below links the NTT terminal values.
   `NativeBatchChecks` now enforces those coverage and every-query finish
   obligations. The exact nonempty sorted/deduplicated column selection gates
   workers, so invalid attachment cannot add authentication work. Each root's
   binding prelude occurs before its own test. `NativeBatchVerifier` computes
   all flags and derives replay on later caches; wrong values imply arithmetic
   or one common availability disagreement. `CommittedBatchOpening` composes
   actual multi-root batches from empty initialization. The loop stops at first
   failure, skips all later root preludes/coins/work, and pays one PCS arithmetic
   error per listed root plus one expected hash charge for the whole run.
   No replay or root-safety certificate and no wrong-opening residual remains.
   Its projection theorem erases the analysis prefix exactly.
   `AuthenticatedNTT` now forces the actual computed compressed queries and
   values into the opening factory, using the same original frozen sources and
   low-coefficient/high-row address order. Failed row checks retain receive/bind
   hashes and skip all compression coins/callbacks and both root batches.
   Its combined from-empty theorem bounds accepted false decoded-source
   transform relations by (r/card(F))^k+c*((2*b-1)/card(F))^b plus two PCS
   arithmetic errors and one expected hash charge on the exact complete run.
   Neither a per-repetition opening multiplier nor a truthful-terminal residual
   remains. `NTTButterfly` now proves the exact field radix-two algorithm
   evaluates at psi^(2*reverse(i)+1), with contiguous output halves and an
   explicit bit-reversal permutation. Primitive psi of order 2*N gives distinct
   nodes, each satisfying node^N=-1. No transform-correctness certificate is
   assumed: polynomial half-splitting proves every butterfly step.
   `PackedNTT` identifies coefficient/lane address lane+b*block, proves packing
   round trips and equality with the concrete linear map, and forces the actual
   field butterflies into the authenticated scheme. Its from-empty theorem
   bounds false butterfly relations on the original frozen sources with the
   same arithmetic and whole-run hash charge. `NTTBlockEncoder` proves the
   per-lane zero-initialized/copy/transformed/interleaved word equals the PCS
   polynomial encoder, hence belongs to the proved distance code.
   The generic results retain an explicit primitive-root condition.
   `NativeFields` now proves the two native moduli prime by Lucas certificates,
   using kernel-checked modular exponentiation and complete p-1 factorizations.
   `NTTRootCheck` identifies the nonzero/half-power test with primitivity in odd
   characteristic. `NativeNTTRoots` checks top roots of orders 2^32 and 2^27,
   proves full admissible mathematical root towers and validates the literal
   N=1024 roots observed from the existing native plan. The main schemes force
   Goldilocks b=k=4,c=8 or BabyBear b=k=8,c=7 and the corresponding proved
   butterfly map, independently of PCS code-block and lookup-extension widths.
   `NativeNTTSecurity` supplies concrete-field from-empty theorems with NTT
   arithmetic errors (r/p)^4+8*(7/p)^4 or (r/p)^8+7*(15/p)^8, plus two PCS
   errors and one whole-run hash charge. Primality, primitive-root and transform
   correctness are no longer supplied conditions in these concrete theorems.
   `PCSAnalysisField` now constructs the degree-b symbol field as GaloisField
   p b, with finite alphabet, fixed Fin-b basis and uniform auxiliary sampler.
   It proves cardinality p^b and supplies the concrete Goldilocks p^4 and
   BabyBear p^8 alphabets independently of lookup degrees 3 and 6. This is an
   analysis construction and adds no calls to the actual verifier program.
   `PCSParameters` expands both code distances to delta=L-m+1, retaining
   truncating Nat subtraction, and identifies the exact PCS loss with
   delta/q^b + max(((L-(delta-radius))/L)^Q,((L-(radius+1))/L)^Q).
   The finite-real version agrees for nonzero q and preserves every term;
   zero alphabet size is deliberately excluded from that coercion theorem.
   `ConcreteNTTSecurity` now supplies concrete NTT theorems with constructed
   alphabets/bases and this complete explicit error, with unchanged program
   and one whole-run hash charge. Its remaining public PCS conditions are
   positive widths, m<=L, source capacity and radius<delta/3. Selecting and
   certifying the native numeric parameters for the total 128-bit objective
   remains necessary, as do the remaining stages and production transcript.
   Native concrete-ntt uses Tonelli–Shanks root construction, so proving its
   integer implementation and plan/cache return values agree with these
   constants is still required, together with optimized kernels, lazy field
   residues, buffer/index operations and Rust refinement.
   Native static first-message preflight precedes transcript
   points; the interactive interface permits first messages adaptive to sampled
   points. Their Fiat–Shamir/Rust refinement remains explicit. Packed ZeroCheck's special
   first-round polynomial, boundary and mixing identities are now proved. Its
   native first-message Boolean loop checks exactly the polynomial boundary.
   Independent equality points miss a false relation with probability at most
   (n/card(F))^k; later fresh mixing and row challenges hide a nonzero polynomial
   family with probability at most ((D+1)/card(F))^k. Combining both terms permits
   arbitrary probabilistic first messages chosen after the equality points.
   Native evaluation vectors supply the first-message degree automatically.
   Cube/Boolean/flat suffix correspondence and the native two-block equality
   table are now proved. The verifier's ordered public-EQ recurrence equals
   folding that actual mixed source. Its typed terminal Boolean check is exactly
   the reduced expression when original factor vectors are their true folds.
   Special-round and remaining-round soundness now compose on one original
   source: for n+1 variables the error is (n/q)^k+(((2*k-1)*d+1)/q)^k
   +n*(((2*k-1)*(d+1))/q)^k, where q=card(F) and d bounds original product arity.
   Native evaluation vectors supply both degree bounds automatically. This
   composed private-coin experiment still has a truthful terminal factor
   obligation. Honest-run completeness now uses a concrete dimension-and-table
   state in these same verifier experiments: each message is the honest round
   polynomial encoded at native nodes, and each challenge folds the stored
   sources. Every supported run accepts and acceptance probability is one,
   including zero remaining rounds. Both codecs are proved; native adjacent
   round checks and the Boolean first-message boundary check always pass.
   `AuthenticatedZeroCheck` now discharges terminal authentication on the
   actual shared run. Prove the production transcript, honest
   callback/optimized-prover, scheduling-completion and Rust adapters before
   claiming complete native ZeroCheck. Prove lookups, decomposition, NTT,
   accumulator, monomial and final extraction bounds with their exact
   commitment/challenge order before claiming complete stage soundness.
5. Adaptive transcript compilation: open. Use one consistent input-indexed XOF
   stream and one declared hash oracle; cover receipts, checkpoints, children,
   prequeries, partial reads, repeated inputs and off-path inputs.
6. Expected work and parameters: open. Generic unbudgeted additive-hazard
   accumulation and its exact VCVio expected-query-count specialization are now
   proved. The concrete canonical cached-hash handler and its fixed-checkpoint
   suffix accumulation are now instantiated. Full primitive composition,
   native phase placement and physical cost coupling remain open. Shared-cache
   collision loss is now composed with the checkpoint-stability bound.
   Adaptive checkpoint recording and private-sampling interleaving
   are now included in the concrete execution and its first-failure charge bound.
   Prove full-history first-bad-event hazards,
   construction/query/submission cost coupling and honest setup offsets. Select
   query quotas only after proving the complete inequality. No query cutoff,
   zeroed unknown loss, or empirical resource maximum substitutes for this step.
7. Implementation refinement: open. Prove typed Rust acceptance refines the Lean
   model, then specify byte decoding separately. Extraction tools and primitives
   must have an explicit trust boundary. Differential tests are not refinement.

Intermediate theorems may expose explicit premises. No final security claim may
silently assume its unresolved PCS, Fiat-Shamir or expected-work conclusion.
The permitted kernel foundations are `propext`, `Classical.choice`, and
`Quot.sound`; headline dependencies must not contain `sorryAx`, custom axioms,
or native-compiler trust.

## Checks

Run focused builds with `scripts/in-container lake build
FormalProof4FHETest.HasteBootsSmoke`, then the containerized Lean audit client.
`scripts/check` explicitly includes the HasteBoots smoke target. Import the new
library through `FormalProof4FHE.HasteBoots`; the legacy umbrella modules stay
unchanged.

Verified for this increment:

- The focused Lake build passes (including cached dependencies).
- Direct Lean checking of `HasteBootsSmoke.lean` with `warningAsError=true` passes.
- Three hundred ninety-one guarded transitive axiom checks report only `propext`, `Classical.choice`
  and `Quot.sound`; unexpected additional axioms fail the smoke target.
- Dependency resolution contains exactly one VCVio, the original local path;
  no existing dependency revision changed.
- `git diff --check` passes.

The full legacy-repository `scripts/check` gate passed before `NativePublic`
and passed again with public preprocessing included. Both runs include the
complete library/test build and all standalone audit/smoke invocations.
The composed reference and extraction bridge pass the focused build and guarded
smoke tests. Their full gate passed in `/tmp/hasteboots-pbs-check.log`.
The common-source/proximity, symbol/coefficient sampler, exact code
correspondence and base-layout proximity bridges pass focused validation, strict
Lean checking and all 55 guarded axiom checks. Their full `scripts/check` gate
passed in `/tmp/hasteboots-code-correspondence-check.log`.
The shared-column, adaptive near/far, and combined common-source opening
components pass the focused build, strict Lean smoke checking and 71 guarded
axiom checks. Their full `scripts/check` gate passed in
`/tmp/hasteboots-column-opening-check.log`.
The native semantic response, matrix finishing, extraction and completeness
adapters pass the focused build, strict Lean smoke check and 91 guarded axiom
checks. Their full `scripts/check` gate passed in
`/tmp/hasteboots-matrix-response-check.log`.
The flat-index, query-split and complete flat-query opening adapters are
checked by the focused build, strict Lean smoke check and 109 guarded axiom
checks. Their full `scripts/check` gate passed in
`/tmp/hasteboots-flat-opening-check.log`.
The common-domain Merkle model, prefix payload recovery, deterministic
availability reduction and one-step hazard pass the focused build, strict Lean
smoke check and 127 guarded axiom checks. Their full `scripts/check` gate passed
in `/tmp/hasteboots-merkle-availability-check.log`.
The native pure/effectful path, accepted cached verification and byte-framing
adapters pass the focused build, strict Lean smoke check and 149 guarded axiom
checks. Their full `scripts/check` gate passed in
`/tmp/hasteboots-native-merkle-check.log`.
The payload-evolution, checkpoint stability, shared-union hazard and unrestricted
accumulation foundation pass the focused build, strict Lean smoke check and
174 guarded axiom checks. Their full `scripts/check` gate passed in
`/tmp/hasteboots-payload-checkpoint-check.log`.
The concrete cached-hash handler, exact cache/log/key invariant, canonical-run
projection and fixed-checkpoint adaptive-suffix accumulation pass the focused
build, strict Lean smoke check and 192 guarded axiom checks. Their full
`scripts/check` gate passed in `/tmp/hasteboots-cached-handler-check.log`.
The adaptive checkpoint/private-computation execution, canonical projection,
persistent failure monitor and unrestricted first-failure charge bound pass the
focused build, strict Lean smoke check and 206 guarded axiom checks. Their full
`scripts/check` gate passed in `/tmp/hasteboots-adaptive-checkpoints-check.log`.
The shared-cache collision hazard, combined persistent exception and root-wide
authenticated-payload availability bound pass the focused build, strict Lean
smoke check and 228 guarded axiom checks. Their full `scripts/check` gate passed
in `/tmp/hasteboots-shared-availability-check.log`.
The native verifier routing, actual-cache acceptance bridge, continuation
persistence and checked single-opening availability game pass the focused
build, strict Lean smoke check and 238 guarded axiom checks. Their full
`scripts/check` gate passed in `/tmp/hasteboots-native-opening-execution-check.log`.
The final-cache replay interface, interleaved native-worker trace semantics
and joint listed-column availability bound pass the focused build, strict Lean
smoke check and 250 guarded axiom checks. The interleaving regression uses
actual cached-handler steps and a background hash between a native worker's
leaf and node calls. Their full `scripts/check` gate passed in
`/tmp/hasteboots-interleaved-columns-check.log`.
The native coordinate address/fold/coverage proofs, two-family Boolean checks,
list-payload typed recovery and authenticated fixed-word-check bridge pass the
focused build, strict Lean smoke check and 271 guarded axiom checks. Regressions
cover distinct packing/block widths, the two response families, duplicate draws
and zero fallback. Their full `scripts/check` gate passed in
`/tmp/hasteboots-coordinate-bridge-check.log`.
The adaptive-response marginal/composition interface, probabilistic-response
common-source bound and native matrix-opening specialization pass the focused
build, strict Lean smoke check and 276 guarded axiom checks. Regressions cover
challenge-correlated response coins and a fresh draw after the response. Their
full `scripts/check` gate passed in `/tmp/hasteboots-random-response-check.log`.
The actual private-sampling law, checkpoint persistence and combined conditional
interactive opening bound pass the focused build, strict Lean smoke check and
287 guarded axiom checks. Their full `scripts/check` gate passed in
`/tmp/hasteboots-shared-interactive-check.log`.
The adaptive commitment-prefix projection and empty-cache authenticated
interactive matrix-opening theorem pass the focused build, strict Lean smoke
check and 291 guarded axiom checks. The prefix regression hashes before
recording its actual log and drawing private coins. Their full `scripts/check`
gate passed in `/tmp/hasteboots-commit-prefix-check.log`.
The packed-round interpolation/fold/degree identities, independent-lane root
probability, consecutive-node/native-message adapters and adaptive n-round
soundness bound pass the focused build, strict Lean smoke check and 315 guarded
axiom checks. Regressions exercise cross-lane challenges, repeated factors,
adjacent native entries and exact two-lane healing probability. Their full
`scripts/check` gate passed in `/tmp/hasteboots-packed-sumcheck-check.log`.
The packed ZeroCheck special-first-round algebra, reduced-shape EQ-factor
identity, independent equality-point and matrix-mixing bounds, adaptive
first-message reduction and native Boolean boundary-check adapter pass the
focused build, strict Lean smoke check and 338 guarded axiom checks. Regressions
cover equality weights, row-major mixing, zero vector components, coin regrouping
and the last boundary entry. Their full `scripts/check` gate passed in
`/tmp/hasteboots-zero-first-check.log`.
The cube/Boolean/flat suffix correspondence, native two-block equality table,
ordered public-EQ evaluation, typed terminal-check identity and composed
private-coin packed ZeroCheck bound pass the focused build, strict Lean smoke
check and 365 guarded axiom checks. Regressions cover low/high bit order, native
EQ table entries, noncommuting query order and final-lane terminal rejection.
Their full `scripts/check` gate passed in
`/tmp/hasteboots-composed-zero-check.log`.
The honest evaluation-message codecs, concrete stored-table sumcheck/ZeroCheck
provers, literal native round/boundary checks and probability-one completeness
for the existing verifier experiments pass the focused build, strict Lean
smoke check and 376 guarded axiom checks. Regressions cover maximum-degree and
zero messages, a nonzero square-sum source, and a valid ZeroCheck relation at
arbitrary suffix depth. Their full `scripts/check` gate passed in
`/tmp/hasteboots-honest-complete-check.log`.
The source-independent ordered subclaim verifier, exact shared-handler round
law, shared-execution arithmetic bound, arbitrary-continuation preservation
and terminal wrong-factor reduction pass the focused build, strict Lean smoke
check and 391 guarded axiom checks. Regressions retain rejected-message hash
work, skip its callback, preserve the valid message/draw/callback state sequence,
and expose an accepting incorrect factor as the explicit residual event. Their
full `scripts/check` gate passed in `/tmp/hasteboots-shared-subclaim-check.log`.
The fixed decoded-source/query geometry and adaptive query-prefix opening
bound pass the focused build and 401 guarded axiom checks. Regressions check
low/high split addresses, noncommuting matrix order and both empty-half cases.
Their full `scripts/check` gate passed in `/tmp/hasteboots-adaptive-query-check.log`.
The additional private-memory commitment-prefix projection and averaging lemma,
and the opening theorem generalized to retain that memory, are covered by 404
guarded axiom audits. The focused build, strict smoke check and final full
`scripts/check` gate passed; the complete final log is
`/tmp/hasteboots-stateful-query-check.log`. The private-memory regression retains
sampled commitment coins across the checkpoint while recording only the public
root.
The shared sequential arithmetic union, final-cache joint authentication,
multi-root recording/projection and empty-cache joint opening theorem have 419
guarded axiom audits. Regressions cover private-memory-dependent hash order,
repeated roots and the actual post-commitment log. The focused build, strict
smoke check and full `scripts/check` gate passed; the complete gate log is
`/tmp/hasteboots-joint-opening-check.log`. No custom axioms, admitted proofs or
compiler-evaluated proof shortcuts were introduced.
The actual early-return loop, terminal-before-opening adapter, stopped joint
opening bound and literal factor-value checks are covered by 438 guarded axiom
audits. Regressions retain failed-step memory and hashes, skip later openings,
skip binding on a wrong terminal value, exclude rejected proposals from the
accepted PCS event, and reject a wrong claimed finish value. The focused build,
strict smoke check and full `scripts/check` gate passed. The complete gate log is
`/tmp/hasteboots-guarded-terminal-check.log`; no custom axioms or admitted proofs
were introduced.
The executable hash-worker scheduler, native authentication/coordinate pools,
cache-persistent successful-factor checks and concrete supplied-value opening
bound have 458 guarded axiom audits. Regressions cover A-leaf/B-hash/A-node
interleavings, unfinished workers with pre-cached answers, cancellation with
retained background work, two actual native columns and coordinate rejection.
The focused build, strict smoke check and full `scripts/check` gate passed.
The complete gate log is `/tmp/hasteboots-computed-worker-check.log`; the new
headline proofs have guarded transitive axiom checks, with no custom axioms,
admitted proofs or compiler-evaluated proof shortcuts.
The terminal preparation equality and complete authenticated packed-sumcheck
bound, including native evaluation-vector specialization, have 468 guarded
axiom audits. Regressions cover exact guarded/prepared program equality,
retained rejected-packet memory and the complete committed zero-round program
skipping binding/opening work after a bad terminal identity. The focused build,
strict smoke check and full `scripts/check` gate passed; the full log is
`/tmp/hasteboots-authenticated-sumcheck-check.log`. No custom axioms, admitted
proofs or compiler-evaluated proof shortcuts were introduced.
The source-independent shared ZeroCheck program, indexed public EQ evaluation,
three-term arithmetic bound, native evaluation-vector specialization and
original-factor terminal preparation have 484 guarded axiom audits. Regressions
cover noncommuting indexed EQ order, first-boundary rejection with retained
message hashes and skipped mixing/callbacks, the zero-suffix mixing-column sum,
terminal rejection preserving received memory, and successful binding retaining
its hash after reception. The focused build, strict smoke check and full
`scripts/check` gate passed; the complete gate log is
`/tmp/hasteboots-shared-zero-check.log`. These proofs introduce no custom axioms,
admitted proofs or compiler-evaluated proof shortcuts. Concrete committed
ZeroCheck opening composition remains the next obligation; native static
preflight versus adaptive private-coin first-message order remains explicit for
Fiat–Shamir/Rust refinement.
The complete authenticated ZeroCheck program, simultaneous query/source
reindexing, native first/ordinary message specialization and exact analysis
projection have 492 guarded axiom audits. Regressions cover overriding a
conflicting opening-factory value with the checked original value, an empty
PCS suffix with the special variable in the front, preserved ordered query
lists, and a complete committed run retaining both commit/first-message hashes
while skipping mixing, terminal and PCS work after a bad first boundary. The
focused build, strict smoke check and full `scripts/check` gate passed; the
complete gate log is `/tmp/hasteboots-authenticated-zero-check.log`. No custom
axioms, admitted proofs or compiler-evaluated proof shortcuts were introduced.
False decoded-source zero-relation acceptance is now bounded by the three
ZeroCheck terms, the PCS arithmetic sum and one expected hash charge for that
same stopped execution; no wrong-opening event or EQ commitment remains.
Full PBS stage relations/order, heterogeneous stage composition, native honest
scheduling completion, Fiat–Shamir, concrete fields/NTT and Rust/physical-work
refinement remain required by the original objective.
The first concrete canonical complete-PBS Hadamard stage now has 499 guarded
axiom audits. Its trusted shape fixes product arity two, coefficient signs,
evaluation/key pairs and the final output slot. Typed roles biject with native
array indices and every factor is covered in native order. The pointwise
aggregate relation is equivalent to the ZeroCheck zero relation, and its
native-message soundness theorem specializes the complete authenticated bound
without a supplied shape, degree or factor-coverage certificate. Regressions
cover exact native index order, two contributing products, swapped key rows,
a changed output, valid cancellation of opposite products and the zero-pair
edge retaining the output term. The focused build, strict smoke check and
full `scripts/check` gate passed; the full log is
`/tmp/hasteboots-pbs-hadamard-check.log`. No custom axioms, admitted proofs or
compiler-evaluated proof shortcuts were introduced. Public-key preprocessing
and root binding, NTT meaning, linear/decomposition/lookup/accumulator/monomial
and final extraction relations, full sequential stage composition, honest
scheduling, Fiat–Shamir and Rust/physical-work refinement remain obligations.
The NTT tensor-row detection, source-query geometry and actual shared
proposal/binding prefix now have 517 guarded axiom audits. The row-miss bound
is (r/card(F))^k for a fixed false transform relation and persists through
arbitrary later work. Local acceptance reduces to that miss event or the exact
accepted wrong-row event, still explicitly unbounded. Source evaluation equals
compression of the tensor-folded original polynomial with native low
coefficient/high row address order. Regressions cover ordered size-two
negacyclic-root evaluation, swapped-output rejection, native join addresses,
noncommuting compression order and both received/binding hashes retained after
a failed local check. The focused build, strict smoke check and full
`scripts/check` gate passed; the complete log is
`/tmp/hasteboots-ntt-row-check.log`. No custom axioms, admitted proofs or
compiler-evaluated proof shortcuts were introduced. Independent compression,
concrete shared-test/shared-column Brakedown batch openings, native NTT roots,
bit-reversed output and optimized/Rust refinement remain necessary for the
complete NTT stage; remaining PBS stages and the full original objective stay
open.
Fresh coefficient-compression detection, guarded shared sampling and the
composed NTT arithmetic theorem now have 533 guarded axiom audits. A wrong
fixed polynomial row survives c fresh matrix folds with probability at most
c*((2*b-1)/card(F))^b; one common query covers all coefficient/evaluation rows
without a family-size factor. The actual shared row/check/compression program
bounds truthful original-source terminal acceptance by the row term plus this
compression term. Regressions cover a real native zero-challenge Lagrange
query hiding wrong rows, a nontrivial 1/17 composed bound over F17 and rejection
skipping positive-dimensional compression draws and callbacks while preserving
received/binding hashes. The focused build, strict smoke check and full
`scripts/check` gate passed; the complete log is
`/tmp/hasteboots-ntt-compression-check.log`. No custom axioms, admitted proofs or
compiler-evaluated proof shortcuts were introduced. Concrete native batch
terminal authentication with shared random test/columns, native NTT roots and
output order, the remaining PBS relations/stage composition, honest scheduling,
Fiat–Shamir and Rust/physical-work refinement remain open.
The shared-sampling batch arithmetic bound, stable native response grouping,
query-prefix/left-weight transport and computed interleaved batch column pool
now have 564 guarded axiom audits. A whole pre-test query/value family pays
one PCS arithmetic error, using one common test and column sample, without a
query-count multiplier. Grouping recovers first original representatives and
uses raw ordered prefixes; equal aggregate weights alone do not merge groups.
Batch workers authenticate columns once and check the test plus every group.
Regressions cover first-seen key order, suffix-only sharing, different prefixes
with equal weights, identical authentication-call counts for two groups,
a failing later group and an empty group family retaining the random-test
obligation. The focused build, strict smoke check and full `scripts/check`
gate passed; the complete log is `/tmp/hasteboots-native-batch-check.log`.
No custom axioms, admitted proofs or compiler-evaluated proof shortcuts were
introduced. Complete native coverage/grouped finish enforcement, root-wide
availability and probability composition, NTT terminal authentication, native
NTT/field/Rust refinement and the rest of the original security objective
remain open.
Completed-run logs are `/tmp/hasteboots-full-check.log` and
`/tmp/hasteboots-native-check.log`. Record any pre-existing unrelated failures
separately; do not weaken warning or axiom policy to obtain a successful build.

The committed native batch verifier now has 578 guarded axiom audits. Exact
nonempty sorted column coverage gates the worker pool; every original query,
including nonrepresentatives, must pass its finish check. Root binding runs
before each root's shared sampling, and rejection skips later root bindings,
coins and workers while retaining all hashes already issued. The complete
from-empty theorem bounds wrong values by one PCS arithmetic error per listed
root plus one availability charge for the whole execution; erasing its
analysis-only snapshot recovers the actual program. Focused build, strict
smoke and full `scripts/check` passed; full log:
`/tmp/hasteboots-committed-native-batch-check.log`. No custom axioms, admitted
proofs or compiler-evaluated proof shortcuts were introduced. Linking the NTT
queries and computed values to these batches, concrete native NTT/field/Rust
refinement and the remaining security objective stay open.

Authenticated NTT composition now has 584 guarded axiom audits. Actual row
sampling, adaptive receive/bind work, local transform checking and gated fresh
compression feed two stopped native original-source batches. Computed queries
and compressed values override factory claims. The from-empty false decoded
transform relation theorem pays the row and compression errors, two PCS
arithmetic errors and one whole-execution expected hash charge. It leaves no
truthful-terminal or wrong-opening assumption and no per-repetition loss.
Regressions check factory substitution, root protection, memory on disabled
compression and actual rejection retaining receive/bind hashes while skipping
compression and both root batches. Focused build, strict smoke and full
`scripts/check` passed; full log:
`/tmp/hasteboots-authenticated-ntt-check.log`. No custom axioms, admitted proofs
or compiler-evaluated proof shortcuts were introduced. Native NTT roots/output
order and field/Rust refinement, remaining PBS relations/composition, honest
scheduling, Fiat–Shamir and the concrete 128-bit expected-work theorem remain
open; the overall objective is not complete.

Exact-field negacyclic butterflies, packed NTT specialization and padded
coordinate encoding now have 609 guarded axiom audits. Polynomial half-splitting
proves the recursive butterflies evaluate at odd bit-reversed root powers;
primitive roots give distinct PCS nodes and node^N=-1. Packed flattening fixes
lane+b*block, and the authenticated scheme executes those proved butterflies
instead of a factory transform. Per-lane zero buffers, coefficient copying,
transforms and output interleaving equal the polynomial PCS encoder and land
in its distance code. Regressions cover eight-element bit reversal, explicit
F17 transform values, swapped middle-output rejection, packed lanes, the
one-element transform, unrelated factory-transform replacement, independent
lane padding and all-zero inputs. Focused build, strict smoke and full
`scripts/check` passed; full log: `/tmp/hasteboots-ntt-butterfly-check.log`.
No custom axioms, admitted proofs or compiler-evaluated proof shortcuts were
introduced. Primitive-root conditions remain explicit: validating retained
Goldilocks/BabyBear roots and refining native breadth-first/optimized kernels,
lazy residues and Rust buffers/indices remain necessary. The current native
default delegates to pado-labs/concrete-ntt, locked by Cargo.lock at
`cdeba793e46208320b30d78be19f7be78d49016a`; its optimized implementation is not
proved by the field-butterfly theorem. Remaining PBS relations/composition,
honest scheduling, Fiat–Shamir and the concrete 128-bit expected-work theorem
also remain open; the overall objective stays active.

Concrete prime fields, root checks and main NTT profile bounds now have 638
guarded axiom audits. Lucas certificates prove the actual Goldilocks/BabyBear
moduli prime. The native nonzero/half-power test is equivalent to primitivity
in odd characteristic; arithmetic certificates establish top orders 2^32/2^27,
all admissible mathematical root towers and the N=1024 literal roots. A probe
compiled against the existing native library returned main roots
455906449640507599 and 812423803, matching the independently proved literals;
it did not change the Rust worktree. Concrete-field NTT soundness now supplies
prime-field/root/packing/transform conditions internally, with arithmetic losses
(r/p)^4+8*(7/p)^4 or (r/p)^8+7*(15/p)^8 plus two PCS errors and one full-run
expected hash charge. Regressions cover zero, one, smaller/larger root orders,
the characteristic-two counterexample, field instances, canonical main-root
residues, main half powers and both tower endpoints; a beyond-adicity root
claim is disproved. Focused build, strict smoke and full `scripts/check`
passed; full log: `/tmp/hasteboots-native-root-check.log`. No custom axioms,
admitted proofs or compiled proof shortcuts were introduced. Proving native
Tonelli–Shanks/plan/cache return values and optimized kernels/field/Rust
refinement remains necessary; these arithmetic certificates do not supply that
refinement. The PCS analysis extension/basis, complete PBS composition, honest
scheduling, Fiat–Shamir and total 128-bit expected-work theorem remain open.

Constructed PCS alphabets and explicit concrete NTT losses now have 650
guarded axiom audits. `PCSAnalysisField` constructs degree-b Galois alphabets,
Fin-b bases and auxiliary uniform samplers, with cardinality p^b for positive
degree. The Goldilocks/BabyBear presets use degrees 4/8 independently of lookup
degrees 3/6. `PCSParameters` expands both code distances and retains the full
proximity term and both column-miss terms, with a proved finite-real bridge
and finiteness for nonzero alphabet size. `ConcreteNTTSecurity` supplies the
main NTT bounds without an external field/basis premise or abstract code
distance, while preserving the actual verifier program and one whole-run hash
charge. Regressions cover a 289-element constructed symbol field, lookup-degree
separation, zero-degree/zero-message boundaries, exact nontrivial PCS loss,
zero column quota, saturation and the zero-denominator counterexample to
unconditional finite-real coercion. Focused build, strict smoke and full
`scripts/check` passed; full log: `/tmp/hasteboots-pcs-alphabet-check.log`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced;
the Rust worktree is unchanged. Native parameter certification for the total
128-bit bound, native construction/kernel/field/Rust refinement, remaining
PBS relation enforcement and composition, honest scheduling and Fiat–Shamir
remain open; the overall objective is not complete.

Canonical packed-linear authentication now has 675 guarded axiom audits.
`PackedLinear` proves literal scalar accumulation, linearity of ordered matrix
folding, honest local completeness for every query and one compression loss
for an entire false fixed relation family. `SingletonOpening` proves equality
of the one-claim batch transition with actual typed single-column workers,
including preparation, column attachment, stopping and retained work.
`AuthenticatedLinear` binds trusted relations before one common query,
computes local checks before openings, protects all query/value/root fields
and opens original sources in native index order. Its from-empty bound has
one compression term, the source PCS error sum and one full-run expected hash
charge. `ConcreteLinearSecurity` constructs the analysis alphabet and gives
the explicit prime-field bound without an external extension/basis premise.
Regressions cover repeated indices, zero coefficients, lane violations,
shared-query cancellation, trusted-shape rejection, factory-field replacement
and retained hash calls on local rejection. Focused build, strict smoke and
full `scripts/check` passed; full log:
`/tmp/hasteboots-canonical-linear-check.log`. No custom axioms, admitted proofs
or compiled proof shortcuts were introduced; the Rust worktree is unchanged.
Raw proof preflight, dimension/count decoding and coefficient normalization
still require refinement; the single-transition equality is between the
stated typed programs. Canonical PBS coefficient/role instances, remaining
stage enforcement/composition, honest scheduling, native field/byte/Rust
refinement, Fiat–Shamir and the total 128-bit expected-work theorem remain
open; the overall objective stays active.

Trusted radix reconstruction and zero borrow endpoints now have 681 guarded
axiom audits. `DecompositionLinear` fixes the native registry (input, d digit
columns, d+1 borrow columns), proves that every slot has a role and identifies
the three ordered linear relations with explicit pointwise field identities.
Honest source tables pass every local query; the trusted preflight succeeds
under its positive-width/strict-field-size conditions. The concrete from-empty
theorem specializes the complete authenticated program with one compression
term, (2*d+2) full PCS errors and one whole-program expected hash charge.
Regressions cover the literal d=2/radix=4 coefficient/index order, a valid
reconstruction, nonzero initial/final borrows, a wrong digit, honest folding
and the zero-digit boundary. An out-of-range digit reconstructing 17=0 in F17
explicitly demonstrates why field reconstruction does not establish integer
canonicity. Focused build, strict smoke and full `scripts/check` passed; full
log: `/tmp/hasteboots-decomposition-linear-check.log` (9,970 build jobs plus
strict regression checks). No custom axioms, admitted proofs or compiled
proof shortcuts were introduced; the Rust worktree is unchanged. Digit-range
and borrow-transition tuple lookups, checked native configuration/normalization,
public-root and complete-PBS composition, honest scheduling, native field/byte/
Rust refinement, Fiat–Shamir and the total 128-bit expected-work theorem remain
open; the overall objective is not complete.

Integer canonicity from the native radix constraints now has 699 guarded
axiom audits. `RadixCanonicity` reproduces the ordered public transition
tables and recovers bounded natural digits, borrow bits and the outgoing
comparison result from field-valued membership under strict radix<p.
Weighted borrow inequalities telescope to a reconstruction below p; quotient/
remainder expansion and the digits of p-1 derive the canonical count's width
condition. Together with the trusted linear relation this identifies both
the reconstructed integer and every quotient/remainder digit with the input's
canonical representative. The semantic failure theorem retains a false linear
relation or a concrete missing lookup row, without assuming lookup security or
discarding its loss. Statements are per active scalar position and impose no
lookup condition on inactive padding. Regressions cover exact public-table
order, modulus digits/count, a valid nontrivial borrow chain, digit extraction,
field wraparound with forced versus true final borrow, an out-of-range digit,
cast aliasing when radix>=p and zero/one-radix arithmetic boundaries. Focused
build, strict smoke and full `scripts/check` passed; full log:
`/tmp/hasteboots-radix-canonicity-check.log` (9,971 build jobs plus strict
regression checks). No custom axioms, admitted proofs or compiled proof
shortcuts were introduced; the Rust worktree is unchanged. Actual lookup
verifier enforcement, honest borrow/table witness construction, checked native
configuration/normalization, public-root and full-PBS composition, scheduling,
native field/byte/Rust refinement, Fiat–Shamir and the total 128-bit expected-
work theorem remain open; the overall objective stays active.

Honest radix digits and borrow witnesses now have 725 guarded axiom audits.
`RadixWitness` implements the native low-to-high recurrence, proves every
computed borrow a bit and every transition exact, and proves final zero iff
the bounded digit value plus its incoming bit is at most the public bound.
Canonical field digits construct the actual 2*d+2 registry columns, preserving
the input and satisfying all linear identities and literal comparison-table
memberships. Witness existence specializes to the canonical digit count; the
width condition is derived rather than supplied externally. Zero input
positions produce zero digit/borrow columns, agreeing with native inactive
padding initialization. The generated honest values pass the local linear
check for every query. Regressions cover a nontrivial F17 borrow chain, the
maximum canonical value, the noncanonical value 17, a nonzero incoming bit at
the exact bound, the empty digit sequence, both packed lanes, registry order,
zero padding, constructed linear/lookup constraints, common-query local
acceptance and the canonical-count witness theorem. Focused build, strict
smoke and full `scripts/check` passed; full log:
`/tmp/hasteboots-radix-witness-check.log` (9,972 build jobs plus strict regression
checks). No custom axioms, admitted proofs or compiled proof shortcuts were
introduced; the Rust worktree is unchanged. Source inspection confirms the
same recurrence and zero initialization in both `prove_impl` and canonical
`borrow_tables`, with canonicalized digit conversion in the latter. Honest
cryptographic commitment/opening/scheduler completion, lookup-verifier
security, checked native configuration/field/integer/normalization/Rust
refinement, public-root and full-PBS composition, Fiat–Shamir and the total
128-bit expected-work theorem remain open; the overall objective stays active.

Scalar tuple hashing and the native radix-table specialization now have 746
guarded axiom audits. `TupleHash` proves iterative powers, ordered zip and
left accumulation equal extension-field polynomial evaluation, preserves
base-field linearity, and gives distinct polynomials for distinct base tuples.
The collision loss is tableSize*(width-1)/card(K), with one fixed bad source
selected before the common scalar challenge and no extra source-count factor.
Ordered list tables may contain duplicates. `RadixTupleHash` proves the literal
ordered digit/bit product, length 2*radix and distinctness under radix<p, giving
the degree-two specialization (2*radix)*2/card(K). `TupleHashOracle` routes the
one private scalar through the actual shared handler and retains its miss bound
through arbitrary preparation and later adaptive work, including rejection.
Regressions cover exact native power order, the exact two-root probability
2/17, shared-source hashing without a size factor, the abstract extension-field
bound 2/289, empty/single-coordinate boundaries, radix table geometry and cast
aliasing, and retained real hash calls around a rejecting continuation. An
adaptive post-challenge tuple forces a collision, explicitly testing why the
fixed-source premise is essential. The degree-two abstract field example is
not a native lookup-extension implementation certificate or a replacement for
the actual hash-field cardinality. Focused build, strict smoke and full
`scripts/check` passed; full log: `/tmp/hasteboots-tuple-hash-check.log` (9,978
build jobs plus strict regression checks). No custom axioms, admitted proofs
or compiled proof shortcuts were introduced; the Rust worktree is unchanged.
Reciprocal/rational detection, independent-pair repetition, actual authenticated
lookup acceptance, native extension-field/normalization/Rust refinement,
honest cryptographic opening/scheduler completion, public-root and full-PBS
composition, Fiat–Shamir and the total 128-bit expected-work theorem remain
open; the overall objective stays active.

Reciprocal detection and the exact masked helper identity now have 781 guarded
axiom audits. `ReciprocalPolynomial` uses the native r+hash sign, retains all
repeated active source rows, and clears the reciprocal sum to S'*T-S*Q with
degree at most L+T-1. A missing hashed source has positive root multiplicity
at most L<p; the characteristic bound proves both its pole coefficient and
the numerator nonzero for arbitrary fixed public multiplicities. Actual
helper reciprocal constraints force nonzero source denominators and the
correct inverses. `ReciprocalMask` proves the literal r*h+mask*g*h-mask identity
forces inactive helpers zero for nonzero r, even with arbitrary original
source padding; the full helper sum reduces to the active prefix and implies
the same numerator root. `ReciprocalDetection` excludes zero and public poles,
proves domain card>=card(K)-T-1 with repeated/overlapping poles, proves ideal
sampler totality under the strict public size guard, and obtains failure loss
(L+T-1)/(card(K)-T-1). The sampler is ideal conditional-uniform selection;
native rejection-loop, transcript and issued-work equivalence remain open.
Regressions cover the F17 false-pass point r=15 with sampling probability 1/15,
the bound 2/15, a rejecting point, excluded zero/poles, repeated/overlapping
poles and an empty domain. Characteristic-three missing-source repetitions
cancel the numerator and satisfy the reciprocal identity, confirming that the
strict L<p condition is necessary. Mask regressions cover active poles,
nonzero-r padding, the zero-r counterexample and a full-helper sum/root with
arbitrary source padding. Focused build, strict smoke and full `scripts/check`
passed; full log: `/tmp/hasteboots-reciprocal-check.log` (9,979 build jobs plus
strict regression checks). No custom axioms, admitted proofs or compiled proof
shortcuts were introduced; the Rust worktree is unchanged. Hash/reciprocal
pair composition, repetition, actual sumcheck/ZeroCheck/PCS lookup enforcement,
native extension-query/field/integer/normalization/Rust refinement, honest
cryptographic opening/scheduler completion, public-root and full-PBS composition,
Fiat–Shamir and the total 128-bit expected-work theorem remain open; the overall
objective stays active.

Hash/reciprocal pair composition and independent amplification now have 789
guarded axiom audits. `TupleLookupPair` follows the native y-then-accepted-r
order and retains combined loss T*(width-1)/card(K)+(L+T-1)/(card(K)-T-1).
One fixed nonmember is selected before y; outside its table-hash collision,
conditional reciprocal detection applies with L below the characteristic.
Original tuples, public table and multiplicities remain fixed across fresh
pairs. The exact all-pass probability is the single-pair probability to the
repetition count, and the combined-error power bound follows. Strict public
domain size gives total single and repeated ideal sampling; zero repetitions
pass vacuously. `TupleLookupPairOracle` routes the complete ideal sampler
through the shared handler and retains its arithmetic event through arbitrary
preparation and later adaptive work, including rejecting continuations and
all issued calls. Regressions cover width-one reciprocal-only loss, both loss
terms at width three, fresh-pair squaring versus reuse of one pair, the
zero-repetition boundary, totality, the indispensable accepted-domain
denominator and real retained hash calls around repeated ideal draws. Focused
build, strict smoke and full `scripts/check` passed; full log:
`/tmp/hasteboots-tuple-lookup-pair-check.log` (9,983 build jobs plus strict
regression checks). No custom axioms, admitted proofs or compiled proof
shortcuts were introduced; the Rust worktree is unchanged. This remains the
ideal private-coin arithmetic component. Actual sumcheck/ZeroCheck/PCS lookup
acceptance, extension/base query and basis refinement (including post-matrices
and ignored helper padding), native rejection-loop/field/integer/normalization/
Rust/transcript/work refinement, honest cryptographic opening/scheduler
completion, public-root and full-PBS composition, Fiat–Shamir and the total
128-bit expected-work theorem remain open; the overall objective stays active.

The generic lookup-extension/base-field query bridge now has 823 guarded
axiom audits (34 added). `PaddedExtension` proves the basis encoder/decoder,
exact successful element parsing, projection and native multiplication-column
identities. `ExtensionQuery` proves ordinary extension tensor evaluation for
coefficient and scalar sources, including arbitrary unused helper lanes,
zero-variable post-matrices, canonical low-bit lane addresses and the required
right-side lane map on the first row pair. Successfully decoding an incorrect
extension terminal implies an incorrect fold of the original base-field
source. `ExtensionSourceOpening` specializes this transfer to the actual PCS
common-source decoder and response-finishing map, yielding the existing
matrix-response incorrect-evaluation event for the same available word,
source layout and root interpretation. No projected source is recommitted,
no lookup-extension PCS security certificate is assumed, and lookup basis
dimension remains separate from the PCS analysis alphabet width.
Regressions cover malformed/nonzero padding, opening the original constant
vector before projecting, ignored helper padding at a non-Boolean point,
reading a scalar lane ignored by helper decoding, zero-variable scalar
post-maps, both matrix orders with different results, nonempty scalar queries,
low-bit lane weights, ordered two-coordinate evaluation, and wrong decoded
coefficient/scalar claims transferring to wrong original base openings. The
F17 singleton-basis examples are algebra regressions, not native lookup-field
implementation certificates. Focused build, strict smoke and full
`scripts/check` passed; full log: `/tmp/hasteboots-extension-check.log` (9,986
build jobs plus strict regression checks); strict HasteBoots smoke log:
`/tmp/hasteboots-extension-strict-smoke.log`. No custom axioms, admitted proofs
or compiled proof shortcuts were introduced; all guarded audits use only
`propext`, `Classical.choice` and `Quot.sound`. The Rust worktree remains
unchanged. The next obligation is actual lookup sumcheck/ZeroCheck/helper and
source PCS acceptance composition on one shared execution, retaining every
loss and issued call. Concrete native polynomial-basis/extension-field,
coefficient normalization, bit-loop/machine/Rust/bytes/transcript/work
refinement, native rejection sampling, honest cryptographic opening/scheduler
completion, public-root and full-PBS composition, Fiat–Shamir and the total
128-bit expected-work theorem remain open; the overall objective stays active.

The native lookup public-factor/terminal and reciprocal-enforcement milestone
now has 861 guarded axiom audits (38 added). `NativePrefixMask` proves the
high-to-low same/out loop equals the exact active-prefix MLE in original
low-bit address order, with separate full-table and zero-prefix branches and
Boolean interpolation. Its threshold uses canonical bit coordinates; the
Rust shift/word-size representation bridge remains open.
`ExtensionLookupIdentity` proves public EQ evaluation and tuple-hash linearity,
the literal masked terminal as separate MLE factors, the partial three-term
arity bound 4, the full affine-factor arity bound 3, and the corresponding
honest round-polynomial degree bounds. Constant/translated tables fold exactly,
so the full-table g+r operation introduces no new committed source. A fixed
nonzero masked Boolean identity survives one fresh EQ point with probability
at most n/card(K); helpers and sources must precede that draw.
`LookupReciprocalEnforcement` reindexes the original helper/source cubes in
native order and proves exact helper sums and masked Boolean identities imply
the active-source reciprocal event used by the pair theorem. A nonpassing
pair forces either a false full helper sum or a nonzero identity, with the
same EQ bound when the helper sum is truthful. Original source padding is
unrestricted; nonzero r forces inactive helpers zero. `ExtensionLookupTerminal`
splits the full point into low lane/high row coordinates and proves successful
source/helper decoding plus literal terminal equality imply the truthful
factor expression or a false original base-field source/helper query fold.
Tuple count, packing width and lookup basis degree remain distinct.
Regressions cover all four-cell prefix boundaries at non-Boolean points,
coordinate reversal, both loop accumulators, the indispensable full-table
shortcut, zero-dimensional masks, public EQ, scalar tuple hashing, and the
counterexample separating products of MLEs from the MLE of a pointwise
residual. A nonpassing pair with truthful helper sum receives the checked
1/17 fresh-EQ bound. Focused build, strict smoke and full `scripts/check`
passed; full log: `/tmp/hasteboots-lookup-identity-check.log` (9,987 build jobs
plus strict regression checks); strict HasteBoots smoke log:
`/tmp/hasteboots-lookup-identity-strict-smoke.log`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced; audit axiom sets are
subsets of `propext`, `Classical.choice` and `Quot.sound`. The Rust worktree
is unchanged. The next links are the ordinary scalar sumcheck point/query
semantics, original source flattening into the full scalar identity table,
and operational grouped helper/source PCS acceptance on one shared execution,
retaining all arithmetic/PCS errors and one complete-run hash charge.
Native polynomial-basis/extension-field and normalization/bit-loop/machine/
Rust/bytes/transcript/work refinement, native rejection sampling, honest
cryptographic opening/scheduler completion, public-root and full-PBS
composition, Fiat–Shamir and the total 128-bit expected-work theorem remain
open; the overall objective stays active.

The original packed-source/full-scalar-table bridge now has 874 guarded axiom
audits (13 added). `LookupSourceFlattening` splits the full cube into low lane
and high row coordinates, factors its tensor weights, and proves the exact
native address lane+width*row. Its query-independent flattening recovers every
original entry and is injective. The packed scalar-query value equals the
ordinary full scalar MLE of those same base entries embedded into the lookup
field. Tuple compression agrees with the identity polynomial's hashed scalar
source. Both partial/full truthful terminal branches rewrite directly to
their degree-four/degree-three identity grammars over these flattened sources
and the original helper decoder. No source view is newly committed, and no
zero-padding premise is imposed on original scalar source lanes. Regressions
check all four entries of a two-lane/two-row source, non-Boolean interpolation,
coordinate reversal, zero row variables, zero lane bits, both dimensions zero,
and width-four packing with degree parameter three and unequal lane/row bit
counts. These generic dimension examples are not a native extension-field
implementation certificate. Focused build, strict smoke and full
`scripts/check` passed; full log: `/tmp/hasteboots-source-flattening-check.log`
(9,991 build jobs plus strict regression checks); strict HasteBoots smoke log:
`/tmp/hasteboots-source-flattening-strict-smoke.log`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced; all guarded audit axiom
sets remain subsets of `propext`, `Classical.choice` and `Quot.sound`. The Rust
worktree remains unchanged. The next operational link is ordinary scalar
sumcheck point/query semantics, followed by grouped original helper/source PCS
acceptance and the full shared arithmetic/error/work composition. Native
polynomial-basis/extension-field and normalization/bit-loop/machine/Rust/bytes/
transcript/work refinement, native rejection sampling, honest cryptographic
opening/scheduler completion, public-root and full-PBS composition, Fiat–Shamir
and the total 128-bit expected-work theorem remain open; the overall objective
stays active.

The ordinary scalar sumcheck/query and lookup-subclaim milestone now has 894
guarded axiom audits (20 added). `ScalarSumcheckQuery` proves the native
width-one consecutive Boolean interpolation matrices are [1-x] and [x],
extracts the ordered point and identifies its fold with ordinary scalar MLE
evaluation, including zero rounds. Arbitrary 1x1 queries are not silently
assumed scalar. `ScalarSumcheckOracle` proves every supported result of the
actual shared `PackedSumcheckOracle.program` has scalar query form, through
arbitrary adaptive send/callback programs and rejection. This invariant is
proved operationally, not supplied as a certificate. The ordinary scalar MLE
terminal event inherits n*D/card(K); native D+1 evaluation-vector messages
supply their degree bound, and an ordinary field-element initial claim is
accepted by the theorem interface. Arbitrary later shared work retains the
MLE event and every issued call. This is a lookup-field bound with width one,
not a PCS-width repetition or base-field-cardinality substitution.
`LookupScalarSubclaim` identifies the helper-sum and both partial/full identity
MLE events with the literal terminal formulas over the original flattened
sources/helper decoder. Successfully decoded checked terminals expose that
arithmetic event or a false original source/helper base opening; the full
branch retains its degree-three affine grammar. Regressions cover native
non-Boolean and Boolean endpoint weights, point/coordinate order, ordinary
fold evaluation, an explicit nonscalar 1x1 query, zero-round folding and a
false zero-round terminal. A native [1,-1] evaluation-vector false boundary
claim receives the checked 1/17 MLE bound on the shared execution with actual
message/callback hash programs. Focused build, strict smoke and full
`scripts/check` passed; full log: `/tmp/hasteboots-scalar-check.log` (9,992 build
jobs plus strict regression checks); strict HasteBoots smoke log:
`/tmp/hasteboots-scalar-strict-smoke.log`. No custom axioms, admitted proofs or
compiled proof shortcuts were introduced; all guarded audit axiom sets are
subsets of `propext`, `Classical.choice` and `Quot.sound`. The Rust worktree is
unchanged. The next obligation is the complete sequential lookup program,
including helper-sum/EQ/identity stages and original grouped helper/source
PCS acceptance, with one shared arithmetic/error/work composition. Native
polynomial-basis/extension-field and normalization/bit-loop/machine/Rust/bytes/
transcript/work refinement, native rejection sampling, honest cryptographic
opening/scheduler completion, public-root and full-PBS composition, Fiat–Shamir
and the total 128-bit expected-work theorem remain open; the overall objective
stays active.

The per-pair lookup sequence and computed terminal-preparation milestone now
has 910 guarded axiom audits (16 added). `LookupPairSequence` implements the
public-table sum-claim comparison, native helper-sum sumcheck, fresh EQ draw
only after success, and identity sumcheck on the same shared state. It retains
the earlier sum result for the joint event and skips EQ/identity work after
sum failure. `LookupPairArithmetic` computes the public total from literal
tuple hashes and embedded base-field multiplicities. A nonpassing pair gives
joint truthful-subclaim probability at most n/card(K)+n*D/card(K), with D=4
partial and D=3 full. The proof splits on the fixed helper sum: if false, the
helper-sum verifier contributes at most n/card(K); if correct, reciprocal
enforcement yields a nonzero identity and fresh EQ plus identity sumcheck give
the displayed bound. These exclusive cases need no independence and do not
silently discard a loss. The full affine grammar is identified with the
Boolean masked grammar without replacing its smaller round degree. The caller
supplies no EQ or sumcheck security certificate to the concrete bounds.
`LookupPairTerminal` decodes supplied source vectors in order, computes the
literal terminal equality and proves successful local checks imply the joint
arithmetic event or one of exactly three wrong original opening families:
sum-helper, identity-helper and scalar sources. Helper claims are the encoded
subclaim/helper values; zero-variable post-projection fixes those encodings.
`PreparedLookupPair` runs claim reception after successful scalar stages,
computes its own check, binds only after success, and proves every returned
packet matches the actual earlier subclaims and checked values. It receives
no ghost source table or caller-supplied acceptance flag. These are the typed
per-pair stages and obligations, not complete authenticated lookup acceptance.
Regressions verify wrong public sum claims issue no stage calls; failed sum
messages retain their real hash and skip callbacks/EQ/identity work; partial
and full nonpassing pairs have the checked 1/17+4/17 and 1/17+3/17 bounds;
correct/incorrect terminal values and malformed terminal padding are handled
by the computed checker. Rejected terminal reception keeps its hash and skips
binding; successful reception binds on the same returned state and retains
both actual calls. F17 examples are algebra/runtime regressions, not native
lookup-extension implementation certificates. Focused build, strict smoke and
full `scripts/check` passed; full log:
`/tmp/hasteboots-pair-sequence-check.log` (9,998 build jobs plus strict regression
checks); strict HasteBoots smoke log:
`/tmp/hasteboots-pair-sequence-strict-smoke.log`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced; guarded audit axiom sets
remain subsets of `propext`, `Classical.choice` and `Quot.sound`. The Rust
worktree is unchanged. Remaining work includes transferring prepared-packet
acceptance to the retained joint event outside the explicit opening failures,
actual grouped helper/source PCS authentication (with their different layouts),
helper commitment prefixes, outer pair repetitions and one complete shared
arithmetic/error/work bound. Native polynomial-basis/extension-field and
normalization/bit-loop/machine/Rust/bytes/transcript/work refinement, native
rejection sampling, honest cryptographic opening/scheduler completion,
public-root and full-PBS composition, Fiat–Shamir and the total 128-bit
expected-work theorem remain open; the overall objective stays active.


The lookup completion and context-indexed-height milestone adds ten guarded
axiom audits, bringing the total to 920. `PreparedLookupSoundness` proves that
successful actual preparation supplies either the retained joint arithmetic
event or the three original opening failures, with concrete partial/full
bounds surviving reception and binding. `CompletedLookupPair` skips later
verification when preparation is absent and preserves arbitrary actual later
work otherwise. Its support and probability theorems retain the earlier
packet and charge wrong openings only together with final acceptance on that
same complete execution. `LookupCompletionSoundness` instantiates the generic
composition with the nonpassing-pair bounds n/card(K)+n*D/card(K), D=4 partial
and D=3 full, without accepting a supplied PCS security certificate. The
opening callback is intentionally arbitrary and still needs actual grouped
PCS instantiation.

`VariableHeightBatchVerifier` removes the constant-height restriction from the
single-root arithmetic-or-availability argument. Different contexts have
height(cfg); the selected native batch uses height(tag), and every other root
remains on the same shared cache and checkpoint state. Computed native batch
acceptance supplies worker-pool replay; the step theorem does not require a
caller replay or PCS certificate. The lower-level lemma states its replay
premise explicitly. Recorded root membership is still required and must be
obtained from the actual commitment prefix in the complete composition.

Regressions cover disabled preparation skipping a callback that would hash
and return true, later rejection retaining its real hash, and the difference
between arbitrary proposed failure and final accepted failure. A zero-round
actual local lookup preparation followed by an unconditional true callback
accepts wrong helper values with probability one, showing why authentication
cannot be omitted. A native height-one batch runs in a shared state also
supporting a height-two context and retains all five issued hashes in its
eight-entry log. This is a runtime test of the selected-root adapter, not a
proof of an actual heterogeneous multi-root execution.

The next authentication composition must use dependent per-root PCS layouts
(front, suffix, claim count, code parameters, query count and height), rather
than pad roots into a fictitious homogeneous commitment. Each actual native
step can retain its root index with its dependent result; successful sequence
coverage then identifies each wrong original query with its actual checked
batch. Use the real root-recording prefix to obtain checkpoint membership,
freeze each decoded source before adaptive query selection, sum per-root
arithmetic losses and charge the one global availability disagreement over
the complete execution once. The lookup completion theorem's final-accepted
wrong-opening event is the interface to discharge. Helper prefix ordering,
outer pair repetition, native rejection sampling, Rust/bytes/Fiat–Shamir
refinement, honest cryptographic scheduler/openings, full-PBS composition and
the final concrete unbudgeted 128-bit expected-work result remain open.

Validation for this milestone passed: focused HasteBoots build; strict
warning-as-error smoke; full `scripts/check` (10,002 build jobs plus its
strict regression suites); and `git diff --check`. Logs:
`/tmp/hasteboots-lookup-completion-smoke-build.log`,
`/tmp/hasteboots-lookup-completion-strict-smoke.log`, and
`/tmp/hasteboots-lookup-completion-check.log`. The smoke file guards 920
transitive axiom audits, all subsets of `propext`, `Classical.choice` and
`Quot.sound`. No custom axioms, admitted proofs or compiled proof shortcuts
were introduced. The Rust worktree is unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. These results complete this
milestone; the overall proof objective stays active.


The heterogeneous original-root authentication milestone adds five guarded
axiom audits, bringing the total to 925. `DependentShortCircuitSequence`
passively packs each actual native result with the trusted scheduled root's
index. A prover cannot supply another sigma tag; returned native data,
private memory, acceptance flag and shared state remain intact. The support
lemma recovers the actual native execution, and successful result checks hold
in the final cache after later roots run.

`HeterogeneousBatchOpening` gives each root its own front/suffix split,
claim count, m, query count and context-indexed height. The packing width and
PCS analysis field are common, as required by the fixed native PCS alphabet;
this is separate from lookup's extension field. Trusted encoding, domain and
emitted root override the behavior factory's corresponding fields. The
operational continuation selects queries after the actual root-recording
prefix, retains adaptive private memory, skips disabled work and stops on
rejection. Erasing the proof-only prefix snapshot recovers this exact actual
execution. No padded root views or replacement commitments are introduced.

The main `soundness_from_empty` theorem bounds final accepted wrong original
values by the sum of each listed root's own `JointMatrixOpening.error` plus
one `ExpectedHazard.charge` for the complete commitment/select/native-open
execution. Every decoded source is fixed by that root's prefix snapshot before
adaptive query selection. Computed accepted native batches establish replay
in the final cache. Successful loop coverage and trusted tags identify the
actual attempted batch for every wrong root. The context-indexed authentication
lemma then gives its arithmetic event or the single global availability
exception. The theorem derives the arithmetic bound internally and requires
no caller PCS security, replay, initial safety certificate or query budget.
Code-size/capacity, basis, relative-distance, root-list coverage and uniform
sampler premises remain explicit mathematical/protocol parameters.

Regressions verify different dependent result types retain scheduled tags;
rejection of the second step preserves both real hashes and skips a third
attempt; and the trusted emitted root overrides a behavior factory's different
root. A typed factory has genuinely different front/suffix, claim count, m,
query count and height for its two roots. A disabled actual continuation keeps
query-selection work while skipping both roots. A height-two native verifier
with missing columns rejects before authentication workers and keeps its
provider hash. An actual fresh-sampled dependent native loop runs that root
and rejects, retains its test and draw distribution, and skips the following
height-one root's prepare, samples and hashes. Small F17 examples are runtime
and algebra regressions, not native field/Rust or 128-bit certificates.

The homogeneous-layout barrier is removed. Remaining lookup authentication
requires exact family instantiation and staged commitment-prefix composition:
build the original-helper and source root families, prove every sum-helper,
identity-helper and scalar-source failure
maps to a wrong value in that family, and use the actual commitment ordering
to freeze helpers at the correct point relative to pair/EQ challenges. Compose
this with `LookupCompletionSoundness` on the same complete run, outer pair
repetitions and retained work. Native rejection sampling, polynomial-basis and
machine/Rust/bytes/transcript refinement, honest cryptographic scheduler/opening
completion, Fiat–Shamir, full-PBS composition and the final unbudgeted 128-bit
expected-work theorem remain open. The full objective stays active.

Native ordering recheck: `HasteBoots/snarks/src/packed_extension_lookup.rs`
lines 430–449 bind the already-public sources, derive all pair challenges,
and only then bind all reciprocal helper roots. Lines 450–505 perform the
sum/EQ/identity/terminal-claim algebra; lines 506–519 authenticate two helper
queries per pair/root; lines 531–545 authenticate the repetition-indexed
scalar queries per original source. Thus the one-prefix heterogeneous theorem
is not yet the complete native lookup theorem: original sources must retain
their earlier pre-pair checkpoints, while helpers freeze after pair challenges
and before EQ/sumcheck draws. Moving all source snapshots to the later helper
prefix would leave an adaptive-source gap. The next staged-prefix composition
must preserve both recording times and keep the same one whole-run availability
charge, rather than assume equality of the two decoded source snapshots.

Validation passed for this milestone: focused HasteBoots build, strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,001 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-heterogeneous-smoke-build.log`,
`/tmp/hasteboots-heterogeneous-strict-smoke.log`, and
`/tmp/hasteboots-heterogeneous-check.log`. All 925 guarded transitive axiom
audits use subsets of `propext`, `Classical.choice` and `Quot.sound`. No custom
axioms, admitted proofs or compiled proof shortcuts were added. The Rust
worktree remains unchanged; the overall security proof is still in progress.


The staged original-root authentication milestone adds eight guarded axiom
audits, bringing the total to 933. `StagedCommitmentPrefix` executes source
commitment/recording, an arbitrary adaptive middle computation, helper
recording and the actual suffix. The middle phase can contain pair challenges,
rejection sampling and helper commitment work. Its witness retains both
actual pre-recording states; projecting away those proof-only states recovers
the exact operational program, final state and all calls. Its event theorem
averages conditional arithmetic over both actual adaptive prefixes and charges
availability once over the complete execution from the empty state.

`RecordedHeterogeneousBatchOpening` proves native accepted-wrong reduction
against an arbitrary family of already-recorded original checkpoints, whose
recording times may differ. Root identity and recorded membership are explicit
bookkeeping inputs to this local lemma. It derives replay from computed native
acceptance and derives the per-root arithmetic bounds internally; it does not
assume initial safety, replay or PCS security. `StagedHeterogeneousBatchOpening`
then discharges the bookkeeping inputs from the actual source recording,
checkpoint preservation through the middle computation and helper recording.
The complete theorem sums the actual per-root PCS arithmetic errors and adds
one expected availability charge for source commitment, adaptive middle work,
algebra selection, disabled/rejected native branches and all interleaved hashes.

Source and helper root functions and private memories are retained separately
and assembled into trusted native roots. Every source word uses its original
pre-middle log; every helper word uses its own later helper-commit log. The
source is never re-decoded at the helper prefix and equality of those two
possible decoded words is not postulated. The native root order is all helpers
then all sources, matching the checked extension-lookup verifier. The packing
width and PCS analysis alphabet are common; per-root tensor split, claim
count, code parameters, query count and context height remain heterogeneous.
This is the actual two-prefix PCS composition, not yet the exact lookup
family/query or private pair/repetition instantiation.

Runtime regressions draw a real private coin between source and helper
recording, route middle work using the source phase's retained private memory,
and perform a later rejecting hash callback. The source snapshot has log
length four, the helper snapshot five, and the final rejected execution six.
The retained private coin and both checkpoints survive; projecting the witness
recovers the actual program. A negative regression proves that substituting
the helper-stage log for the source snapshot changes it, even with aliased
context tags. A trusted-order regression checks helper roots precede source
roots. These small cached-oracle tests establish ordering/work behavior rather
than native hash/field/Rust implementation security.

The next proof task is binding lookup's exact two original helper queries per
pair and repetition-indexed scalar source queries to this staged family, then
mapping `LookupPairTerminal.WrongOpenings` to accepted wrong native family
values and composing `LookupCompletionSoundness` on the same run. The original
multiplicities and decoded sources must precede pair draws; helper words may
depend on those pairs but must precede fresh EQ/sumcheck draws. The arbitrary
middle callback in this theorem deliberately does not assert the private pair
distribution or native rejection-sampling law. Pair/repetition composition,
honest cryptographic scheduler/opening completion, machine/Rust/bytes and
Fiat–Shamir refinement, full PBS and the final concrete unbudgeted 128-bit
expected-work theorem remain open. The overall objective stays active.

Validation for the staged-prefix milestone passed: focused HasteBoots build,
strict warning-as-error HasteBoots smoke, full `scripts/check` (10,004 build
jobs and all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-staged-smoke-build.log`,
`/tmp/hasteboots-staged-strict-smoke.log`, and
`/tmp/hasteboots-staged-check.log`. All 933 guarded transitive axiom audits
remain subsets of `propext`, `Classical.choice` and `Quot.sound`; no custom
axioms, admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged at `dff353006322693cab3dc6b654f82151f658f294`.
This completes the timing/authentication milestone; the full proof remains
in progress.


The exact lookup original-opening family milestone adds seven guarded axiom
audits, bringing the total to 940. `PackedQueryArity` transports only a trusted
equality of variable counts, preserving ordered matrices and Boolean-coordinate
fold semantics. `LookupOpeningFamily.Geometry` fixes each original root's
front/suffix split, code parameter m and number of column draws. Sources have
one claim per repetition; each helper has exactly two claims, in native sum
then identity order. These claim counts are distinct from PCS column-query
counts. Helpers use the original coefficient queries and encoded sum/helper
values. Sources use the original scalar queries and received raw packed vectors.
No new root, padded root view or post-map-finished source claim is introduced.

The operational binding function overwrites the behavior factory's query and
value fields with that trusted family. The staged native wrapper additionally
fixes encoding, domain and emitted roots. Neither ghost decoded tables nor an
assumed query/value-binding certificate enter the verifier. For each physical
root, the decoded table depends only on its original word, code and trusted
layout. A dimension equality expresses that same table at the lookup row
count. The two per-root equivalences identify the source/helper raw-fold
failures with their literal matrix PCS wrong-value predicates. The family
iff proves that some pair has one of exactly the three `WrongOpenings` cases
if and only if the native grouped family has a wrong claimed value. It is an
exact event correspondence, not a probability union over queries.

`LookupGroupedOpening.wrong_iff` retains the final native acceptance gate.
Its `soundness_from_empty` theorem applies the actual staged native PCS bound
to final accepted sum-helper, identity-helper or scalar-source failures of any
pair. The result sums each original root's own PCS arithmetic error and adds
one complete-execution expected availability charge. It includes both original
recording times, adaptive middle work, query selection, disabled/rejected paths
and actual worker calls. The lookup extension K has basis degree d; the PCS
analysis alphabet L has separate basis degree d+padding, with that common
packing width equal to 2^c. Their field types and basis degrees are not equated.
The theorem derives the PCS bound and assumes no PCS security certificate,
initial safety, replay promise, query-count cap or per-query independence.
Public code geometry, capacity/distance, basis, uniform sampler and list
coverage premises remain explicit.

Regressions use three source claims versus two helper claims and different
source/helper physical row dimensions. They verify sum/identity values and
ordering for a nonzero repetition index. A behavior factory's forged zero
helper query is replaced: its fold is zero, whereas the actual sum query folds
the original helper table to [4,0], including a helper table with nonzero raw
padding. A zero-row source retains raw [3,5] while its local scalar bridge
returns [5,0]; replacing raw PCS claims by finished values would fail this
regression. The original zero-row root gets no extra query matrices or new
committed view. These F17 tests check algebra and trusted binding, not native
extension implementations or a numerical 128-bit certificate.

This milestone covers the direct original-source opening branch of native
extension lookup. Deferred/global PBS collection still needs its actual larger
root/query family and sequence. The next algebra composition must construct
the actual repeated source-independent selector, retain packets from successful
`PreparedLookupPair` runs and identify those exact packets with this enforced
PCS family. Original source words and multiplicities must precede pair draws;
helpers may depend on pairs but must precede fresh EQ/sumcheck draws. Combine
private pair/repetition bounds, nonpassing-pair arithmetic, final accepted
opening failures and the same complete-run work charge, without assuming the
arbitrary selector here already verifies the lookup algebra. Native rejection
sampling, honest cryptographic opening/scheduler completion, machine/Rust/bytes
and Fiat–Shamir refinement, full PBS and the final concrete unbudgeted 128-bit
expected-work theorem remain open. The objective stays active.

For the next repetition proof, condition first on the source/multiplicity
prefix and then on the entire pair vector. Outside the all-pairs-pass event,
a first nonpassing index can be selected before helper commitment and all
algebra coins. Track that selected pair's actual returned packet through the
short-circuit algebra loop and subsequent PCS phase. This may avoid an
unnecessary repetition multiplier on the scalar-sumcheck loss: other indices'
bad predicates can be false, with the selected-event bound retained through
all earlier/later actual shared work. This is a proof strategy still to verify,
not a loss currently removed from an end-to-end theorem. Any final bound must
explicitly include the private pair collision/rejection terms, selected-pair
arithmetic, native root PCS losses and the single full-run work charge.

Validation for the exact lookup-opening milestone passed: focused HasteBoots
build, strict warning-as-error HasteBoots smoke, full `scripts/check` (10,010
build jobs and all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-lookup-grouped-smoke-build.log`,
`/tmp/hasteboots-lookup-grouped-strict-smoke.log`, and
`/tmp/hasteboots-lookup-grouped-check.log`. All 940 guarded transitive axiom
audits use subsets of `propext`, `Classical.choice` and `Quot.sound`. No custom
axioms, admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged at `dff353006322693cab3dc6b654f82151f658f294`.
The complete formal security objective remains active.


The repeated algebra/provenance and selected-pair completion milestone adds
ten guarded axiom audits, bringing the total to 950. `ShortCircuitAccumulator`
proves trace/private-memory invariants from actual supported successful step
transitions. `RepeatedLookupSelector` executes `List.finRange repetitions` on
one shared state, stores the raw results and fills a packet slot only from
that pair's actual returned `some (packet, memory)`. The next pair receives
that successful returned private memory. A `none` result rejects immediately,
retains its raw result and all issued shared work, and skips remaining pairs.
Because `none` exports no private memory, the halted output keeps its incoming
private memory; it is not described as a new callback-returned failure memory.

Its accepted-packet theorem proves every index is covered and the total PCS
projection returns a packet from a successful result at that same trusted
index in the actual trace. A projection fallback makes the function total on
rejected/incomplete outcomes, but no accepted slot uses it, for any fallback.
The accumulator proof handles index overwrites by retaining a real source
result for every filled slot, while canonical coverage supplies every index.
The selected arithmetic theorem uses the actual short-circuit program and
canonical one-occurrence coverage: all unselected bad predicates are false,
so the sum of conditional scalar losses is one selected loss, not a loss
multiplied by the repetition count. No independence or adversarial query cap
is used. The selected index must be fixed before algebra coins, never chosen
from observed verifier challenges/results.

`RepeatedLookupCompletion` ties successful projected-packet provenance to its
actual earlier raw result. The selected pair's algebra-or-wrong-opening fact
therefore applies to the exact packet delivered to later opening work. Its
completion callback is skipped after computed whole-selector rejection and
otherwise runs on the actual returned shared state and private memory. Final
accepted wrong openings are gated by that same complete execution's final
acceptance; rejected proposals do not become accepted attacks. The callback
has no assumed PCS security property.

`RepeatedLookupAlgebra` instantiates both generic local interfaces with the
actual native `PreparedLookupSoundness.program`. It computes public totals
from the fixed table/multiplicities and pair vector, retains sum-claim checking,
helper-sum sumcheck, fresh EQ, identity sumcheck, computed terminal reception
and checked binding. For a nonpassing index fixed before the repeated algebra,
concrete partial/full completion bounds are n/card(K)+n*D/card(K), D=4 partial
and D=3 full, plus final accepted selected-packet original-opening failure.
It derives native support/provenance and local arithmetic inside the proof;
no caller EQ, sumcheck, packet-provenance or PCS security certificate is an
input. Sources, pair vector and selected helper are fixed before this algebra
experiment; their staged commitment provenance and the private pair law still
need the final outer composition.

Regressions check that successful private memory changes the second pair's
actual hash choice; a second-pair rejection records only indices 0/1, keeps
both issued hashes and skips index 2; a callback that would hash and return
true is never invoked after rejection. A separate regression runs three
actual native zero-round pair verifiers with computed table totals and terminal
checks. They carry memory between real binding hashes, return their own helper
value one in every packet slot instead of fallback fifteen, and retain all
three calls in the six-entry shared log. Degenerate dimensions and F17 are
algebra/runtime regressions, not a claim about native cryptographic fields,
hashes, nontrivial-round empirical security or a 128-bit parameter certificate.

The next integration must use this actual selector as the staged native PCS
query phase, with its computed acceptance gate, actual returned opening memory
and `RepeatedLookupSelector.packets` as the enforced lookup opening family.
The same selected-pair event and exact final packet must be retained through
the source/helper witnesses and final PCS flags. Pair-vector sampling and
multiplicities/source provenance must precede helper/EQ/algebra at the correct
times; condition on the source/pair prefixes to select a nonpassing index or
pay the all-pairs-pass bound. The generic callback's remaining opening failure
cannot be dropped until instantiated with `LookupGroupedOpening` on that exact
complete run. Deferred/global PBS collection, native rejection sampling,
honest cryptographic openings/scheduler completion, Rust/bytes/Fiat–Shamir,
full PBS and the final concrete unbudgeted 128-bit expected-work theorem remain
open. The overall proof objective stays active.

Validation for this repeated-selector milestone passed: focused HasteBoots
build, strict warning-as-error HasteBoots smoke, full `scripts/check` (10,013
build jobs and all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-repeated-smoke-build.log`,
`/tmp/hasteboots-repeated-strict-smoke.log`, and
`/tmp/hasteboots-repeated-check.log`. All 950 guarded transitive axiom audits
use subsets of `propext`, `Classical.choice` and `Quot.sound`; no custom axioms,
admitted proofs or compiled proof shortcuts were introduced. The Rust worktree
is unchanged at `dff353006322693cab3dc6b654f82151f658f294`. The full formal
security objective remains active.


The integrated repeated-selector/staged-PCS milestone adds six guarded axiom
audits, bringing the total to 956. `RepeatedLookupPCS.program` directly runs
the canonical repeated selector, gates native root opening on its computed
acceptance, starts opening with its actual returned memory, and uses its own
packet projection to construct the enforced original-root query/value family.
There is no caller-supplied gate, replacement opening memory or unrelated
packet family at this interface. Helpers open before sources in canonical
trusted index order. The selected-pair raw event and projected packet are
retained on the same actual shared execution through native PCS verification.
Its reduction proves final acceptance implies the selected scalar event,
native PCS arithmetic or the one global availability exception. Native PCS
arithmetic is bounded internally using the real root verifier, rather than an
assumed commitment/PCS/replay certificate.

`RepeatedLookupPCSAlgebra` provides concrete native support and probability
facts for both modes: degree four partial tables and degree three full tables.
The full branch explicitly requires the public logical length to equal the
whole scalar domain. Native public-table totals, prepared packet checking and
private sumcheck/EQ arithmetic derive the local interfaces inside Lean. A
small schedule-data record carries prover callbacks, supplied claims and
initial memory; it does not contain a security certificate. The native lookup
extension K and the separate PCS analysis alphabet L keep their distinct bases
and dimensions in the complete bounds.

`StagedRepeatedLookup` places that entire runtime after the two actual root
recordings. Source tables are decoded only from the pre-middle source
snapshots. Multiplicities are a function of the original source emission,
so the verifier cannot select them using later helper metadata. The already
selected pair vector is projected from the helper emission before any algebra
coins; its nonzero offset is a structural typed challenge property, not a
uniform-sampling or Fiat–Shamir law. Helpers are decoded only from their own
later snapshots. No equality of early/late decoded source words is assumed.
Checkpoint membership and root identity follow from actual source recording,
history preservation through middle work and helper recording.

For fixed prefix data outside the all-pairs-pass event, analysis chooses a
nonpassing index before any algebra coins. This index is never passed to the
runtime. The actual verifier still executes all pairs in native order and
stops on rejection. Its selected scalar event costs n/card(K)+n*D/card(K),
D=4 partial or D=3 full, without a repetition multiplier. The complete
`bad_prefix_bound` theorem derives that scalar loss plus the actual per-root
PCS error sum and one expected availability charge for the complete source,
middle, algebra and opening program from the empty state. All native scalar,
packet-provenance and root-authentication interfaces are discharged. It
assumes no local EQ, sumcheck, PCS, replay, initial safety or query-budget
security certificate. Trusted code geometry, capacity/distance, bases,
uniform primitive samplers and public full-length consistency remain explicit.

`acceptance_bound` then bounds total acceptance by the explicit probability
that all fixed pairs pass, plus those scalar/PCS/work terms. The remaining
all-pairs-pass term is evaluated on this same complete witness. It has not
been replaced by a conjectured private pair law or an unproved Fiat–Shamir
compiler. A malicious or otherwise arbitrary middle program can therefore
make that term large; the theorem does not silently claim 128-bit soundness
without proving the actual sampler and false-statement relation.

The integrated runtime regression uses three actual zero-round prepared pair
verifiers and then the first helper's real native PCS step. The selector's
successful private memory determines which cached hash PCS preparation uses;
the computed missing-column rejection then prevents all later helper/source
roots. The test checks selector success, final PCS rejection, exactly the
first helper index in the attempted-root trace, the returned memory, all five
issued hashes in the eight-entry log, and all four passive root recordings.
The behavior factory's dummy root/query/value fields are overridden by trusted
bindings. The F17 warm-cache fixture is a control-flow/work regression, not a
native hash/extension-field implementation or 128-bit parameter certificate.

The next main proof task is implementing the actual private pair-vector
middle program, retaining its sampled vector through helper commitment and
proving its all-pairs-pass bound against the frozen original source tables and
multiplicities. Preserve the original false-lookup relation and characteristic
constraints. This remains typed ideal-private-oracle semantics: native
transcript binding and child/parent finishing calls, exact primitive-call
placement (including zero-round boundaries), field/byte encodings, rejection
sampling and Rust/Fiat–Shamir refinement must still be verified before
exporting a full native work theorem. Honest cryptographic opening/scheduler
completion, deferred/global PBS collection, full application/knowledge and PBS
composition, and the final concrete unbudgeted 128-bit expected-work theorem
remain open. The overall objective stays active.

Validation for the integrated staged PCS milestone passed: focused HasteBoots
build, strict warning-as-error HasteBoots smoke, full `scripts/check` (10,017
build jobs and all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-staged-pcs-smoke-build.log`,
`/tmp/hasteboots-staged-pcs-strict-smoke.log`, and
`/tmp/hasteboots-staged-pcs-check.log`. All 956 guarded transitive axiom audits
remain subsets of `propext`, `Classical.choice` and `Quot.sound`. No custom
axioms, admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged at `dff353006322693cab3dc6b654f82151f658f294`.
The full formal security objective remains active.


## Ideal private pair-vector law integrated with staged native lookup/PCS

`LookupPairVector` attaches support proofs to the existing optional pair
sampler, proving that every supported result succeeds with a nonzero offset
when `size + 1 < card(K)`. Its erasure is equality of oracle programs, rather
than an assumed distribution certificate: there is no added draw, retry,
fallback or postselection. The first coordinate remains the original uniform
tuple-hash challenge; the offset retains its challenge-dependent public
accepted domain. The two coordinates are not asserted independent.

The vector program draws every pair afresh in the actual repetition order.
Its exact all-pass probability is the single-pair probability raised to the
true repetition count. `vector_bound` derives the existing combined tuple-hash
and reciprocal-domain loss to that power, retaining both losses and the
explicit characteristic condition on the number of active original tuples.
Packing width does not replace the repetition count.

`LookupPairVectorMiddle` runs that private vector before arbitrary helper
construction on the same shared handler. The trusted wrapper retains the
actual vector after the builder returns roots and opaque memory. Helper code
cannot substitute a vector in that trusted slot; its hashes and other shared
work remain in the execution. Its staged bound averages over the actual
source prefix and retains the all-pass event through all subsequent work,
including aborts. It requires neither independence of helper behavior nor a
caller-supplied sampling certificate.

`FrozenLookupSources.tuples` accepts only the original source emission and its
saved source state. It takes no helper state, pair vector or later query
argument. `allPass_iff` proves by definitional equality that the existing
staged lookup predicate uses precisely these original decoded tuples. No
source snapshot is moved to the helper or opening prefix. Multiplicities
remain a function of the original source emission.

`StagedPrivateLookup.false_acceptance_bound` combines this actual middle
program, the repeated native algebra selector and native grouped PCS. Its
false event is nonmembership of at least one active original decoded lookup
tuple in the fixed public table. The bound is the combined pair error to the
repetition count, plus the selected scalar error, the per-root PCS error sum,
and one expected availability charge on the entire source/middle/algebra/PCS
program from the empty state. The same retained vector is passed into the
actual algebra verifier. Lookup field K and PCS analysis alphabet L remain
separate. All pair, scalar, packet-provenance and PCS/authentication probability
interfaces in this theorem are derived internally.

This closes the ideal private pair-vector integration task listed above.
It does not establish that a false PBS application necessarily yields this
false lookup event; application composition remains open. Nor does equality
of the ideal accepted-domain samplers identify the production rejection loop
or its work. Native rejection-loop sampling, exact transcript and primitive
call placement, field/byte encodings, Fiat–Shamir and Rust refinement remain
open. Honest cryptographic opening/scheduler completion, deferred/global PBS,
application/knowledge and full PBS composition, and the final concrete
unbudgeted 128-bit expected-work theorem still remain open. The overall
objective stays active.

New regressions check exact sampler erasure, the true fresh-vector repetition
bound, vacuous all-pass at zero repetitions, and arbitrary helper work. In the
shared-handler fixture the builder returns a forged vector plus a rejecting
flag in opaque memory and makes a cached hash call. The trusted vector still
has exactly its original fresh-sampling program, the returned opaque memory
is preserved, and the final log contains the additional issued hash. This is
a control-flow/work regression over F17, not a native 128-bit parameter claim.

Validation passed for this milestone: focused HasteBoots build, strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,022 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-staged-private-smoke-build.log`,
`/tmp/hasteboots-staged-private-strict-smoke.log`, and
`/tmp/hasteboots-staged-private-check.log`. All 969 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The full formal security objective
remains active.


## Ideal reciprocal rejection loop: operational limiting law and candidate work

`RejectionSampling.runPrefix` implements fresh candidate draws and the real
accept/retry branch over a finite accepted domain. The result retains the
entire ordered candidate list, including rejected candidates. `none` denotes
suspension at the next draw, with all prior work retained; it is not a verifier
rejection or an imposed native retry budget. Every natural prefix length is
an analysis approximation to the same unbounded loop.

For rejected fraction rho, the suspended mass after n attempts is exactly
rho^n. Successful event mass is the sum of rho^i times the first-draw hit
probability for i<n. The successful-event probabilities are monotone in the
prefix length and converge to uniform selection on the accepted domain.
`eventProbability_eq_uniform` identifies their supremum with the existing
optional accepted-domain sampler, including the empty-domain failure case.
`success_tends_to_uniform` proves convergence of the actual operational event
laws. Nonempty accepted domains have rho<1 and vanishing suspended mass.
No pathwise retry bound or empirical maximum is assumed.

`expectedAttempts` integrates the actual retained trace length, counting every
attempt on success and suspension alike. Its recurrence is 1 plus rho times
the suffix expectation. Its exact value on a prefix is the finite geometric
sum, and its monotone unbounded limit is card(A)/accepted.card. Empty domains
have infinite expected attempts, rather than silently returning a dummy value
or zero work. Nonempty domains have finite unbounded expected attempts.

`ReciprocalRejection` specializes the loop to exactly the zero/public-table
pole predicate in `HasteBoots/snarks/src/packed_extension_lookup.rs::challenges`.
Its marginal output law agrees with `ReciprocalDetection.sample`, the ideal
law used by `StagedPrivateLookup`. The exact expected field-candidate count
uses the actual number of distinct allowed values. The derived public upper
bound is q/(q-size-1), using the proved distinct-exclusion bound; repeated
public hashes do not inflate the exact cost. Every operational prefix embeds
as private shared work with the incoming hash/cache/checkpoint state unchanged.

This supplies the ideal reciprocal retry law and candidate-count analysis,
not a full native work refinement. The staged lookup theorem still runs its
accepted-domain sampler. A trace-aware joint refinement of retries, helper
construction and child/parent transcript state is required before replacing
that whole operational execution. Equality of the marginal accepted values
does not equate transcript states or discard rejected-draw work. Canonical
byte-to-field rejection in `helper/src/classical_transcript.rs::field_build`,
exact primitive/hash costs, transcript binding, Fiat–Shamir and Rust refinement
remain open. Honest cryptographic opening/scheduler completion, deferred/global
PBS, application/knowledge and full PBS composition, and the final concrete
unbudgeted 128-bit expected-work theorem also remain open. The full objective
stays active.

New regressions check a rejected fraction 3/4: three attempts have suspended
mass 27/64, successful mass 37/64 and expected attempted-candidate count 37/16;
the unbounded expected count is four. They also cover zero-length prefixes,
empty domains, all-accepted domains and the actual shared-state preservation
bridge. A deterministic response tape executes two rejected draws followed
by acceptance, preserving their order and leaving the next response unused;
suspending the same tape earlier retains both issued candidates. Over F17,
three repeated zero poles give the exact expected count 17/16 while the public
size-only bound remains 17/13. These are ideal probability/work regressions,
not a production sampler or 128-bit parameter certificate.

Validation passed: focused HasteBoots build, strict warning-as-error
HasteBoots smoke, full `scripts/check` (10,026 build jobs and all strict
regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-rejection-smoke-build.log`,
`/tmp/hasteboots-rejection-strict-smoke.log`, and
`/tmp/hasteboots-rejection-check.log`. All 992 guarded transitive axiom audits
remain subsets of `propext`, `Classical.choice` and `Quot.sound`. No custom
axioms, admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged at `dff353006322693cab3dc6b654f82151f658f294`.
The full formal security objective remains active.


## Canonical raw-byte sampler: direct native guard, limiting law and byte cost

`CanonicalByteMask` models increasing byte addresses by increasing powers of
256 and proves the little-endian decoding sum. Its explicit high/low-bit
bijection retains all discarded high bits and proves that masking fresh
uniform bytes gives a uniform value below 2^bits. The mask is the native
bitwise AND with 2^bits-1; it is not reduction modulo the characteristic.
Zero-padding an unread scratch suffix preserves the decoded word, and the
16-byte scratch word stays within the u128 range.

`CanonicalByteSampler` sets bits to the bit length of p-1 and byteCount to
(bits+7)/8, matching `helper/src/transcript.rs::CanonicalSampler`. Its actual
`runPrefix` draws raw byte chunks, decodes and masks them, directly compares
the result with p, and retries on failure. It retains all raw chunks,
including those rejected after masking, in their original order. It does not
implement the comparison by enumerating a finite accepted set. `runPrefix_eq`
proves exact oracle-program equality with the generic rejection analysis,
without extra draws, filtering or postselection. Generic `returned_mem` and
specialized `returned_canonical` prove that each actually returned value
satisfies the below-modulus guard, independently of probability claims.

For p>1, the derived bit range contains p and is strictly smaller than 2p.
When p fits a u128, the byte width fits the native 16-byte scratch array. The
explicit full-width mask branch avoids shifting by 128. `nativeCandidate_eq`
proves that decoding the zero-initialized full scratch array and taking that
branch gives exactly the candidate used by the operational comparison.
These are bounded natural/byte reference semantics; full Rust integer/array
refinement is still a separate obligation.

The limiting successful-value law is uniform on canonical `Fin p` values,
and `uniform_zmod` transports it to the residue ring by the proved canonical
representative map. Primality is needed for its field structure, not for this
sampling law. Successful operational event laws converge to that uniform
law; suspended prefixes contribute no successful value. The all-zero raw
chunk establishes nonemptiness, so the suspension probability vanishes with
no retry cap. The proof derives these laws from raw-byte masking and the
actual retry programs, without a caller-supplied uniformity certificate.

`consumedBytes` counts byteCount times the length of the actual retained raw
trace. `expectedBytes_eq` integrates that observation and identifies it with
the corresponding candidate expectation. The monotone unbounded limit is
byteCount * 2^bits/p, strictly below 2*byteCount for a valid characteristic.
The proof includes every attempted read on success and suspension; it uses
all operational prefixes, rather than an observed maximum or a protocol
budget. The new generic normalization theorem derives hit-event ratios from
those operational prefixes.

Regressions exercise real byte-query paths. With p=17, raw bytes 255 and 49
mask to rejected values 31 and 17, then 144 masks to accepted value 16. Their
raw trace is retained and the subsequent byte remains unused. Modulo-p
reduction would incorrectly accept the first raw byte. A shorter prefix
suspends with both rejected chunks retained. A two-byte p=257 path decodes
bytes [1,2] as 513, masks the unused high bits to obtain accepted value one,
charges two consumed bytes and preserves the next byte. Additional checks
cover zero-padding, the full 128-bit mask branch and the power-of-two p=2
edge case. Concrete profile checks give Goldilocks bits=64/bytes=8 and
BabyBear bits=31/bytes=4, retaining their exact expected byte formulas.

This closes the canonical mask/retry law and byte-count part of ideal byte
sampling. It does not identify the complete native field-challenge stream.
Production XOF blocks and readers, variable-length consumed-byte receipts,
labels/descriptors and child/parent transcript binding remain open. Joint
trace-aware composition of canonical coefficient draws, extension-field
assembly, reciprocal retries and adaptive helper construction remains open;
equality of marginal accepted values alone cannot discard those traces or
identify later transcript states. Transfer to actual primitive hash work,
Fiat–Shamir and Rust refinement, honest cryptographic opening/scheduler
completion, deferred/global PBS, application/knowledge and full PBS
composition, and the final concrete unbudgeted 128-bit expected-work theorem
also remain open. The overall objective stays active.

Validation passed for this milestone: focused HasteBoots build, strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,025 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-byte-sampler-smoke-build.log`,
`/tmp/hasteboots-byte-sampler-strict-smoke.log`, and
`/tmp/hasteboots-byte-sampler-check.log`. All 1,028 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The full formal security objective
remains active.


## Sequential coefficients, pure extension assembly and trace-aware continuation

The new generic `RejectionSampling.success_scaled` theorem derives each
finite prefix's successful value law as its actual completion mass times its
limiting accepted-domain law. It does not normalize away unfinished draws.
`OptionalUniformSequence` proves the successful tuple law for the actual
sequential optional control flow, stopping on the first suspended sample.
Its single-draw law is a technical interface; the canonical-byte wrapper
derives that interface internally from the proved raw-byte sampler.

`CanonicalCoefficientVector.program` fills coefficients in increasing index
order. It retains an optional complete vector, the list of all completed
canonical coefficients, and every raw byte chunk in order. Suspending a later
coefficient preserves earlier accepted values and the current rejected raw
chunks, and skips the remaining coefficients. Exact oracle-program erasure
to the optional sequence keeps all issued byte queries and the same control
flow; it erases observation fields, not execution work.

The canonical scalar law is derived from the direct raw-byte retry program,
including its real completion probability a_f for prefix length f. The joint
successful coefficient-vector law is a_f^c times the uniform c-coordinate
law. This exponent counts completion of c scalar draws; it is not a security
amplification factor or a substitute for the true lookup repetition count.
The coefficient law and completion mass have monotone limits, yielding the
full uniform joint law for the unbounded sequential sampler. No independence
or field-sampling security certificate is supplied by the caller.

`CanonicalCoefficientWork` integrates the complete retained byte trace. Its
recurrence is E_f(c+1) = E_single(f) + a_f*E_f(c): every started coefficient
incurs its actual bytes, while the suffix starts only after head completion.
The monotone unbounded limit is c times the canonical single-coefficient
byte cost. The closed formula retains c, the native byte width, bit range and
characteristic explicitly. All work before suspension is included, with no
pathwise retry maximum or protocol sampling budget.

`CanonicalExtensionSampler` fills count*degree flat coefficients before pure
field assembly. Its getter uses the native offset element*degree+coordinate.
A proved mathematical basis gives an explicit bijection between flat scalar
coordinates and the requested field vector. Repeated or reordered coordinate
reads cannot resample scalars. The runtime retains the complete raw
coefficient result alongside its optional assembled values; exact raw erasure
recovers the actual coefficient program. Finite-prefix field-vector laws,
unbounded joint uniformity and the exact raw-byte cost follow internally.
The actual extension degree stays separate from PCS packing/analysis width.

The shared-handler theorem preserves the incoming hash/cache/checkpoint state
through the private byte/assembly prefix. `retained_bound` then allows an
arbitrary continuation to inspect the entire earlier result, including raw
retry traces and partial accepted coefficients. All later shared queries
remain in the actual complete execution. A fixed earlier field-value event
cannot gain probability through that work; no equality of transcript states
or erasure of observable traces is assumed.

The assembly core models execution after native trusted-profile, degree and
size validation. Matching its basis/getter with the concrete Rust extension
constructor, multiplication-table descriptors and validation/overflow checks
remains open. XOF readers and blocks, byte-consumption receipts, labels and
child/parent transcript binding, full joint composition with reciprocal
retries and adaptive lookup helpers, and transfer to actual primitive hash
work remain open. Zero requested elements read no scalar bytes here, but
native zero-element identity phases still require their framing/hash proof.
Fiat–Shamir and Rust refinement, honest cryptographic opening/scheduler
completion, deferred/global PBS, application/knowledge and full PBS
composition, and the final concrete unbudgeted 128-bit expected-work theorem
also remain open. The complete objective stays active.

Regressions execute the real sequential byte-query paths, including rejected
chunks before the first accepted coefficient, suspension during a later
coefficient with the first accepted value preserved, skipping still later
coefficients, and zero-element requests. F17 one-attempt prefixes have actual
completion mass 17/32; two requested coefficients retain its square in their
successful mass and incur expected bytes 1+17/32. Their unbounded vector law
has singleton mass 1/289 and total expected bytes 2*(32/17). Lookup-degree
profile checks use three Goldilocks coefficients or six BabyBear coefficients,
retaining exact byte formulas rather than substituting PCS widths four/eight.

A pure coordinate-order fixture reads coordinates repeatedly and out of order
without consuming another byte. A shared-handler fixture gives two accepted
raw bytes, 16 and 144, the same canonical value 16. Their distinct retained
raw traces cause the adaptive callback to choose different cached leaf
hashes. Both real hash calls remain in the final log and the next byte is
unused. This demonstrates why marginal accepted-value equality alone cannot
replace trace-aware native execution. The product-module coordinate fixture
is not a concrete native extension field or a 128-bit parameter certificate.

Validation passed for this milestone: focused HasteBoots build, strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,032 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-extension-sampler-smoke-build.log`,
`/tmp/hasteboots-extension-sampler-strict-smoke.log`, and
`/tmp/hasteboots-extension-sampler-check.log`. All 1,058 guarded transitive
axiom audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The full formal security objective
remains active.


## Byte-backed reciprocal retries: nested law, partial work and unbounded cost

`OptionalUniformSequence.bind_probability` extends the scaled optional value
law through arbitrary continuations while keeping incomplete mass.
`RejectionSampling.one_step_probability` supplies the full uniform trial's
accept/retry decomposition. These are technical interfaces; the byte-backed
factory derives its field-trial law internally rather than accepting a
sampling or security certificate from the caller.

`OptionalRejectionLoop` retains a complete list of trial observations. A
completed rejected candidate starts the next trial; an unfinished inner field
sample suspends with its observation retained and starts no further trial.
The value projection preserves the exact oracle program. Returned-value
support proves actual acceptance by the supplied direct predicate. Finite
successful laws retain both the field completion factor and the reciprocal
rejection factor, and are dominated by the full accepted-domain law without
normalizing away suspension.

`OptionalRejectionWork` sums the actual work of every retained trial. The head
is always charged, including a partially completed last field sample. For
field completion mass beta, full-field rejected fraction rho and actual mean
head cost C, an outer prefix of length m costs
C * sum_{i<m}(beta*rho)^i. Its successful event mass is
sum_{i<m}(beta*rho)^i * beta * h_event, where h_event is the full uniform
field draw's accepted-event probability. These recurrences require no
cost/value independence assumption: all head work is included before its
value/completion test, while only a completed rejection starts the fresh
suffix.

`ByteReciprocalSampler` instantiates this control flow with the actual
canonical-byte extension program. Each trial retains its optional assembled
field value and complete raw coefficient observation. The reciprocal test is
directly r!=0 and every r+table[i]!=0, with a computable predicate; it does not
enumerate the field at runtime. A support theorem proves that every returned
offset passed both tests. The analysis finite set is proved equal to
`ReciprocalDetection.allowed`. Every finite inner/outer approximation is
bounded by the ideal accepted-domain event law, with no protocol retry cap.

The private shared-state theorem retains the incoming hash/cache/checkpoints
and all nested trial observations. An arbitrary later continuation can inspect
those full observations, including the partially sampled last trial. All of
its actual shared queries remain in the complete execution, and cannot
increase a fixed earlier accepted-offset event. This is not an erasure of
observable retry metadata or an equality of native transcript states.

`ByteReciprocalLimit` takes all inner coefficient and outer reciprocal
approximations. Successful event probabilities are monotone in both depths.
For each fixed outer prefix the inner limit recovers the full uniform-field
rejection prefix. The outer limit therefore has exactly the accepted-domain
law already used by the staged lookup theorem. Nonempty trusted domains have
full eventual successful mass. Work retains all partial-trial bytes through
the same limiting construction, giving the exact unbounded cost
C_field * card(K)/allowed.card, where C_field is the derived full canonical
extension-draw byte cost. The public bound is
C_field * card(K)/(card(K)-tableSize-1). Duplicate poles affect the exact
allowed cardinality, rather than being charged repeatedly as distinct poles.
No empirical maximum or pathwise sampling budget is assumed.

These are fixed-table reciprocal results. They do not assert independence of
the tuple-hash and reciprocal coordinates: the actual public pole table may
depend on the preceding tuple-hash challenge. Full raw-byte tuple-pair and
repetition composition, and its trusted integration with the staged source/
helper/algebra/PCS execution, remain open. The staged verifier still uses its
ideal accepted-domain pair program. Production XOF readers/blocks, receipts,
labels and child/parent transcript binding, concrete Rust field constructor,
basis/descriptor and metadata validation, and transfer from byte consumption
to actual primitive hash work also remain open. Fiat–Shamir and Rust
refinement, honest cryptographic opening/scheduler completion, deferred/global
PBS, application/knowledge and full PBS composition, and the final concrete
unbudgeted 128-bit expected-work theorem remain open. The overall objective
stays active.

The F17 runtime regressions exercise zero exclusion, the nonzero public-table
pole at r=16, canonical-byte rejection of 255/49, and later acceptance of five.
All raw chunks and complete field-trial observations stay in their original
order. A shorter inner approximation suspends inside the third field trial
and skips the fourth; a shorter outer approximation retains its completed
rejected trials and leaves the next byte unused. Zero-depth cases distinguish
no started outer trial from a started but internally suspended trial.

With one inner attempt the actual completion mass is 17/32, and the full-field
rejected fraction is 2/17. The real restart probability is their product
1/16, giving two outer trials expected bytes 1+1/16. The unbounded accepted
singleton law is 1/15 and its expected byte cost is 32/15. Three repeated zero
poles instead give exact total bytes two. A shared-handler regression lets
the continuation inspect the retained rejected trial, make its real cached
hash call, and preserve the already sampled offset and next unused byte.
These fixtures test ideal byte/control/work semantics, not a native 128-bit
parameter or XOF security certificate.

Validation passed: focused HasteBoots build, strict warning-as-error
HasteBoots smoke, full `scripts/check` (10,033 build jobs and all strict
regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-byte-reciprocal-smoke-build.log`,
`/tmp/hasteboots-byte-reciprocal-strict-smoke.log`, and
`/tmp/hasteboots-byte-reciprocal-check.log`. All 1,099 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The complete formal security
objective remains active.


## Raw-byte joint pair law and domain-dependent work

`ByteLookupPairSampler` now runs the first raw-byte field sampler, fixes the
hashed public table from that actual challenge, and only then starts the
reciprocal rejection loop. Its result retains the complete first draw and,
when started, the complete reciprocal observation including rejected and
partial trials. An unfinished first challenge starts no reciprocal trial.
Metadata erasure is equality of query programs, not merely equality of event
probabilities. Supported successful pairs retain the sampled first challenge
and pass the reciprocal exclusions for that exact hashed table.

The finite pair law is the first draw's completion mass times a uniform
average of the **challenge-dependent** reciprocal prefix probabilities.
There is no assertion that the coordinates are independent or that finite
pair completion has one challenge-independent normalization factor. Every
finite approximation is bounded by the existing joint ideal pair law and
inherits both original single-pair lookup losses. Arbitrary later shared
work may inspect both raw observations; its actual execution remains while
a fixed earlier pair event remains bounded by the same ideal pair event.

`ByteLookupPairLimit` takes all first-challenge, inner coefficient and outer
reciprocal approximations. It proves equality with `TupleLookupPair.sample`,
using finite sums commuting with increasing approximations. A sufficiently
large field gives eventual successful pair mass one. No approximation depth
is made into a protocol retry cap.

`ByteLookupPairWork` charges all first-challenge bytes on every outcome and
all reciprocal bytes when the first challenge has completed. Its exact finite
mean is the unconditional first-draw cost plus the first-draw completion mass
times the uniform average of actual reciprocal-prefix costs. The unbounded
cost is

```
fieldCost + average_y [fieldCost * card(K) / card(allowed(hashes(table, y)))]
```

The public upper bound is
`fieldCost * (1 + card(K)/(card(K)-size-1))`. The exact law retains collisions,
duplicate poles and the exclusion of zero; it does not replace the actual
domains by the size bound. No cost/value independence is assumed. The generic
`OptionalUniformSequence.successful_expectation` lemma transports arbitrary
nonnegative observations through a successful optional kernel without
conditioning away its unfinished mass.

F17 regressions use rows `(0,1)` and `(1,0)`, whose hashes are y and one. The
allowed domain has size fifteen at y=1 and fourteen at y=2. Offset fifteen
succeeds at y=1 and is rejected at y=2. Tests retain the first draw's rejected
bytes, all reciprocal candidates and partial raw chunks, distinguish no
started reciprocal loop from a started suspended one, and check the next
unused byte. The finite reciprocal completion factors differ between these
challenges. Zero-depth and zero-outer cases also check the actual byte mean.

This closes the fresh ideal-byte **single pair** composition gap. The staged
verifier still uses the ideal accepted-domain pair vector; actual byte-backed
repetition, its retained vector/work law, and trusted staged integration are
next obligations. Production XOF/transcript/Rust refinement, concrete field
constructor/basis/metadata validation and conversion from byte consumption
to actual primitive hash work remain open. Honest cryptographic opening and
scheduler completion, deferred/global PBS, application/knowledge composition,
and the final concrete unbudgeted 128-bit expected-work theorem remain open.
These sampling laws do not equate a marginal challenge distribution with the
whole native Fiat–Shamir execution. The complete objective remains active.

Validation passed: focused HasteBoots build (3,940 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,039 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-byte-pair-smoke-build.log`,
`/tmp/hasteboots-byte-pair-strict-smoke.log`, and
`/tmp/hasteboots-byte-pair-check.log`. All 1,116 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The complete formal security
objective remains active.


## Repeated raw-byte pairs with retained work

`ObservedOptionalVector` is a fresh-call vector program for an arbitrary
optional observed sampler. It assumes no scaled uniform kernel. Each call
retains its full observation; suspension stops later calls and retains the
completed value list and the final partial observation. Its optional view is
an exact erasure of the query program, including the suspension gate. The
successful all-coordinate event probability is the actual single-call event
mass raised to the requested count. Supported completed vectors inherit any
property proved for every supported successful single call.

Its work observation sums the real costs of all started calls. The exact
recurrence is `mean(count+1) = singleMean + completion * mean(count)`, including
the current call's cost even on suspension. The resulting finite mean is the
single-call mean times the geometric prefix sum of actual successful
completion mass. No cost/value independence or conditioning on success is
used in these statements.

`ByteLookupPairDiagonal` proves that increasing one common analysis depth is
cofinal in all three raw-byte pair-prefix depths. It proves monotonicity and
convergence of successful event probabilities and unconditional byte means.
A common depth is an analysis approximation, not a native retry budget.

`ByteLookupPairVector` instantiates the observed-vector program with the
actual raw-byte pair program. Every repetition draws a fresh hash challenge
and samples its offset against that challenge's hashed public table. The
finite all-pass law is the actual successful single-pair pass mass to the
true repetition count; no independence between the two coordinates of one
pair is inserted. Both original lookup losses therefore amplify to
`TupleLookupPair.error(...) ^ repetitions`. Completing all operational
approximations recovers the existing repeated lookup **all-pass event** law.
The theorem is explicitly an all-coordinate-event law, not an asserted
arbitrary-vector/transcript distribution equivalence.

A sufficiently large field gives eventual completion mass one. Exact
unbounded bytes are the single pair's true domain-dependent average byte
mean times the repetition count. The public upper bound is consequently

```
fieldCost * (1 + card(K)/(card(K)-size-1)) * repetitions
```

The zero-repetition case is handled separately, without assuming finiteness
to justify a product limit at zero. All completed offsets are proved nonzero
from the support of the actual byte programs. An arbitrary later shared
continuation may inspect all retained observations and make its real hash
queries; the fixed earlier all-pass event is still bounded by the same
repeated lookup error.

Native source correspondence was rechecked in
`HasteBoots/snarks/src/packed_extension_lookup.rs:639` and
`HasteBoots/snarks/src/packed_tuple_lookup.rs:397`: their challenge loops
sample y, hash the fixed table, and perform reciprocal exclusions before
starting the next repetition. Transcript labels, XOF reader state and child/
parent linking are not equated with the fresh ideal-byte syntax by this
control-flow correspondence.

F17 runtime tests run three different hash challenges and their corresponding
reciprocal domains in order, retaining rejected offsets and all eight raw
bytes. Separate tests suspend the second repetition during Y or inside the
reciprocal field sampler; the first completed pair and every partial raw
chunk remain, the third repetition is skipped, and the next unused bytes
remain on the input tape. Zero repetitions completes an empty vector without
queries, while a zero outer reciprocal approximation suspends after charging
the first Y. Tests also exercise the concrete false-source repeated bound,
eventual successful mass, and exact repeated-byte-mean factor.

The remaining immediate integration is proof-only attachment of these actual
successful vectors to the typed nonzero-offset interface, followed by the
trusted helper wrapper and staged source/helper/algebra/PCS execution. A
suspended approximation must stay suspended: it cannot supply a fallback
vector or resample after helper work. Production XOF/transcript/Rust
refinement, concrete field constructor/basis/metadata validation, transfer
from byte consumption to primitive hash work, honest opening and scheduler
completion, deferred/global PBS, application/knowledge and full PBS
composition, and the final concrete unbudgeted 128-bit expected-work theorem
remain open. The complete objective remains active.

Validation passed: focused HasteBoots build (3,943 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,040 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-byte-vector-smoke-build.log`,
`/tmp/hasteboots-byte-vector-strict-smoke.log`, and
`/tmp/hasteboots-byte-vector-check.log`. All 1,145 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The complete formal security
objective remains active.


## Typed byte vectors and the original-source helper phase

`ByteLookupPairTyped` attaches the nonzero-offset proofs already derived from
support of the actual byte-backed vector program. The result stores both the
full raw observation and an optional typed vector, with a proof that erasing
the vector's types gives exactly the raw optional values. Erasing the complete
typed sample recovers the original oracle query program. Every finite
successful-vector event and the actual consumed-byte mean are preserved.
There is no postselection, replacement draw or fallback on suspension.

`ByteLookupPairMiddle` runs that typed byte program before arbitrary helper
construction. The builder can inspect every complete and partial raw trace
and the actual typed vector; it supplies only helper roots and opaque memory.
The trusted `completed` view attaches the stored vector afterwards, with
proved provenance back to the original raw-byte values. A vector placed by
the builder inside its opaque memory cannot replace the verifier's vector.

An unfinished vector starts no helper work. Its completed helper view is
absent, its root-request list is empty, and `continueWith` starts no subsequent
verifier work. The emission still stores every completed pair and partial raw
chunk. Both suspension and completion therefore preserve the real sampling
work rather than manufacturing a valid verifier input or aborting away the
observation.

The helper-retained all-pass bound follows from the actual finite byte-vector
bound and the shared continuation theorem. Its staged version averages over
arbitrary original source prefixes, with source tuples and multiplicities
fixed before all byte sampling. The real helper and later shared executions
remain in that theorem.

`StagedByteLookup` specializes this to the actual original-source extraction
and native lookup pass predicate. Its `allPass_iff` is definitional: the
original source tuples are decoded only from the first saved source state,
never from the helper state or a later query-dependent state. The resulting
`allPass_bound` applies to the actual byte-backed helper program and records
helper roots only for completed emissions. Both the canonical-byte assembly
basis over `ZMod p` and the lookup basis over F are explicit; this does not
claim a concrete Rust field/basis/metadata-validation certificate.

The runtime fixtures exercise proof-only typing of two completed pairs and
suspension inside the second repetition. A helper builder observes actual
byte work, makes a cached shared hash query, and returns a different vector
inside opaque memory. The completed verifier input still contains the
original sampled pairs and preserves the helper's actual hash log. A staged
fixture preserves source/hash-prefix length three, helper length four, and
later verifier length five in order; its verifier receives that same vector.
The suspended counterpart keeps all three saved hash-prefix lengths at three,
retains the first completed pair and all four consumed bytes, and skips both
the helper query and the later verifier query. The next unused bytes remain
on the scripted input tape.

The immediate remaining proof is composition of this optional completed helper
view with native algebra/PCS acceptance and its one complete-run availability
charge. The existing `StagedPrivateLookup.false_acceptance_bound` still uses
the ideal accepted-domain vector; it has not been silently identified with a
byte-backed execution. The new theorems bound the actual byte-backed all-pass
event. Full native XOF/transcript/Rust refinement, concrete field constructor/
basis/metadata validation, conversion of byte consumption to primitive hash
work, honest cryptographic opening and scheduler completion, deferred/global
PBS, application/knowledge and full PBS composition, and the final concrete
unbudgeted 128-bit expected-work theorem remain open. The complete objective
remains active.

Validation passed: focused HasteBoots build (3,946 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,045 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-byte-typed-middle-smoke-build.log`,
`/tmp/hasteboots-byte-typed-middle-strict-smoke.log`, and
`/tmp/hasteboots-byte-typed-middle-check.log`. All 1,163 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The complete formal security
objective remains active.


## Byte-backed helper phase composed with native algebra and PCS acceptance

`StagedLookupPrefixFacts` factors the actual native scalar/PCS arithmetic
bound and supported-acceptance reduction at two fixed prefixes. Both local
interfaces are proved from `RepeatedLookupPCSAlgebra.facts` and the native
repeated selector/grouped-PCS theorems; no caller-supplied arithmetic or PCS
certificate is introduced. Its snapshot theorem retains the original source
checkpoint through an arbitrary real middle program, then records the actual
completed helper roots. The middle program need not produce a concrete helper
emission when sampling is suspended.

`OptionalStagedLookup` runs the original native continuation only when the
middle program has an actual completed helper view. Its suspension branch
records no helper roots and executes no native algebra or PCS query. Its
completed branch is exact query-program equality with the original native
continuation, using that helper and the behavior selected from the actual
middle result. Algebra and PCS behavior may inspect retained raw sampling
metadata before their own coins; the theorem does not impose an independence
certificate between that metadata and later prover behavior.

Its `bad_prefix_bound` proves native acceptance outside all-pass at most the
native scalar error plus the original per-root PCS error sum and **one**
complete-run `ExpectedHazard.charge`. The charge uses the actual source,
middle and optional continuation program. It retains earlier raw-byte queries,
rejected and partial samples, all middle queries, and the actual later algebra
and opening work. The proof never assigns separate availability charges to
byte retries or moves the original source snapshot to the helper prefix.

`StagedByteLookupSecurity.false_acceptance_bound` instantiates this theorem
with `ByteLookupPairMiddle.program` and its trusted completed view. It combines
the actual byte-backed repeated-pair all-pass bound for false original source
tuples with native algebra/PCS acceptance. The resulting bound is

```
TupleLookupPair.error(card(K), tupleWidth, activeCount, tableSize)^repetitions
  + (nativeScalarError + nativePerRootPCSErrorSum
     + completeRunAvailabilityCharge)
```

Original multiplicities and source tuples precede all sampled pairs. Helper
roots freeze before algebra/PCS coins. The trusted vector is the same vector
used by the native repeated arithmetic selector and the successful packet/
memory projection that starts grouped PCS. There is no resampling at helper
or algebra time and no supplied enabled flag, successful memory, packet family
or pair/PCS certificate that bypasses those links.

This theorem applies uniformly to every finite first-challenge, inner field
and outer reciprocal operational approximation. Those are analysis depths,
not chosen protocol retry caps. The unbounded sampling value/work laws remain
proved separately; equality with a complete **unbounded native execution**
and its work theorem is not asserted here. In particular, lookup-pair coins
are refined to fresh ideal raw bytes, while algebra and PCS randomness still
uses explicit ideal private-field sampling. Production transcript/XOF readers,
child/parent binding and Rust execution have not been equated with this model.

Remaining obligations include the unbounded whole-protocol execution and its
limit/work transfer, production XOF/transcript/Rust refinement, concrete field
constructor/basis/metadata validation, refinement of the remaining challenge
sites and conversion from byte consumption to primitive hash work. Honest
cryptographic opening and scheduler completion, deferred/global PBS,
application/knowledge and full PBS composition, and the final concrete
unbudgeted 128-bit expected-work theorem remain open. The complete objective
remains active.

The completed regression first executes the actual byte prefix: three pairs
`(0,1)`, all six raw bytes, and the four original/helper roots are retained
before algebra starts. It then proves that every supported ideal native-coin
run executes all three pair verifiers and the first helper PCS batch. The
computed PCS rejection skips later roots; successful selector memory reaches
PCS, and all five native hashes remain, bringing the shared hash log from
length three to eight. The proof uses probability semantics for the native
phase's classically defined checks, rather than assuming those checks reduce
on a literal scripted coin tape.

The suspended regression runs the composed staged program directly: its
second repetition suspends during Y, retains the first completed pair and
all four consumed bytes, records only the original source root, and runs
neither helper construction nor native algebra/PCS. The next unused bytes
remain on the scripted input tape. Exact continuation-case theorems also
establish the original native query program on completion and no verifier
queries on suspension.

Validation passed: focused HasteBoots build (3,949 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,048 build jobs and
all strict regression suites), and `git diff --check`. Logs:
`/tmp/hasteboots-byte-native-smoke-build.log`,
`/tmp/hasteboots-byte-native-strict-smoke.log`, and
`/tmp/hasteboots-byte-native-check.log`. All 1,170 guarded transitive axiom
audits remain subsets of `propext`, `Classical.choice` and `Quot.sound`.
No custom axioms, admitted proofs or compiled proof shortcuts were introduced.
The Rust worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`. The complete formal security
objective remains active.


## Full completed-trace limits and adaptive shared continuations

`CompletedObservation.LE` compares every event on the complete observation,
including raw rejected draws. Its bind theorem retains adaptive dependence on
those observations. Exact trace orders now cover the canonical byte loop,
sequential coefficients, extension assembly, reciprocal retries, hash/offset
pairs, repeated vectors and the typed wrapper. These orders concern completed
outcomes; suspended partial records remain genuine finite-program outputs.

`CompletedObservationLimit` restricts each operational distribution to its
completed outcomes and takes the increasing outer-measure supremum. The
Carathéodory proof establishes a countably additive measure on all observation
events. Every event is the limit of its actual gated prefix probabilities;
completion mass one gives a probability measure without conditioning or
renormalizing any finite prefix. Incomplete outputs have limiting measure
zero. Uniform finite-prefix event bounds pass to this measure.

`ByteLookupUnbounded` applies this construction to the actual typed repeated
lookup sampler. The common-depth sequence is cofinal in all three independent
byte/retry depths. Existing completion estimates prove mass one when the
canonical modulus is valid and the reciprocal domain is large enough. The
repeated tuple-lookup bound holds for this complete raw-observation law.
No retry cap or independent replacement of the actual Y-dependent offset
domain is introduced.

`CompletedContinuation` includes arbitrary trace-dependent total private-coin
continuations in a joint measure. `SharedCompletedContinuation.run_program`
proves an exact equality with the actual shared interpreter: private sampling
keeps the incoming cache/log, completed sampling starts the real continuation,
and suspension skips it while retaining the partial observation. Its joint
limit includes the actual final shared state. Probability normalization,
uniform event-bound transfer and preservation of all earlier complete raw
observation events are proved. These results apply at a fixed incoming shared
state; composing the original source checkpoint and the full native staged
acceptance/work experiment remains an additional obligation.

The smoke regressions distinguish equal value marginals with different raw
traces, exercise trace-sensitive depth monotonicity, prove normalized actual
byte and adaptive joint limits, exclude suspended observations in the limit,
and instantiate a continuation whose real cached hash depends on the raw
byte cost. A scripted continuation observes both rejected candidates and the accepted
draw before consuming its next primitive query, retaining the trace length
and the later answer in its result.

This does not identify the expected cost of the complete-trace limit with
the supremum of unconditional finite-prefix work. Almost-sure completion alone
is insufficient for that step; the expensive partial tails require their own
work-transfer argument. The final native acceptance/availability limit,
production SHA/XOF/FS and Rust refinement, primitive hash accounting, honest
opening/scheduler completeness, deferred/global PBS, application/knowledge
composition and the concrete unbudgeted 128-bit expected-work theorem remain
open. The full objective remains active.

Validation passed: focused HasteBoots build (3,958 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,057 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-limit-smoke-build.log`,
`/tmp/hasteboots-limit-strict-smoke.log` and
`/tmp/hasteboots-limit-check.log`. The 55 new theorem audits bring the
checked total to 1,225, all with transitive axiom sets contained in
`propext`, `Classical.choice` and `Quot.sound`. No custom axioms,
admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged at
`dff353006322693cab3dc6b654f82151f658f294`.


## Unbounded staged native lookup with the original source law

`ByteLookupMiddleTrace` proves full completed-observation monotonicity after
the actual helper builder and shared interpreter. Larger canonical, inner
and outer rejection depths preserve each earlier completed record, including
the helper's actual final cache/log. The helper may inspect every rejected
byte. Its completion mass is exactly the real typed sampler's completion
mass, regardless of the incoming state or helper behavior.

`StagedCompletedObservation` lifts this order through the actual source
commitment and both root-recording stages of `StagedCommitmentPrefix.witness`.
The original source/state is sampled before the byte sampler and retained;
later native work uses the actual helper state. Completion and source-event
factorization are proved after averaging the real source distribution,
without replacing source-time decoding by helper-time or final-state decoding.

`StagedByteLookupLimit` constructs a countably additive measure on these full
staged outcomes. It is normalized from eventual byte-sampler completion,
including native verifier runs whose flags reject. Its events are limits of
actual gated finite programs; the common depth is cofinal in all independent
depths. Erasing the two analysis snapshots gives the limit of the actual
staged query program with its final shared state. The original source/state
marginal is exactly preserved in the limit: finite completion has its proved
sampler mass, and that mass tends to one. Thus no source distribution is
biased through successful-sampling conditioning.

`StagedByteLookupUnboundedSecurity.false_acceptance_bound` now transfers the
proved native staged lookup false-acceptance bound to this unbounded measure.
The bound retains the repeated tuple-lookup loss, scalar algebra loss, grouped
PCS loss, and the supremum of the actual whole-prefix availability charges.
Every prefix charge covers the real source, byte/helper phase and optional
native continuation together; no oracle/retry cap or supplied PCS/FS
certificate is assumed.

That availability supremum remains explicit. This result does not identify
it with an expected charge under the completed-limit measure, and does not
transfer the unconditional byte-work means through expensive partial tails.
Those work identities, production SHA/XOF/transcript/FS and Rust refinement,
remaining challenge sites, primitive hash accounting, honest opening/scheduler
completeness, deferred/global PBS, application/knowledge/full-PBS composition,
and the concrete unbudgeted 128-bit expected-work theorem remain open.

The native-fixture regressions instantiate the normalized full staged and
operational measures for three actual byte-backed repetitions followed by
the native algebra/PCS continuation. A source-marginal regression proves that
its source snapshot retains the warm three-entry hash log and zero recorded
roots, even though later helper/native work records roots and issues hashes.
The full security objective remains active.

Validation passed: focused HasteBoots build (3,962 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,061 build jobs
and every strict regression suite, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-staged-limit-smoke-build.log`,
`/tmp/hasteboots-staged-limit-strict-smoke.log` and
`/tmp/hasteboots-staged-limit-check.log`. All 17 new theorem audits passed;
the total is now 1,242, with transitive axiom sets contained in `propext`,
`Classical.choice` and `Quot.sound`. No custom axioms, admitted proofs or
compiled proof shortcuts were introduced. The Rust worktree is unchanged.
The full formal-security objective remains active.


## Actual charge recording and completed-limit expectations

`ExpectedChargeComposition.bind` proves exact whole-run charge additivity:
the second phase starts at the actual first result/state, and its charge is
averaged over that same execution. Returning a pure observation of a result
adds no queries or charge. No branch is discarded because its verifier flag
rejects, and no finite expected cost is assumed.

`ChargedExecution.handler` instruments any actual stateful query handler
with a nonnegative account. It assesses the loss on the pre-response state,
then records the actual next state and adds that loss to the account.
`erase` proves equality with the full original query program after dropping
the account, and `event` preserves every original result/state probability.
`expected` and `expected_zero` identify the terminal account's expectation
with the existing recursive `ExpectedHazard.charge`, including infinite
expectations. This supplies an explicit actual-execution observable for the
charge used in the native lookup bound; it is not a work-budget assumption.

`PrivateSamplingCharge` proves zero charge for the full embedded private
computation whenever its private queries have zero loss. The concrete
availability/collision loss satisfies this premise by definition. Its exact
continuation theorem retains the entire private sampling observation and
uses the unchanged shared state for every later state-dependent charge.
This zero availability hazard does not assign zero computational work to
byte sampling or erase its rejected/partial draws.

`CompletedExpectation` proves continuity of the nonnegative integral for
increasing setwise measures, first for simple functions and then all
nonnegative observables. Applied to `CompletedObservationLimit`, the mean
retained cost is exactly the supremum of completion-gated finite means.
There is no bounded-cost, finite-mean or finite-observation-space premise.
The theorem deliberately keeps incomplete-prefix costs separate: almost-sure
completion alone does not replace gated expectations by unconditional means.

The execution regression uses the actual shared cache/log and a scripted
private draw. It then issues a fresh hash followed by a cache hit and returns
false. Its account retains the initial five units, one unit for the private
draw, eleven for the fresh hash, and three for the cached hash, for a total
of twenty. The cache hit consumes no extra uniform response; the ordered hash
log retains both calls. Additional regressions specialize the expected-account
identity and zero byte-sampling availability loss, and instantiate the gated
expectation-limit identity for the actual unbounded byte-lookup trace cost.

The remaining work includes constructing the corresponding completed
instrumented staged measure and transferring its account through the limit,
controlling unconditional partial-tail byte work, production SHA/XOF/FS and
Rust refinement, primitive hash accounting, honest opening/scheduler
completeness, deferred/global PBS, application/knowledge/full-PBS composition,
and the final concrete unbudgeted 128-bit expected-work theorem. The complete
formal-security objective remains active.

Validation passed: focused HasteBoots build (3,966 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,062 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-charge-smoke-build.log`,
`/tmp/hasteboots-charge-strict-smoke.log` and
`/tmp/hasteboots-charge-check.log`. All 14 new theorem audits passed,
bringing the total to 1,256; their transitive axiom sets are contained in
`propext`, `Classical.choice` and `Quot.sound`. No custom axioms,
admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged. The full formal-security objective remains active.


## Commit checkpoint

The accumulated implementation is now split into dependency-ordered commits:
ArkLib setup; matrix/PBS algebra; shared Merkle execution; packed sumcheck and
ZeroCheck; native NTT/batched PCS/linear checks; lookup arithmetic; repeated
native lookup/PCS; byte rejection and staged security; unbounded observation
measures; actual charge recording; and regression/documentation integration.
Each proof chunk's internal imports are supplied by that chunk or an earlier
commit. The source content retains the validated state recorded above.
Subsequent proof milestones should be committed as coherent tested chunks,
with their regressions and remaining security obligations recorded here.
The complete formal-security objective remains active.


## Recorded availability account in the unbounded byte continuation

`PrivateChargedSampling` proves exact interpretation of private sampling
through `ChargedExecution.handler`. When the private-query loss is zero,
each response and the whole embedded query program preserve both the actual
shared state and its existing account. This includes partial observations,
all rejected draws and arbitrary existing accounts. No expected-zero-to-
pathwise-zero inference is used: equality of the actual query program is
proved before taking probabilities or expectations.

`SharedChargedCompletion` retains the raw observation, actual continuation
result, final shared state and account in one countably additive measure.
Complete-observation order lifts through the recorded interpreter; eventual
sampler completion gives mass one. Erasing the account preserves every event
on the original complete shared execution, including joint events on raw
work and the final cache/log.

Starting this continuation's account at zero gives an exact additional fact:
when private sampling suspends, its account is still zero and the continuation
has issued no queries. Gating the account by sampling completion therefore
removes exactly zero new availability charge on every such execution.
Combining this fact with `CompletedExpectation` and `ChargedExecution` proves
that the mean account under the unbounded complete measure equals the
supremum of the actual sampling-plus-continuation prefix charges. There is
no finite-mean, query-budget or trace/continuation independence premise.

`ByteLookupChargedLimit` specializes this construction to the real repeated
canonical-byte/reciprocal sampler and actual checkpoint/collision loss.
The latter's private-query loss is proved zero by definition. Its completed
execution/account measure is normalized under the existing modulus/domain
conditions, has the proved expected-account identity, and retains the repeated
lookup bound through arbitrary trace-dependent shared continuation work.
This availability identity does not assign zero computational work to bytes.

The partial-byte regression runs the actual recorded interpreter: it retains
the first completed pair, all four consumed bytes, the three-entry incoming
hash log, the pre-existing account of seven, and the unused response tape.
The native regressions record the original source root before byte sampling,
then run helper construction/root recording and the actual repeated native
algebra/PCS continuation. They instantiate its normalized full account law,
expected-charge identity and account erasure for a joint byte-cost/final-log
event, including runs whose computed verifier flags reject.

The proved expected-account identity is conditional on a fixed incoming
shared state and starts the new phase's account at zero. Earlier charged
source commitment work must still be composed in its real original position;
this entry does not identify the earlier full staged charge supremum with a
completed whole-protocol expected account. Unconditional partial-tail byte
work, production SHA/XOF/transcript/FS and Rust refinement, primitive hash
accounting, honest opening/scheduler completeness, deferred/global PBS,
application/knowledge/full-PBS composition and the final concrete unbudgeted
128-bit expected-work theorem remain open. The full objective remains active.

Validation passed: focused HasteBoots build (3,969 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,066 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-charged-limit-smoke-build.log`,
`/tmp/hasteboots-charged-limit-strict-smoke.log` and
`/tmp/hasteboots-charged-limit-check.log`. All 16 new theorem audits passed,
bringing the total to 1,272; their transitive axiom sets are contained in
`propext`, `Classical.choice` and `Quot.sound`. No custom axioms,
admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged. This proof, its regressions and its documented
scope form one commit chunk. The full formal-security objective remains active.


## Earlier charged prefix composed before the completed continuation

`ChargeAccountShift` proves an exact query-program identity for every
recorded interpreter: starting from an existing account equals the same
zero-account execution with that existing account added to its final cost.
Primitive answers, return values and final original state are identical.
The identity permits infinite existing accounts and does not subtract costs.

`CompletedPrefixMixture` first samples the actual earlier prefix and retains
its full observation, then runs its observation-dependent completed tail.
It constructs the countably additive joint measure and proves that its
nonnegative mean is the actual prefix average of the conditional completed
means. Monotone convergence is pointwise in the original prefix observation;
there is no finite-mean, uniform-cost or prefix/continuation independence
premise. Normalization is proved when each prefix's tail completes almost
surely, without conditioning the original prefix distribution.

`ChargedPrefixCompletion` applies this construction to the actual recorded
shared handler. The source observation includes its return value, actual
intermediate state and earlier account. Each conditional tail starts from
that exact original state; its zero-account construction records only new
increments. The operational projection adds the earlier account once, and
`finite_operational` proves equality with the actual full query program that
executes the prefix before private sampling and later shared work. Every
operational event is the limit of those actual completed finite full runs.

The complete mean splits into the actual earlier recursive charge plus its
prefix-average conditional later charge. Conditional charges are proved
monotone from the completed observation/account order. Nonnegative monotone
convergence and exact charge composition then identify the complete mean
with the supremum of the same full finite-program charges. Earlier work is
not omitted when a finite sampling approximation suspends, nor duplicated
across repetitions. Both source and later expectations may be infinite.
This is an availability-account identity under zero private-query loss;
it does not set physical byte work to zero.

The suspension regression issues an actual earlier hash and records a source
root, charging five units in the test metric. It then suspends without issuing
the later hash, retaining the earlier account, four-entry hash log, source
root and unused uniform response. The native fixture issues earlier hash work
and records the original source root before real repeated byte sampling,
helper/root construction and the native algebra/PCS continuation. It
instantiates the normalized full account law and expected whole-prefix charge
identity using the actual checkpoint/collision loss.

This closes earlier-charge accounting for the prefix-plus-completed-
continuation program. Applying the identity directly to the previously
proved `StagedByteLookupUnboundedSecurity` bound still requires the exact
factorization adapters for its trusted typed helper emission, original source
snapshot and root-recording interface. Computational byte-tail work,
production SHA/XOF/transcript/FS and Rust refinement, primitive hash-work
accounting, honest opening/scheduler completeness, deferred/global PBS,
application/knowledge/full-PBS composition and the final concrete unbudgeted
128-bit expected-work theorem remain open. The full objective remains active.

Validation passed: focused HasteBoots build (3,972 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,069 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-prefix-charge-smoke-build.log`,
`/tmp/hasteboots-prefix-charge-strict-smoke.log` and
`/tmp/hasteboots-prefix-charge-check.log`. All 17 new theorem audits passed,
bringing the total to 1,289; their transitive axiom sets are contained in
`propext`, `Classical.choice` and `Quot.sound`. No custom axioms,
admitted proofs or compiled proof shortcuts were introduced. The Rust
worktree remains unchanged. The proof, its source-work regressions and its
documented remaining interface obligations form one commit chunk. The full
formal-security objective remains active.


## Original staged native lookup bound with an expected availability account

`StagedByteFactor.factor` proves equality of query programs between the
original `StagedCommitmentPrefix.program` byte/helper/native execution and
the prefix-plus-completed-continuation program used by the charge proof.
The original source commitment and its root annotations run before bytes;
the actual helper builder and chosen helper roots follow completed sampling.
The typed sample and every raw observation remain stored in the helper
emission. Projection only repackages returned values and inserts no query,
fallback typed vector, root or native result on suspension.

Its two structural premises state that suspended samples record no helper
roots and run no native continuation. The concrete native theorem derives
both facts from `ByteLookupPairMiddle.completed` and
`OptionalStagedLookup.continuation`; they are not supplied security or work
certificates. `StagedByteFactor.charge` then identifies the original staged
program's charge with the factored program's charge for any state-dependent
loss, using that pure result projection adds no queries.

`StagedByteChargedLimit` projects the proven completed account construction
back to the original staged result shape: original source, typed raw-byte/
optional helper emission, optional native result, and actual final state/
account. The measure is normalized under the existing sampler/domain
conditions. Its mean account equals the supremum of the original whole
staged query program's finite charges, retaining earlier source work and
both real root-recording stages exactly once.

`StagedByteExpectedSecurity.false_acceptance_bound` now replaces the charge
supremum in the previously proved unbounded native lookup bound by this
actual mean availability account. The false-acceptance event remains in the
original frozen-source witness law; it is not changed to helper-time or
final-state source decoding. The lookup repetition, scalar algebra and
grouped PCS losses are retained. The mean account includes all source,
sampling/helper and native work charged by the actual availability metric,
including computed native rejection branches. No oracle/retry cap or
assumed PCS/FS/work certificate is introduced.

The native regressions instantiate exact query-program factorization with
an earlier source hash, original source-root recording, three genuine byte
pairs, helper/root construction and the actual algebra/PCS continuation.
They also verify normalization in the original staged return shape and the
mean identity against that original program's whole charge supremum.

This closes the earlier staged lookup-bound/expected-account adapter
obligation. It does not yet convert the state-dependent availability account
to concrete primitive hash work, transfer unconditional computational byte
work through partial tails, or refine production SHA/XOF/transcript/FS and
Rust execution. Honest opening/scheduler completeness, deferred/global PBS,
application/knowledge/full-PBS composition and the final concrete unbudgeted
128-bit expected-work theorem also remain open. The full objective remains
active.

Validation passed: focused HasteBoots build (3,975 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,074 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-staged-expected-smoke-build.log`,
`/tmp/hasteboots-staged-expected-strict-smoke.log` and
`/tmp/hasteboots-staged-expected-check.log`. All five new theorem audits
passed, bringing the total to 1,294; their transitive axiom sets are
contained in `propext`, `Classical.choice` and `Quot.sound`. No custom
axioms, admitted proofs or compiled proof shortcuts were introduced. The
Rust worktree remains unchanged. The exact adapter, expected-account native
bound, regressions and documented remaining obligations form one commit
chunk. The full formal-security objective remains active.


## Canonical byte work in the completed raw-trace measure

`CompletedCostTransfer` partitions each unconditional prefix cost into its
completed and incomplete contributions. Monotonicity of the completed
observation measures gives convergence of the first contribution to the
actual completed mean. A proved zero limit for the second contribution
then transfers the unconditional limit exactly. This theorem does not
require finite means or replace the work-tail proof with completion
probability tending to one.

`RejectionTraceWork` derives the operational trace-length bound at each
analysis depth and proves that a suspended trace has length exactly that
depth. The incomplete expected work is therefore exactly `n * rho^n`,
where `rho` is the sampler's rejection probability. Its geometric decay
for a nonempty accepted domain proves the actual completed raw-trace
mean is the full-domain cardinality divided by the accepted cardinality.
The completed trace measure is normalized under the same condition.
An empty accepted domain instead has zero completed mass while the
unconditional retry mean is infinite; a regression checks this distinction.
These are derived bounds for finite approximations, not native retry caps.

`CanonicalTraceWork` constructs the completed measure of the actual
masked-below-modulus byte sampler, retaining every rejected raw chunk.
Its incomplete expected byte work is the configured byte width times
`n * rho^n`, which tends to zero for `1 < p`. Its completed expected bytes
thus equal the previously proved unconditional byte-work limit, exactly
`byteCount(p) * 2^bits(p) / p`. Regressions check a small modulus, positive
incomplete work at finite depth, and the native Goldilocks and BabyBear
formulas. Their raw chunk widths are eight and four bytes respectively;
these widths are separate from protocol packing parameters.

This closes the base canonical sampler's computational byte-work transfer.
Nested sequential coefficient/extension and reciprocal/pair/vector byte-work
transfers remain open, as do physical SHA/XOF/hash-work accounting, production
transcript/FS and Rust refinement, honest opening/scheduler completeness,
deferred/global PBS, application/knowledge/full-PBS composition and the final
concrete unbudgeted 128-bit expected-work theorem. The full formal-security
objective remains active.

Validation passed: focused HasteBoots build (3,978 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,077 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-completed-byte-work-smoke-build.log`,
`/tmp/hasteboots-completed-byte-work-strict-smoke.log` and
`/tmp/hasteboots-completed-byte-work-check.log`. All 19 new theorem audits
passed, bringing the total to 1,313; their transitive axiom sets are contained
in `propext`, `Classical.choice` and `Quot.sound`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced. The Rust worktree remains
unchanged. The general transfer, canonical sampler application, regressions
and documented remaining obligations form one commit chunk.


## Completed sequential coefficient and extension byte means

`CoefficientTraceWork` derives support and suspension bounds from the actual
sequential coefficient query program. At analysis depth `n`, a request for
`c` coefficients retains at most `c * n` raw chunks, including earlier accepted
coefficients and the suspended last coefficient. Its suspension probability
is at most `c * rho^n`, where `rho` is the actual base sampler rejection
probability. The proof starts the suffix only after a completed head; it
requires no supplied independence certificate.

These bounds give an incomplete expected byte cost of at most
`byteCount(p) * c * c * (n * rho^n)`. For `1 < p`, the geometric work tail
vanishes, so `CompletedCostTransfer` identifies the completed raw-trace
mean with the previously derived unconditional limit, exactly
`c * CanonicalByteSampler.totalExpectedBytes p`. The same completed measure
is normalized without rescaling finite successful mass. The per-depth
support bounds are analysis facts, not protocol retry or byte limits.

`ExtensionTraceWork` retains the actual pure basis assembly together with
the whole coefficient observation. Its incomplete work equals that of the
`count * degree` sequential coefficients; completion is precisely coefficient
completion. Consequently its completed measure is normalized and its exact
byte mean is `count * degree` times the base sampler mean. The theorem
does not assume a concrete native field constructor or count pure assembly
as physical hash work.

Regressions check normalization, zero coefficient requests, two completed
coefficients, and the real suspended execution that accepts the first
coefficient and retains both raw chunks. A two-coordinate basis with two
requested elements checks the four-coefficient completed mean. Native
Goldilocks degree three and BabyBear degree six regressions check their
completed raw byte means; lookup degrees remain separate from PCS packing.

This closes the sequential coefficient and pure extension byte-work
transfers. Reciprocal/pair/vector byte-work transfers, physical SHA/XOF/hash
work, production transcript/FS and Rust refinement, honest opening/scheduler
completeness, deferred/global PBS, application/knowledge/full-PBS composition
and the final concrete unbudgeted 128-bit expected-work theorem remain open.
The full formal-security objective remains active.

Validation passed: focused HasteBoots build (3,980 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,076 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-coefficient-trace-smoke-build.log`,
`/tmp/hasteboots-coefficient-trace-strict-smoke.log` and
`/tmp/hasteboots-coefficient-trace-check.log`. All 11 new theorem audits
passed, bringing the total to 1,324; their transitive axiom sets are contained
in `propext`, `Classical.choice` and `Quot.sound`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced. The Rust worktree remains
unchanged. The sequential and assembly work transfer, regressions and
documented remaining obligations form one commit chunk.


## Completed reciprocal raw-trial byte-work mean

`OptionalRejectionTail` proves finite support cost bounds and an exact
suspension recurrence for the actual optional rejection loop. An inner
suspension stops immediately and retains that trial; only a completed
rejected candidate starts another trial. If the inner suspension probability
is `a` and completed rejection probability is `r`, outer depth `O` has
suspension probability at most `O * a + r^O`. Every supported trial's
work contributes to the prefix bound, including a partial last trial.

`ReciprocalTraceWork` derives the field-trial suspension bound from the
sequential coefficient program and the completed pole-rejection rate from
the actual candidate law. Let `w` be raw byte width, `d` the basis degree,
`I` inner depth, `O` outer depth, `kappa` the canonical byte rejection
probability and `theta` the rejection probability of the actual reciprocal
allowed domain. The full prefix consumes at most `w * d * I * O` bytes
and suspends with probability at most `O * d * kappa^I + theta^O`.
Consequently its unfinished expected work is bounded by their product.
All these are derived analysis-prefix bounds, not native retry or byte caps.

At common depth `n`, this product is
`w * d^2 * n^3 * kappa^n + w * d * n^2 * theta^n`. Polynomial/geometric
decay proves both terms tend to zero under `1 < p` and the existing
accepted-domain size condition. This accounts separately for unfinished
inner fields and completed but rejected field trials; it does not infer
work convergence merely from successful mass tending to one.

The completed raw-trial measure is normalized and cofinal in all independent
inner/outer depths, for arbitrary events on the full retained observation.
Its exact expected consumed bytes equal the existing unconditional
reciprocal work supremum and formula: one actual field draw's canonical
byte mean times `card(K) / card(allowed(table))`. The real allowed-domain
cardinality preserves duplicate-pole behavior. No cost/value independence
certificate or finite successful-mass normalization is supplied.

Regressions check immediate stopping on inner suspension, normalized
completed traces, the exact completed mean `32/15` for the small-field
one-pole fixture, support bounds including partial work, and cofinality
for a raw-byte-cost event. The concrete tape regression retains two
completed rejected fields and an incomplete third field with four issued
bytes, leaving the later tape unused.

This closes the reciprocal byte-work transfer. Pair/vector byte-work
transfers, physical SHA/XOF/hash work, production transcript/FS and Rust
refinement, honest opening/scheduler completeness, deferred/global PBS,
application/knowledge/full-PBS composition and the final concrete unbudgeted
128-bit expected-work theorem remain open. The full objective remains active.

Validation passed: focused HasteBoots build (3,982 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,079 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-reciprocal-trace-smoke-build.log`,
`/tmp/hasteboots-reciprocal-trace-strict-smoke.log` and
`/tmp/hasteboots-reciprocal-trace-check.log`. All 18 new theorem audits
passed, bringing the total to 1,342; their transitive axiom sets are contained
in `propext`, `Classical.choice` and `Quot.sound`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced. The Rust worktree remains
unchanged. The nested rejection bounds, completed reciprocal byte-work
transfer, regressions and documented remaining obligations form one commit
chunk. The full formal-security objective remains active.


## Completed pair and repeated typed lookup byte-work means

`PairTraceWork` derives support and suspension bounds from the actual
byte-backed pair program. The first completed field challenge chooses its
public-table hashes and reciprocal domain; unfinished first draws start no
reciprocal trial. With byte width `w`, basis degree `d` and depths `H,I,O`,
full retained work is at most `w * d * (H + I * O)`. Suspension is bounded by
`d * kappa^H + O * d * kappa^I + sum_y theta(y)^O`, where `kappa` is the
base canonical rejection probability and `theta(y)` belongs to the actual
reciprocal domain for first challenge `y`.

The unweighted finite sum over challenges is only an auxiliary work-tail
bound. It does not replace the exact conditional-domain average in the
final mean or add a security loss. Every fixed polynomial multiple of this
suspension probability tends to zero along common depth, because each
actual domain is nonempty under the existing size condition. The completed
pair measure is normalized and its byte mean equals the existing exact
unconditional pair-work formula, retaining collisions and duplicate poles.
No independence between the pair coordinates is assumed.

`ObservedVectorTail` derives support and suspension bounds for the actual
sequential observed-vector program. A failed head stops the suffix; every
started observation remains in the work sum. For `r` requested repetitions,
the raw vector support bound is `r * w * d * (n + n^2)` and its suspension
probability is at most `r` times that of the real single-pair program.
`VectorTraceWork` combines these bounds with the pair's polynomial tail
decay to prove that unfinished vector byte work vanishes. Earlier successful
pairs and the suspended last pair are all counted. These are derived bounds
on finite analysis approximations, not native retry or byte caps.

The typing adapter uses the already proved exact raw-program erasure and
completion equivalence. It transfers the result directly to the existing
`ByteLookupUnbounded.measure` used by the staged native security proof.
The actual completed typed mean equals the unconditional repeated-byte
supremum, hence the exact conditional-domain pair byte mean times the true
repetition count. A public size-based upper bound is also proved for that
same completed measure. Repetition count, extension degree and PCS packing
remain separate parameters.

Regressions check pair normalization and mean, support bounds with partial
work, zero and three repetitions in the original typed measure, and its
public size-based cost bound. The actual typed trace regression preserves
one completed pair and six total bytes when the second pair suspends
inside an offset field draw, leaving the third repetition and later tape
unstarted. Existing fixtures retain different domain cardinalities at
different first challenges.

This closes the canonical/coefficient/extension/reciprocal/pair/vector
byte-work transfers to completed sampler measures, including the existing
unbounded typed lookup law. Converting these byte means and the separate
availability account to physical SHA/XOF/hash work remains open, as do
production transcript/FS and Rust refinement, honest opening/scheduler
completeness, deferred/global PBS, application/knowledge/full-PBS composition
and the final concrete unbudgeted 128-bit expected-work theorem. The full
formal-security objective remains active.

Validation passed: focused HasteBoots build (3,985 jobs), strict
warning-as-error HasteBoots smoke, full `scripts/check` (10,081 build jobs
and all strict regression suites, terminal exit zero), and
`git diff --check`. Logs: `/tmp/hasteboots-pair-vector-trace-smoke-build.log`,
`/tmp/hasteboots-pair-vector-trace-strict-smoke.log` and
`/tmp/hasteboots-pair-vector-trace-check.log`. All 18 new theorem audits
passed, bringing the total to 1,360; their transitive axiom sets are contained
in `propext`, `Classical.choice` and `Quot.sound`. No custom axioms, admitted
proofs or compiled proof shortcuts were introduced. The Rust worktree remains
unchanged. The conditional pair and sequential vector work tails, original
typed-measure transfer, regressions and documented remaining obligations
form one commit chunk. The full formal-security objective remains active.


## Revised roadmap M0: experiment contract and extraction probe

The revised plan prioritizes the custom transcript/compiler and unrestricted
expected-work gaps. Final completion requires both primitive and abstract
64-bit computation accounting, checked correspondence with the pinned Rust
typed verifier, and a separate byte-decoding corollary. The original protocol
12/schedule-5 Brakedown target, dimensions, keys, and Goldilocks-before-BabyBear
order are unchanged.

`SecurityExperiment` defines the target interface independently of any
claimed security bound. Chronological events distinguish attacker, verifier
and setup work. Primitive SHA-512 blocks, SHAKE absorb/squeeze blocks,
constructed bytes, memory operations and machine steps have separate fields;
no conversion between them is assumed. Submissions do not magically create
a paid-work event: native execution and cost refinement must justify that
charge. Earlier accepted false submissions persist after later rejection.

The final target ranges over an explicit adversary type and its implemented
experiment. A history is a potentially infinite sequence of optional events,
with the countable product sigma algebra. Total attacker steps are the
supremum of actual finite prefix counts. This admits unbounded retries and
infinite work without using a discrete sigma algebra on an uncountable
whole-history space. `RiskBound` retains an explicit initial-risk term;
`ExpectedWorkSecurity` states the desired ratio and does not prove it.
The current module is a contract, not the joint native execution or a
security certificate.

Remaining revised milestones, in order: implement joint SHAKE/SHA-512
transcript semantics; prove one actual linked lookup child under prequeries
and stream reuse; prove the stopping/work conversion; compose all PBS stages
and application extraction; compile the whole transcript and prove checked
Rust correspondence; then certify concrete parameters and the byte corollary.
No further sampler foundations are planned without a named dependency of
these end-to-end obligations.

Extraction probe: Aeneas revision
`15b968482b0dcd7aae45020b6d1bca39b5024af5` was cloned outside the repository.
Its recorded Charon pin is `ef3748c1a92c6acc402f978770193d34adc0fe6e` and
its Lean backend targets 4.31.0. Neither extraction executable is installed
on PATH. A direct source probe failed because Aeneas was not a resolved
package; this is not a demonstrated Lean compatibility failure. A separate
temporary checkout now attempts the primitive backend against the existing
Lean 4.35/mathlib environment. Root dependency pins and vendor sources are
unchanged. Successful extraction and the Rust refinement gate remain open.

The isolated primitive-backend build terminated with exit 1 after resolving
mathlib to the root 4.35 source. It fails in `AeneasMeta.BvEnumToBitVec`
(the imported `Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Enums` module was
moved) and `AeneasMeta.Simp.Simp` (the simplifier result and hash-set APIs
changed). Logs: `/tmp/hasteboots-aeneas-m0-build.log`. Reproduction uses the
pinned checkout above, changes only its temporary Lean toolchain to 4.35.0
and its mathlib require to `/workspace/.lake/packages/mathlib`, then runs
`lake update mathlib` and `lake build Aeneas.Std.Primitives` inside the
project container. This is a diagnosed compatibility task, not evidence that
extraction is impossible or that the full goal is blocked. The next tooling
step is to port those two meta modules in isolation and repeat the probe.

Contract validation passed: focused HasteBoots build (3,986 jobs), strict
warning-as-error smoke, and full `scripts/check` (10,082 build jobs and all
strict suites, terminal exit zero). Four new guarded theorem audits passed,
bringing the total to 1,364, with only standard kernel foundations. Logs:
`/tmp/hasteboots-experiment-smoke.log`, `/tmp/hasteboots-experiment-strict.log`
and `/tmp/hasteboots-experiment-check.log`. `git diff --check` passed and the
Rust worktree is unchanged. These checks validate the contract and its ledger
properties; the final security goal is still unproved. The concrete joint
execution must additionally establish normalization and correspondence with
the specified adversary class. M0 is partially implemented; the extraction
gate and later milestones remain open.


## Revised roadmap M0: pinned Aeneas primitive backend on Lean 4.35

The two diagnosed compatibility failures are repaired in an isolated patch
against Aeneas `15b968482b0dcd7aae45020b6d1bca39b5024af5`. The enum helper
imports the relocated Lean module and uses the public reserved-name action
dispatcher with the already resolved absolute declaration name. It verifies
that each conversion constant was produced and preserves idempotence, without
calling private realization helpers. The simplifier preserves explicit
`Option` values for fresh hypotheses and supplies the hash-set element type
required by Lean 4.35. No proof axioms or primitive semantics were changed.

`interop/aeneas/lean435.patch` and `scripts/probe-hasteboots-aeneas` make the
probe reproducible. The script owns a separate checkout, checks its exact
revision and ownership marker, applies or verifies the patch, uses the root
toolchain/mathlib, builds `Aeneas.Std.Primitives`, and runs the isolated
warning-as-error `interop/aeneas/Probe.lean`. Default checkout location is
ignored `build/aeneas-probe`; root dependencies and vendor sources remain
unchanged. Existing unmarked checkouts are refused.

The isolated regressions exercise successful `Result` bind, overflow-error
propagation, divergence propagation, and eager enum conversions in a non-root
namespace, including repeated realization. The upstream primitive build
passes (56 jobs), with upstream proposition-style warnings; our regression
file passes warning-as-error. The preserved upstream warnings are not
reported as root strict-check failures. Logs:
`/tmp/hasteboots-aeneas-m0-repair.log` and
`/tmp/hasteboots-aeneas-repro.log`.

This clears the primitive-backend compatibility subgate only. The full Aeneas
standard library, Charon/frontend build, extraction of actual HasteBoots
framing/sampling, oracle-aware result bridge, and checked verifier
correspondence remain open. No Rust extraction or security theorem is claimed
from a primitive import. The next tooling step is to extend this isolated
probe to the standard-library surface needed by the real sampler and then
build the recorded Charon frontend. The full objective remains active.

Reproduction additionally passed after reversing the patch to the pinned
pristine source (`/tmp/hasteboots-aeneas-repro-fresh.log`, terminal exit zero),
and the probe refused an existing unmarked directory without modifying it.
`bash -n` and `git diff --check` passed. Root Lean proof sources, dependency
pins and Rust sources are unchanged; validation for this chunk is the
isolated patched backend and strict regression probe.


## Revised roadmap M0: standard library compatibility

`interop/aeneas/stdlib435.patch` extends the isolated port to `Aeneas.Std`.
It restores definition-alias transparency in the WP and collection proofs,
updates numeric conversion cast proofs and WP unfolding, uses the current
natural-number cancellation lemma, avoids the new `Nat.reduceLog2` name
collision, and matches powers without depending on a removed instance path.
The primitive arithmetic definitions are preserved. The compatibility script
now applies both patches and builds `Aeneas.Std` before the strict probe.

Validation: all 1,666 standard-library build jobs passed; the strict probe
also passed, including little-endian byte conversion and leading-zero counts
at zero, one, and a 64-bit boundary. Log:
`/tmp/hasteboots-std-repro.log`. This is not a claim that upstream is free of
admissions: it includes an unused `StringIter` declaration using `sorry`.
Each extracted target must pass its own dependency audit. The umbrella
`Aeneas` build still fails in unrelated BV tactic examples, a duplicate
array lemma, and diagnostic-message tests on Lean 4.35. Generated probes use
`Aeneas.Std` and the Rust attribute module by an import-only change; no
program terms are repaired to make them typecheck.

The patch reverse-check, script syntax check, and whitespace checks passed.
Root proof sources, dependency pins, vendor sources, and the HasteBoots Rust
worktree are unchanged. No root full-suite rerun was needed for this isolated
backend change; the previous root full-suite result remains the one above.
The sampler extraction and full Rust correspondence obligations remain open.


## Revised roadmap M0: actual sampler extraction probe

`scripts/extract-hasteboots-sampler` copies the complete `CanonicalSampler`
fragment verbatim from the pinned Rust `helper/src/transcript.rs`, lines
544–573. It checks both the complete source SHA-256 and the fragment SHA-256.
A separate diagnostic wrapper supplies a fixed repeated block to the reader;
that wrapper is not an oracle model and is not used as a replacement sampler.
No original Rust source is modified.

The frontend is the official Aeneas release
[nightly-2026.07.11-15b9684](https://github.com/AeneasVerif/aeneas/releases/tag/nightly-2026.07.11-15b9684),
with bundled Charon 0.1.223 (recorded Charon revision
`ef3748c1a92c6acc402f978770193d34adc0fe6e`). The Linux archive SHA-256 is
`a3ebfd35c9c77873bcc6e22fa0f1d9965539b6364c6b706a5af8aeca41d`.
The harness additionally verifies the three executable hashes and the bundled
Rust toolchain file. It requires Rust nightly-2026-06-01 with `rustc-dev`,
`rust-src`, `llvm-tools-preview`, and `miri` installed. Miri's sysroot is
necessary to expose the Rust standard-library MIR for `div_ceil`. This
experiment uses the verified official binaries, not a local frontend build.

Given the unpacked release directory and the prepared isolated backend:

```sh
scripts/probe-hasteboots-aeneas /tmp/hasteboots-aeneas-m0
scripts/extract-hasteboots-sampler --tools /tmp/hasteboots-aeneas-tools \
  --backend /tmp/hasteboots-aeneas-m0
scripts/extract-hasteboots-sampler --tools /tmp/hasteboots-aeneas-tools \
  --backend /tmp/hasteboots-aeneas-m0 --mode sampler
```

The default constructor-only extraction passes Lean 4.35 typechecking and
its target dependency audit is exactly `[propext, Classical.choice,
Quot.sound]`. `u32::div_ceil` is extracted transparently by the inclusion
pattern `core::num::_::div_ceil`; treating it as an opaque axiom is refused.
Only the generated import changes, from the umbrella `Aeneas` to `Aeneas.Std`
and `Aeneas.Tactic.RustAttributes`. Every generated declaration and term is
preserved. This establishes an import/extraction subgate, not constructor
functional correctness or Rust compiler correctness.

The full sampler command currently **fails** Lean typechecking. The generated
`FnMut` callback use carries the updated mutable slice, whereas the backend
`FnMut` class expects only the unit result and updated closure. The closure's
`FnOnce` instance also mismatches its expected unit result. Elaboration then
reports `sorryAx` in the sampler dependency closure; the command exits
nonzero and its manifest records failure. No admitted sampler is accepted.
This is a concrete frontend/backend correspondence gap to resolve before the
full Rust refinement gate can pass. Broad extraction of Rust internals also
exposes unsupported pointer/transmute operations; the narrow inclusion rules
avoid those without hiding `div_ceil`.

Each run has a fresh directory under ignored `build/hasteboots-extraction`,
with the exact fixture, LLBC, generated Lean, import-only checked file,
commands, logs, source/tool/output hashes, backend diff fingerprint, root
manifest/toolchain, mathlib revision, and explicit pass/failure status.
Failures cannot reuse an earlier successful output. Constructor reproduction
passed; full sampler reproduction reached and rejected the callback mismatch.
Root proof sources and dependency pins remain unchanged. Joint oracle
semantics, unrestricted work conversion, PBS composition, and full verifier
correspondence remain unproved; the full objective remains active.


## Revised roadmap M1: normalized joint input-indexed oracle world

`InputIndexedOracle.lean` defines one probability measure on all SHAKE byte
coordinates `(complete input, output position)` and all SHA-512 byte
coordinates `(complete input, position < 64)`. The two primitive families
share one world and use disjoint coordinate tags. Only the base byte space
is discrete; the infinite world has the product sigma algebra. Normalization
is proved by the infinite-product probability-measure instance.

Readers retain an input and cursor. Every read consults the same fixed
world, and its cursor advances by the actual requested count. The proved
split/coalesced-read identity preserves both output and cursor pointwise;
empty reads preserve the cursor, and restarting a repeated input uses its
existing prefix. Cloning a reader is ordinary copying of that same state,
not resampling. The model does not place reader IDs or method labels in
oracle keys.

Distinct finite coordinates have the exact product byte law and the exact
uniform finite-vector marginal used by the byte-sampler proofs. The SHAKE
block law, complete SHA-512 digest law, and joint cross-primitive byte law
are derived from the same normalized measure. Finite mixed prequery
assignments are measurable and have mass `256^(-number of distinct
coordinates)`; adding a fresh coordinate multiplies mass by `1/256`.
Repeated coordinates remain one assignment, as covered by the regression.
This is a fixed finite-history extension theorem, not adaptive
conditioning, a Fiat–Shamir theorem, or a claimed fresh phase.

This implements the joint ideal-law and reader-consistency part of M1.
Native length framing (kinds 0–8), receipt and child transitions, native
extension basis descriptors, adaptive revelation/cached-handler equivalence,
and transcript compilation remain open. M0's full Rust correspondence gate
also remains open: specialization with `--monomorphize-mut=except-types`,
`--remove-adt-clauses`, and `--lift-associated-types=*` successfully reaches
Aeneas but fails with a `core.ops.function.FnOnce` name collision. The pinned
upstream higher-ranked trait test leaves the mutable-reference callback as a
TODO. No generated terms or original Rust sources were rewritten to hide
these failures. Diagnostic artifacts are in
`build/hasteboots-extraction/sampler-specialized-j53tpgal`.


Validation passed: focused HasteBoots smoke build (4,064 jobs), separate
warning-as-error HasteBoots smoke, and full `scripts/check` (10,083 build
jobs followed by all strict suites, terminal exit zero). Ten new guarded
HasteBoots dependency audits passed, bringing the total to 1,374. The new
proofs depend only on the permitted standard kernel foundations. Logs:
`/tmp/hasteboots-joint-oracle-smoke.log`,
`/tmp/hasteboots-joint-oracle-strict.log`, and
`/tmp/hasteboots-joint-oracle-check.log`. Whitespace checks passed. Root
dependency pins, vendor sources, and the Rust worktree are unchanged.
The complete security objective remains active and unproved.


## Revised roadmap M1: frame codec and logged native transitions

`TranscriptFrame.lean` specifies the inspected native layout
`kind || u64le(label length) || label || u64le(message length) || message`.
Little-endian round trips and injectivity retain explicit length bounds
below `2^64`; overlarge lengths are not silently treated as injective.
The decoder checks header/body lengths and rejects kinds outside 0–8.
Decoding an encoded frame returns an arbitrary suffix unchanged. This
proves frame-boundary uniqueness and injectivity of complete valid frame
sequences. Structural decoding does not certify protocol-stage admissibility.

`NativeTranscript.lean` specifies root initialization (kind 0), public byte
absorption (1), byte requests/results (2/3), canonical-field request and
receipt framing (4/5), child-fork/finish framing (6/7), and checkpointing (8).
All methods consult the same joint `World`. A writer log records reader
starts and returned chunks in model execution order, including empty byte
challenges and zero-count field requests. Receipt and checkpoint readers
are logged alongside challenge/seed/fingerprint readers. Reader IDs are
not oracle keys. Profile inheritance is proved for forks.

Field phases retain every consumed raw chunk. Begin/draw coherence proves
that retained bytes are the exact prefix of the original request's stream;
splitting reads preserves the complete raw output and final field phase.
The 80-byte receipt consists of a 16-byte little-endian consumed length and
64 bytes from the same-world SHAKE query on the literal domain followed by
the complete raw prefix. No rejected candidate is removed. The receipt
query's first UTF-8 byte is 72, outside the frame-kind range, proving that
its input cannot equal a nonempty framed stream. This does not establish
freshness relative to arbitrary adversarial prequeries. Request framing
also preserves label identity under the declared length bounds.

Source inspection was against unchanged HasteBoots revision
`dff353006322693cab3dc6b654f82151f658f294`,
`helper/src/classical_transcript.rs` SHA-256
`8ac0ace46e2da0d135b606bd9d290514c1e5b9a2fd6e1c67a15327b625b82c50`.
These are source-aligned ideal-model definitions, not an extracted Rust
correspondence certificate. The native field/basis descriptors (including
the native extension polynomials), detached wrapper parent-binding checks,
canonical/reciprocal sampler connection, and scheduler correspondence
remain open. Adaptive revelation and replay, the linked lookup child
compiler under whole-history prequeries, the unrestricted stopping/work
conversion, full PBS composition, and final concrete security theorem
also remain open. Observation logs are not assumed to be attacker-work
counters, and no primitive-to-machine-cost conversion is asserted.


Validation passed: the focused HasteBoots smoke build (4,066 jobs), separate
warning-as-error HasteBoots smoke, and full `scripts/check` (10,085 build jobs
followed by all strict suites, terminal exit zero). Fifteen new guarded
HasteBoots audits passed, bringing the total to 1,389, all within the
permitted standard kernel foundations. Regressions cover an independent
byte fixture, little-endian length order, invalid kinds, truncated headers
and bodies, u64 truncation, empty challenges, zero-count field-reader starts,
and complete raw-byte retention. Logs: `/tmp/hasteboots-framed-smoke.log`,
`/tmp/hasteboots-framed-strict.log`, `/tmp/hasteboots-frame-audit.log`, and
`/tmp/hasteboots-framed-check.log`. Whitespace checks passed; dependency pins,
vendor sources, and original Rust sources are unchanged. Next M1 work is
counterfactual replay from logged observations and typed descriptor/child
integration; arbitrary-input decoder soundness remains to be proved before
using the decoder to classify adversarial prequeries. The full security
objective remains active and unproved.


## Revised roadmap M1: mixed-oracle prefix replay and exact fiber laws

`ObservationReplay.lean` adds truthfulness and counterfactual replay for a
shared log containing SHAKE starts/chunks and complete SHA-512 digest
observations. The native observation type now also admits hash entries.
Truthfulness prevents replay certificates from holding vacuously for an
impossible observation log. The finite footprint counts distinct returned
coordinates across both primitives, retaining repeated calls in the ordered
log. Changing bytes outside that footprint preserves the complete execution.
The primitive hash action uses the same joint world; connecting the existing
Merkle cached handler to this action remains a separate bridge.

Whole-execution replay alone would not establish online query selection.
`OracleProgram.lean` therefore supplies explicit start/read/hash nodes whose
continuations receive results but no world argument. Every finite prefix
returns its actual residual program. Agreement with the observed prefix
preserves its log, residual program, and next request's primitive, complete
input, offset, and count. This proves that the next request is determined
before its response is supplied. The prefix budget is an analysis device,
not an implementation retry cap or a machine-work counter. Unbounded loops
still require compiled compatible prefix families and a completion bridge.

For any certified execution, its exact fiber is proved equal to a finite
coordinate-assignment event in the original product sigma algebra. It is
measurable and has exact mass `(1/256)^(number of distinct returned bytes)`.
Fixing any byte value at a coordinate outside that footprint multiplies the
fiber mass by `1/256`, without division by successful mass or a success-floor
premise. Whole-history use requires the program to include the complete
observed past. Native stage compilers must still establish the required
unobserved-coordinate premise; labels alone do not establish it.

`NativeTranscriptProgram.lean` represents the native-model operations as
online programs. Nine interpretation theorems preserve both the result
and ordered observations for queries, byte challenges, checkpoints,
field starts/reads/receipts/finishes, forks, and child finishes. A linked-child
interface composes an online body between native fork and finish and inherits
prefix replay. The body remains an explicit parameter: the actual typed
lookup protocol has not been compiled or proved secure by this interface.
The equalities relate Lean models; they are not Rust extraction certificates.

Still open: native typed field/basis descriptors, canonical and reciprocal
sampler prefix compilation, arbitrary-input decoder soundness, the actual
linked lookup compiler with whole-history prequeries and stream reuse,
unrestricted stopping/work conversion, full PBS composition, concrete
parameter certification, and checked Rust/scheduler correspondence. The
full security objective remains active and unproved.


Validation passed: focused HasteBoots smoke build (4,069 jobs), separate
warning-as-error HasteBoots smoke, and full `scripts/check` (10,088 build jobs
and all strict suites, terminal exit zero). Twenty-six new guarded audits
passed, bringing the HasteBoots total to 1,415. Dependencies remain within
`propext`, `Classical.choice`, and `Quot.sound`. Regressions cover adaptive
mixed-oracle next-input selection, repeated-read footprint deduplication,
empty-challenge prefix state, observed-byte mutation, and exact adaptive
prefix fiber mass. Logs: `/tmp/hasteboots-replay-smoke.log`,
`/tmp/hasteboots-replay-strict.log`, `/tmp/hasteboots-replay-audit.log`, and
`/tmp/hasteboots-replay-check.log`. Whitespace checks passed. Original Rust
sources, vendor sources, and root dependency pins are unchanged. The complete
security theorem remains unproved; no milestone here discharges the actual
lookup body, unrestricted work conversion, or Rust refinement obligations.


## Revised roadmap M1: canonical native sampler prefix compilation

`CanonicalTranscriptSampler.lean` compiles the canonical rejection subloop
into the online oracle-program language. Each attempt calls the existing
field reader for the configured byte width, decodes little-endian, applies
the native mask (including the full 128-bit branch), and accepts exactly
below the modulus. The source-aligned evaluator and compiled program have
proved identical outcomes and ordered logs. Native callers still require
`1 < p` and `p < 2^128`; the generic mathematical definitions also exist
outside that native domain and do not model invalid-constructor panics.

The byte-list decoder is proved equal to the existing finite-vector decoder.
Zero padding the unread suffix of the native 16-byte scratch array preserves
the decoded value, and that scratch value fits u128. The operational accept
test is exactly the existing canonical masked-vector test. Every accepted
value is proved below the modulus. Full raw chunks are retained, including
rejected candidates and high bits discarded by the mask.

The final field phase contains exactly the previous consumed prefix followed
by all new raw chunks. Reader coherence is preserved. Successful observations
are unchanged by every larger analysis depth, and suspended logs refine to
larger logs. An exact resumption theorem identifies execution at depth
`first + extra` with continuing the first observation, concatenating its
chunks and logs. Suspension emits no receipt. It is not a native rejection,
verification result, or implementation retry limit.

The typed raw observation is proved reachable in the existing private
canonical sampler for every world. This transfers the previously proved
support-level attempt bound and exact suspended attempt count. Actual added
reader bytes equal the earlier trace byte-cost function pointwise; the
unread scratch zeros are not counted as returned bytes. This is neither an
expected-work theorem nor a primitive-to-machine-cost conversion.

The support bridge does not assert equality of distributions for a stage
chosen after adversarial prequeries. That probability bridge still requires
the whole-history first-query compiler and its freshness premises. Also open
are the coefficient/vector collector and field finalization, native typed
basis descriptors, reciprocal/lookup body compilation, arbitrary-input
frame-decoder soundness, unrestricted stopping/work conversion, full PBS
composition, concrete certification, and checked Rust/scheduler refinement.
The full objective remains active and unproved.


Validation passed: focused HasteBoots smoke build (4,070 jobs), separate
warning-as-error HasteBoots smoke, and full `scripts/check` (10,089 build jobs
followed by all strict suites, terminal exit zero). Twenty new guarded audits
passed, bringing the HasteBoots total to 1,435, all within the permitted
standard kernel foundations. Kernel-reduced fixtures cover rejection then
acceptance, ordered rejected-byte retention, no premature receipt, stable
completion at every larger depth, continued suspension, and unused high bits
retained despite masking. Logs: `/tmp/hasteboots-canonical-program-smoke.log`,
`/tmp/hasteboots-canonical-program-strict.log`,
`/tmp/hasteboots-canonical-program-audit.log`, and
`/tmp/hasteboots-canonical-program-check.log`. Whitespace checks passed.
Original Rust sources, vendor sources, and dependency pins are unchanged.
The full security theorem and Rust refinement remain unproved.


## Revised roadmap M1: coefficient collection and one-shot field receipts

`NativeFieldVector.lean` compiles scalar coefficient collection around the
canonical sampler. Its analysis budget counts candidate trials across the
whole vector. Rejection retains the coefficient index; acceptance appends
the canonical natural value and advances the index. The collector keeps
both accepted values and all raw chunks. The online program is proved equal
to its source-aligned evaluator, including ordered observations.

The invariant `remaining + accepted length = requested count` is proved for
requests, including suspended ones. Every returned value is below the
modulus, and a finished request has exactly the requested number of values.
Raw-byte retention, reader coherence, the pending request, and its receipt
label are preserved. Exact resumption concatenates the original logs and
continues with the current coefficient and byte cursor; it does not replay
previous candidates or restart the field request.

Finalization distinguishes suspended from finished requests. A pending
collector emits no receipt. A completed collector emits the native 80-byte
receipt and kind-5 frame once. Resuming a finished request produces no
additional observations. A separate zero-count theorem retains the field
reader start and empty-prefix receipt, even at analysis budget zero. The
prime-vector helper adds the native kind-1 `prime vector` prelude.

This models the scalar collection in `field_values`/`field_build`, with
canonical naturals as values. Typed field conversion, extension grouping,
and the selected basis descriptors remain open. Native callers must also
establish valid modulus and machine-word request-count bounds. Suspension
is an analysis state, not a Rust API return or a verifier rejection.
The request/resume theorems do not introduce a native retry cutoff.

The whole-history distribution bridge, reciprocal and actual lookup body
compilation, arbitrary-input decoder soundness, unrestricted stopping/work
conversion, full PBS composition, concrete certification, and checked Rust
and scheduler correspondence remain open. The full security objective
remains active and unproved.


Validation passed: focused HasteBoots smoke build (4,071 jobs), separate
warning-as-error HasteBoots smoke, and full `scripts/check` (10,090 build jobs
followed by all strict suites, terminal exit zero). Thirty new guarded audits
passed, bringing the HasteBoots total to 1,465, with only permitted standard
kernel foundations. Kernel-reduced regressions cover rejection without
coefficient advancement, partial-vector resumption, no premature receipt,
finished-request idempotence, zero-count finalization, and masked high bits
retained in the raw receipt input. Logs: `/tmp/hasteboots-field-vector-smoke.log`,
`/tmp/hasteboots-field-vector-strict.log`, `/tmp/hasteboots-field-vector-audit.log`,
and `/tmp/hasteboots-field-vector-check.log`. Whitespace checks passed. Rust
revision `dff353006322693cab3dc6b654f82151f658f294` and both inspected transcript
source hashes were rechecked. Rust sources, vendor sources, and dependency
pins are unchanged. This milestone does not complete the security theorem
or the checked Rust correspondence gate.


## Native challenge fields and typed assembly

`NativeExtensionFields.lean` proves irreducibility of the actual native
challenge polynomials: Goldilocks `X^3 - 7` and BabyBear `X^6 - 31`.
Kernel-checked finite-field exponent witnesses establish the required
non-cube and non-square facts. For BabyBear, a norm argument over the
cubic extension excludes a square root of its generator; polynomial
composition then proves the degree-six polynomial irreducible. No extra
irreducibility axiom or external primality/certificate trust is introduced.

The resulting quotient fields have explicit power bases indexed by `Fin 3`
and `Fin 6`, with basis vectors equal to the corresponding generator powers.
Their cardinalities are proved to be the base modulus cubed and raised to
the sixth power. These are the native challenge fields, distinct from the
PCS degree-four/eight symbol fields. This establishes field structure and
size, without inferring a security bound from either cardinality.

`NativeFieldAssembly.lean` converts a length-checked list of accepted
canonical integers into indexed base-field coefficients. The canonical
representative of each converted value equals the original integer under
the established `< p` bounds. Extension assembly preserves every
coordinate at flat offset `coordinate + degree * element`. The
`finished_request_coordinate` theorem obtains both length and bounds from
the actual completed `NativeFieldVector.request`, including its native
receipt, for every world and finite analysis budget. Concrete assembly
functions use the newly proved Goldilocks degree-three and BabyBear
degree-six power bases. Assembly is pure and issues no oracle operations.

This closes the mathematical field-existence and typed-coordinate grouping
part of M1. It does not prove Rust lazy/Montgomery representation conversion,
extension-basis descriptor byte agreement, valid native request sizes, or
the whole-history conditional distribution bridge. Those obligations,
the actual lookup compiler, unrestricted stopping/work conversion, full
PBS security composition, concrete parameter certification, and checked
Rust/scheduler correspondence remain open. The final security theorem
remains unproved.


Validation passed: focused HasteBoots smoke (4,074 jobs), a separate
warning-as-error HasteBoots smoke, and full `scripts/check` (10,092 jobs
and every subsequent strict suite, terminal exit zero). Fourteen new
guarded theorem audits passed, bringing the HasteBoots total to 1,479;
all use only the permitted `propext`, `Classical.choice`, and `Quot.sound`
foundations. Regressions check native cardinalities and cross-element
coordinate offsets for both extension fields. Logs are
`/tmp/hasteboots-native-assembly-{build,audit,smoke,strict,check}.log`.
The inspected Rust revision and transcript hashes remain unchanged;
Rust sources, vendor sources, and dependency pins were not modified.
