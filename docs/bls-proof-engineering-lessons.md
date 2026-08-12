# BLS12-381 Lean Proof Engineering Lessons

This document records reusable lessons from the BLS12-381 precompile proofs.
It is intentionally organized so it can later become the reference material
for a proof-engineering skill. It records observed failures and successful
responses; it is not a claim that every proposed architectural improvement has
already been implemented or benchmarked.

## Contents

1. [Scope and current status](#scope-and-current-status)
2. [The central root cause](#the-central-root-cause)
3. [Three different kinds of memory pressure](#three-different-kinds-of-memory-pressure)
4. [Why physical files help](#why-physical-files-help)
5. [Why physical files are not the complete fix](#why-physical-files-are-not-the-complete-fix)
6. [Observed incidents](#observed-incidents)
7. [Architectural patterns that work](#architectural-patterns-that-work)
8. [Import-boundary lessons](#import-boundary-lessons)
9. [Check and policy lessons](#check-and-policy-lessons)
10. [Certificate lessons](#certificate-lessons)
11. [Measurement workflow](#measurement-workflow)
12. [Debugging workflow](#debugging-workflow)
13. [What not to do](#what-not-to-do)
14. [Recommended migration sequence](#recommended-migration-sequence)
15. [Candidate future skill shape](#candidate-future-skill-shape)

## Scope and current status

- G1ADD and G2ADD are the completed BLS precompile proof trees.
- G1MSM and G2MSM contain partial agent work that was stopped because the file
  count had grown too large.
- G1MSM and G2MSM are paused. Do not resume or refactor them as a side effect of
  work on completed ADD challenges.
- Map-to-curve and pairing scaffolding are separate challenge work and must not
  be pulled into ADD proof closures merely because they share BLS mathematics.
- The objective is not the fewest physical files. It is the smallest public
  conceptual graph that still has enough private compiled boundaries to keep
  elaboration bounded.

At the reviewed commit range, BLS work added approximately 1,634 files and
124,691 lines relative to the merge base with `origin/main`. About 556 files
were checks, and about 576 belonged to other BLS challenge work, primarily the
paused MSM trees. The completed G1ADD/G2ADD and shared support account for a
minority of the total file count.

## The central root cause

The worst memory spikes occur when a theorem asks Lean to relate two enormous
reducible computations simultaneously:

```text
expanded Yul/EVM execution state
        =
expanded limb/field/curve computation
```

The mathematical statement can be simple while elaboration is not. During
unification, definitional equality, `simp`, `rw`, `change`, or projection
reduction, Lean may materialize substantial portions of both graphs:

- source syntax and interpreter control flow;
- nested `EvmState` updates;
- memory reads, writes, and framing facts;
- 256-bit word conversions;
- 381-bit constants in several representations;
- schoolbook multiplication and reduction schedules;
- field and curve operations; and
- dependent branches containing both outcomes.

The root solution is to ensure those giant graphs are never presented together
to one declaration. Module splitting helps cache intermediate results, but the
proof interface must also change.

## Three different kinds of memory pressure

Treat these as separate failure modes.

### One declaration expands two large representations

Symptoms include long time in weak-head normalization, no proof state before
RSS grows, sensitivity to an apparently harmless type annotation, and large
differences between a generic theorem and its concrete-numeral specialization.

Remedies:

- name semantic intermediate values;
- split branch conditions before unfolding implementations;
- prove exact projection equations;
- use targeted `rw` or `simp only`;
- publish deep operation contracts; and
- relate interpreters of one authoritative program where practical.

### Several acceptable Lean processes peak together

A module that peaks at 3 GiB may be acceptable alone and fatal when four such
jobs run concurrently.

Remedies:

- build heavy targets with `lake -Kjobs=1`;
- ensure no unrelated Lean workers are active during measurement;
- separate CI jobs and caches by challenge; and
- avoid broad default builds while developing a leaf theorem.

### Ambient compiled environment is unnecessarily large

Broad imports bring many compiled declarations and instances into every
consumer even if no giant definition is unfolded.

Remedies:

- import precise stable contracts;
- keep executable definitions separate from Mathlib-heavy lawful proofs;
- keep challenge roots separate; and
- use the all-inclusive umbrella only for aggregate checks or interactive
  convenience, not production proof leaves.

Narrow imports address the third failure mode. They reduce baseline RSS and
rebuild cost, but they do not by themselves fix a single pathological theorem.

## Why physical files help

A compiled `.olean` is an effective opacity and caching boundary. Downstream
proofs can use a theorem without reconstructing its proof or normalizing the
implementation it characterizes.

Useful physical boundaries include:

- arithmetic stages with large constants or carry graphs;
- execution separated from representation refinement;
- source definitions separated from interpreter proofs;
- branch-specific execution stages;
- prime and root certificate evidence;
- byte-assembly and stack-certificate chunks; and
- final composition modules that consume already compiled facts.

A small source file may still be valuable. Some tiny prime/root certificate
sources produce multi-megabyte `.olean` files; their source line count is a
poor proxy for their kernel payload or elaboration role.

## Why physical files are not the complete fix

Splitting every failed declaration into a new file can turn an elaboration
emergency into repository structure. It treats the immediate symptom while
creating navigation and maintenance costs.

The stronger design uses:

### Compositional stage contracts

Separate execution, result, frame, and gas facts:

```lean
theorem operation_exec : Runs code initial final
theorem operation_result : readResult final = mathematicalResult
theorem operation_frame : UnchangedExcept scratch initial final
theorem operation_gas : gasUsed initial final = cost
```

Compose these contracts without reopening the expanded implementation.

### One deep theorem per arithmetic operation

A consumer-facing operation theorem should bundle the invariants callers need:

```lean
theorem Fp.mul_contract {a b : Fp.Limbs}
    (ha : Fp.Canonical a) (hb : Fp.Canonical b) :
    Fp.Canonical (Fp.mulCanonical a b) ∧
      Fp.toField (Fp.mulCanonical a b) = Fp.toField a * Fp.toField b
```

Downstream code should not need to import or unfold schoolbook products,
Barrett/Montgomery rounds, carries, or constants.

### One authoritative parametric program

Where possible, define one operation and interpret it as:

- executable limb computation;
- audited/tracing computation;
- source/Yul computation; and
- mathematical computation.

Correctness then becomes interpreter refinement rather than equality between
two independently written expanded programs. `Fp2SourceProgram.lean` and
`ScalarMulProgram.lean` already demonstrate this pattern.

### Relational summaries instead of full states

Track selected stack values, named memory regions, gas delta, halt/result
status, and a frame condition for everything else. Connect the relational
layer to concrete big-step execution once. Do not reconstruct a complete state
graph at every semantic step when most fields remain unchanged.

## Observed incidents

### G1ADD field subtraction

An all-at-once refinement between source subtraction and shared limb
subtraction grew to approximately 19.8 GiB RSS without finishing after roughly
50 seconds. The successful staged proof completed around 2.7 GiB RSS.

The successful stages named and related:

```text
raw subtraction
    -> repair predicate
    -> conditional modulus repair
    -> final value
```

The source evaluator was not the expensive part. The expensive boundary was
the equality between two complete reducible representations before their
intermediate values and branch predicates had been aligned.

### G2 inversion chain

A low-memory-looking monolithic inversion chain reached approximately 14.2
GiB. Splitting square, scalar, real, negation, imaginary, and store stages kept
individual stages near 3.4 GiB.

Lesson: a mathematically linear operation can still construct a huge symbolic
state graph. Split at semantic values and memory contracts, not arbitrary line
counts.

### Fp2 interpreter-to-EVM equality spike

On 2026-08-12, the first Fp2 contract migration tried to identify the frozen
G2ADD `fp2Mul` final output with `Fp2.mulSource`, the direct interpreter of the
authoritative parametric program:

```lean
fp2At (fp2MulFinalState yst out a b) out =
  Fp2.mulSource left right
```

The left side contains the concrete staged EVM state; the right side contains
the reducible interpreter and limb arithmetic. Direct component extensionality
followed by `rfl` timed out at the default 200,000 heartbeats. Moving the
projection into shared `Fp2SourceSchedule` and proving it by `rfl` also timed
out. Replacing `rfl` with `runMulWith_id_eq` and a `simp only` list of named
primitive projections still materialized the reducible graph: the Lean process
reached about 16.7 GiB RSS after 44 seconds and was terminated.

The experiment was restored to a compiling state. No heartbeat was raised and
no stage file was removed. The safe part remains: `Fp2.mulSource_spec` bundles
canonicality and mathematical meaning for callers already at the `mulSource`
boundary. The concrete G2ADD consumer was not migrated.

This shows that opacity at a theorem name is insufficient when elaborating the
theorem itself requires the giant equality. The next G2 attempt must use a
relational stage summary whose hypotheses and result name selected values and
memory regions. It must not equate a complete EVM-derived result with a
reducible interpreter computation.

### G1MSM whole-program execution

Whole-program interpreter soundness reached approximately 8.3 GiB. Relational
prefix/tail composition reduced the observed leaf peak to about 2.6 GiB.

Lesson: compose execution relations rather than normalize the whole source
program in one theorem. The MSM work remains paused despite this local lesson.

### G1MSM projection refinements

Subtraction output/context projection attempts ranged from roughly 7 to 12
GiB. Generic value-only context theorems and cached smart-constructor
projections reduced successful leaves to around 3.5 GiB.

Lesson: projection from a large reducible state can be as expensive as the
operation itself. Export named projection theorems.

### G2MSM compiler equality and certificates

A monolithic compiler equality reached about 8.3 GiB. Frozen normalized AST,
assembly, byte, and stack chunks produced leaves in the approximate 2 to 5.2
GiB range. An optimizer equality aggregate reached about 6.3 GiB and required
opaque half-aggregators plus a shallow final composition.

Lesson: closed computations and generated evidence need bounded, genuinely
linear representations and shallow composition. The MSM tree remains paused.

### Completed ADD broad-import leak

Both challenge-level support modules imported their narrow `Spec` and then the
complete shared BLS proof umbrella. Their four local EVM state/config lemmas
used only the `Spec` dependency.

Warm standalone measurements before and after omitting the umbrella:

| Module | Broad umbrella | Narrow import | Reduction |
| --- | ---: | ---: | ---: |
| G1ADD `ProofSupport.lean` | about 3.22 GiB | about 2.18 GiB | about 1.04 GiB |
| G2ADD `ProofSupport.lean` | about 3.22 GiB | about 2.48 GiB | about 0.74 GiB |

These are directional warm elaboration measurements, not controlled cold-build
results.

### Hidden transitive import: `Fp.mulCanonical`

After removing the umbrella, a full G1ADD rebuild failed in
`SourceOnCurveRefinement.lean`. The module used `Fp.mulCanonical`,
`canonical_mulCanonical`, and `toField_mulCanonical` without directly importing
their owner, `FpMul.lean`.

The standalone challenge `ProofSupport.lean` probe passed because it did not
exercise this downstream source file. Only the final-root rebuild revealed the
dependency leak.

Lesson: a narrow import refactor must rebuild the final consumer tree, not just
the edited module. Add the exact owning import at the use site.

The same issue then appeared in G2ADD's `SourceFpModexpDefs.lean`, which reused
G1ADD's Fp execution/refinement helpers but added its own equality to
`Fp.mulCanonical`. Reusing a module that proves a related result does not imply
that the consumer imports every owner needed for new declarations it adds.
`SourceFpModexpDefs.lean` also needed its own explicit `FpMul.lean` import.

### Misowned representation bridge: `Fp.finEquiv_toField`

The next G1ADD rebuild failed because source on-curve refinements used the
generic theorem `Fp.finEquiv_toField`, but that theorem lived in the heavy
`FpMontgomeryLawful.lean` module. The broad umbrella had hidden this ownership
mistake.

Adding a direct import of the heavy Montgomery module would have made the build
pass but weakened the intended boundary. The theorem is an `rfl` bridge between
the Fp representation and the lawful prime field, so it belongs with the
canonical Fp/prime-field predicate boundary. It was moved, without changing its
name or statement, to `FpPredicates.lean`, which callers already import.

Lesson: when import narrowing reveals repeated missing symbols, do not blindly
add heavy imports. Check whether the declaration is owned by the wrong module.

### Late hidden codec dependencies

The G2ADD final-root rebuild progressed through almost the entire source tree
before two codec dependencies failed:

- `SourceMainPostOutput.lean` used `Codec.encodeG2` without importing its
  minimal owner, `CodecG2Core.lean`.
- `SourceInputCodec.lean` used
  `Codec.decodeFp2_eq_some_iff_components` without importing its owner,
  `CodecFp2.lean`.

Both files had compiled previously because the challenge-level broad umbrella
made the names ambient. The repair was to import the exact codec leaf, not the
full G2 codec or shared umbrella.

Lesson: hidden dependencies may not appear until very late in a final-root
rebuild. Continue until the actual final theorem has rebuilt; a mostly green
tree is not sufficient evidence.

### Narrow-import refactor verification on 2026-08-12

After repairing the explicit Fp and codec dependencies:

- the G1ADD final-correctness root rebuilt successfully;
- a fully cached G1ADD confirmation exited zero in about 1.0 seconds with
  approximately 0.89 GiB maximum RSS;
- the last G2ADD rebuild segment compiled its remaining source-spec and final
  modules successfully in about 14.9 seconds with approximately 2.84 GiB
  maximum RSS;
- `Checks.Bls12381G1Add` and `Checks.Bls12381G2Add` both built successfully;
  and
- the tested policy scanner accepted both completed challenge trees after the
  broad imports were removed.

These figures do not form a clean before/after cold benchmark. Dependencies
were progressively cached while hidden imports were repaired, and a Lean
language server was active. Retain the standalone warm import comparison as
directional evidence and perform a separately controlled cold comparison
before making a stronger performance claim.

### Conservative source-policy scanner

The proof-policy scanner intentionally scans raw source, including comments and
strings. When the G1ADD CI gate was migrated from a word-boundary `grep` to the
shared scanner, the prose word `admits` was rejected because it contains a
forbidden raw substring.

Lesson: policy migrations can reveal existing violations that the old check did
not cover. Reword prose rather than weakening a deliberately conservative raw
scanner. Self-test path-sensitive policy rules before applying them to the
repository.

### Tool output can yield before a build finishes

A long-running build command may yield output while its `lake` process remains
active. Treat a yielded log as progress, not completion. Check the session or
process table and wait for the actual exit status and `/usr/bin/time` summary.

Lesson: never report a build as passing merely because many targets printed
green lines. Require final exit status zero.

### zsh reserves the lowercase `path` variable

In zsh, assigning to `path` mutates the array tied to the executable search
`PATH`. A diagnostic loop that used `path` for a Lean module filename caused
later `rg`, `sed`, `head`, and `paste` commands in the same shell to become
unavailable.

Lesson: use task-specific shell variable names such as `proof_module_path` or
`check_file`. Avoid `path`, `status`, and other shell-special or system option
names in repository automation.

### zsh rejects unmatched globs by default

After deleting a check cluster, passing its now-unmatched `*.lean` pattern to a
command caused zsh to fail before `git diff` ran. Quote pathspecs intended for
Git or use `find` when an empty match set is valid:

```sh
git diff --stat -- 'Checks/Bls12381G2AddSourceFp2InvLow*.lean'
```

Lesson: distinguish shell expansion from tool-owned pathspec expansion,
especially when verifying deletions.

## Architectural patterns that work

### Deep operation contract

Expose canonicality, representation refinement, and mathematical meaning in
one consumer theorem. Keep internal proof stages private and compiled.

### Semantic-stage split

Split at decoded input, canonical field value, completed arithmetic primitive,
branch result, stored output, or gas boundary. Avoid arbitrary file sizes as
the primary split criterion.

### Definition/proof split

Keep runtime definitions free of broad tactic and Mathlib algebraic-geometry
imports. Put lawful group/field bridges in proof-only modules that depend on
runtime definitions, never the reverse.

### Exact rewrites

Prefer:

- `rw` with a named projection theorem;
- `simp only` with an audited list;
- explicit branch splitting; and
- a small `change` at a definitionally equal boundary.

Avoid asking broad simplification or unification to discover a relationship
between two expanded implementations.

### Generic lemma before large constant

Prove word split/join, carry, borrow, modular congruence, and fold invariants
generically. Instantiate the 381-bit modulus through an opaque theorem.

### Private physical graph, small public graph

Treat a public module as a concept and an internal module as a compilation
boundary. A subsystem may legitimately have many private `.olean` firebreaks
while exposing only a few stable contracts.

### First bundled Fp contract spike

The first deep arithmetic-contract slice added `Fp.mulCanonical_spec` to the
existing `FpMul` module. Given canonical operands, one opaque theorem returns:

```lean
Fp.Canonical (Fp.mulCanonical a b) ∧
  Fp.toField (Fp.mulCanonical a b) = Fp.toField a * Fp.toField b
```

No facade or production-stage file was added. The local
`fpMulOutput_eq_mulCanonical` helper in G1ADD `SourceOnCurveRefinement` was
migrated from separate `canonical_mulCanonical` and
`toField_mulCanonical` calls to one destructuring call to the bundled
contract. The contract has the same guarded trust footprint as its components:
`propext`, `Classical.choice`, and `Quot.sound`.

A warm single-job A/B build of the migrated leaf measured 2,423,616 KiB RSS
for the old consumer and 2,424,392 KiB for the bundled consumer, both at 1.90 s
wall time. A Lean language-server worker was active during both measurements.
This difference is noise: the slice is memory-neutral, not evidence of a memory
reduction. Its value is the stable consumer boundary and one fewer opportunity
for downstream proofs to depend on separate implementation facts. Imports were
unchanged, so the transitive dependency closure did not grow. No proof-stage
file became redundant from this spike alone.

The post-migration single-job boundary rebuilds also passed. G1ADD final
correctness plus its shared-Fp and permanent gates completed 2,302 jobs in
50.43 s at 3,126,220 KiB peak RSS. Because `FpMul` is shared, G2ADD final
correctness and all four permanent gates were rebuilt as well: 2,491 jobs in
2:29.21 at 3,073,196 KiB peak RSS. These are post-change verification figures,
not before/after performance comparisons.

### First bundled Fp2 contract boundary

`Fp2.mulSource_spec` now bundles output canonicality and field meaning for the
direct interpretation of the authoritative Fp2 source program. It lives in the
existing `Fp2SourceLawful` module, adds no facade file, and has the guarded
axiom footprint `[propext, Classical.choice, Quot.sound]`.

Unlike the Fp spike, the first concrete G2ADD migration was intentionally
rolled back after the interpreter-to-EVM bridge reached about 16.7 GiB RSS.
Therefore this contract is a valid shared boundary but not yet evidence that a
G2ADD proof stage can consume it safely.

After restoring the safe boundary, G2ADD final correctness, the shared Fp2
contract check, and all permanent G2ADD gates rebuilt successfully in 1:35.28
at 2,907,560 KiB peak RSS. This is a post-change verification figure, not a
performance comparison with the rejected bridge.

### Safe G2 Fp2 multiplication bridge

The accepted follow-up does not prove that the concrete frozen result equals
`Fp2.mulSource` as a representation. `Fp2MulLowContract` instead bundles:

- the complete staged `fp2Mul` expression evaluation;
- canonicality of the selected output;
- equality with `mulSource` only after applying `Fp2.toField`;
- the lawful multiplication equation; and
- preservation of every selected 32-byte word below the scratch region.

The field-projected bridge composes the existing opaque concrete result theorem
with `Fp2.mulSource_spec`. Lean never unfolds or compares the two full
implementations. The first `onCurveY2` caller now consumes the contract's
canonicality and lawful-result projections rather than calling the individual
stage theorems itself. No facade or production file was added.

The boundary check was written first and failed on the absent contract. The
producer leaf moved from 2,704,512 to 2,713,660 KiB RSS; the migrated caller
moved from 2,717,384 to 2,710,556 KiB. Both differences are noise. The contract
has the guarded trust footprint `[propext, Classical.choice, Quot.sound]`. The
full G2ADD root and all 46 retained checks passed 2,534 jobs in 1:25.67 at
2,897,300 KiB peak RSS. A per-process monitor observed 2,881,032 KiB and never
crossed the 6 GiB stop threshold.

A virtual-address limit is not a valid substitute for RSS monitoring. Applying
`ulimit -v 6291456` caused Lean to fail while mapping a Mathlib `.olean.private`
artifact at only 816,500 KiB RSS. For memory stop rules, run the proof in an
isolated process group, sample the maximum resident set of each process, and
terminate the group if a Lean process crosses the threshold. Do not sum RSS
across the group because shared mapped pages are counted once per process.

This slice avoids the known 16.7 GiB equality failure but does not make the
staged multiplication modules obsolete. They remain the implementation of the
compact contract and the exact states remain necessary for subsequent source
execution.

### First relational G1ADD stage contract

The first complete relational slice used the G1ADD both-infinity return path.
It added `MainBothInfinityContract yst final` to the existing `SourceRun`
module rather than adding a facade or contract file. Its result state is
existential. The public fields expose:

- the complete frozen-source `Run`;
- the selected return bytes and `.ret` halt status;
- unchanged memory across the final return;
- the exact permitted active-word expansion; and
- frame equalities for storage, transient storage, environment, returndata,
  logs, and selfdestructs.

The exact `mainBothInfinityReturnState` is used once to construct the contract,
then hidden. The complete both-infinity branch in `SourceSpec` now consumes
only `contract.run` and `contract.returned_inputWindow`; it no longer names the
expanded final state.

This spike also clarified the source/compiler boundary. Yul
`YulSemantics.EVM.EvmState` does not contain gas. A truthful source-stage
contract cannot state a gas delta. Gas remains a separate compiled-EVM
schedule/refinement contract and should be paired with the source contract
where compiler correctness connects the two semantics.

A blanket `all_goals rfl` while building the frame hit Lean's maximum recursion
depth. The successful proof used only
`simp only [mainBothInfinityReturnState, touchMemory]`, projecting through two
shallow record updates without reducing `mainValidatedState`. The focused leaf
compiled in 1.82 s at 2,760,112 KiB RSS. The new theorem's guarded axiom census
is unchanged: `[propext, Classical.choice, Quot.sound]`.

A warm single-job build of the entire G1ADD root and all 43 G1ADD checks passed
2,342 jobs in 10.03 s at 2,721,348 KiB peak RSS with an active Lean
language-server worker. That is below the earlier 3,126,220 KiB post-Fp
verification figure, but is not a controlled cold A/B claim. The important
result is architectural: a complete spec consumer now depends on an
existential selected-field contract, with no new file and no larger import
closure. The underlying exact-state stages are not yet obsolete because they
still implement the bridge and serve other branches.

### Reusing the relational contract for first-infinity

The second relational slice generalized the branch-specific structure into
`MainReturnContract yst beforeReturn final offset size`. The original
`MainBothInfinityContract` is now a transparent specialization at the
validated state. `MainFirstInfinityContract` specializes the same interface at
the state after copying the second input point into the output window. This
keeps one deep interface for complete source execution, return bytes, active
memory expansion, and frame preservation rather than adding a new structure
for each branch.

The boundary check was written first and failed because the first-infinity
contract and constructor theorem did not exist. After implementation,
`SourceSpec` stopped naming `mainFirstInfinityReturnState`; it consumes only
`contract.run` and `contract.returned_affineIdentity`. The exact copy-and-return
state remains private to the bridge proof.

Direct single-process elaboration of `SourceRun.lean` moved from 2,759,628 KiB
to 2,761,184 KiB RSS, a 1,556 KiB (0.06%) difference that is measurement noise.
The new theorem retains the guarded footprint `[propext, Classical.choice,
Quot.sound]`. The full G1ADD root and all 43 retained checks passed 2,342 jobs
at 2,716,696 KiB peak RSS. No production stage became obsolete: the
first-infinity exact-state chain still implements the relational bridge once.

## Import-boundary lessons

1. Never import `Challenge.Bls12381.ProofSupport` from completed challenge proof
   trees. Import the exact codec, field, affine, or representation contract.
2. Keep the broad umbrella for aggregate checks or interactive convenience.
3. Rebuild final correctness after removing a broad import; edited-leaf success
   is insufficient.
4. When a symbol disappears, locate its owning module with `rg` before adding
   an import.
5. If several callers need a simple general theorem from a heavy specialized
   module, reassess theorem ownership.
6. Do not introduce wrapper facades when existing leaf modules already express
   the capability. A wrapper adds a file without reducing transitive closure.
7. Add a new facade only when at least two active consumers share a meaningful
   contract.
8. Do not use paused MSM work to justify imports or abstractions in completed
   ADD challenges.

## Check and policy lessons

Fine-grained checks are useful during red/green development, but retaining one
file for every internal theorem makes private structure permanent.

Classify checks as:

- public API/type boundary;
- final trust census;
- conformance or branch behavior;
- frozen artifact identity;
- certificate validity;
- resource regression; or
- temporary internal theorem restatement.

Before deleting a check:

1. identify its observable purpose;
2. move any unique assertion to a permanent boundary gate;
3. run the permanent gate and see it protect the behavior;
4. remove only covered restatements; and
5. rebuild final trust roots.

Prefer a focused axiom census rooted at final correctness, gas, field/curve
bridge, and certificate-soundness theorems. Do not relax the ban on untrusted
or compiled-evaluation shortcuts in the core proof path.

Permanent gates should import production boundaries directly. A check that
imports another check hides which gate owns an assertion, makes deletion
coverage harder to audit, and can turn a nominal gate into a forwarding file.
For completed challenges, reject check-to-check imports with a scoped policy
rule, copy unique final-root assertions into the owning permanent gate, verify
the exact axiom messages, and only then remove the forwarding check.

Policy-check implementation lessons:

- write the failing self-test before changing the scanner;
- scope path-sensitive rules by path components, not fragile string prefixes;
- prove narrow leaf imports remain accepted;
- prove direct production imports remain accepted while check-to-check imports
  are rejected;
- scan both source and check trees in CI; and
- use the same scanner in analogous challenge gates to prevent policy drift.

The completed-ADD cleanup ultimately removed 131 check files: two forwarding
final-correctness checks and 129 G2ADD signature-only wrappers. The wrappers
contained only internal `#check` lookups; all production modules behind them
remained in final-correctness closure. Completed-ADD checks fell from 220 to 89
(43 G1ADD and 46 G2ADD) without removing a production proof module or `.olean`
barrier. A CI-shaped build of the G2ADD root and all remaining checks passed
2,534 jobs at 2,732,800 KiB peak RSS, together with the proof and cache policy
self-tests.

An import-graph scan also found no obsolete production stage: all 115 G1ADD
and all 229 G2ADD challenge modules remain reachable. Single-inbound modules
are not automatically redundant. In this codebase they include bounded
certificate chunks and the staged low-memory arithmetic paths that replaced
14-20 GiB monoliths. File-count cleanup must distinguish disposable test
wrappers from semantic `.olean` firebreaks.

A later certificate-boundary consolidation removed one production module per
completed challenge. The count is now 114 G1ADD and 228 G2ADD modules when the
top-level challenge entry point is included (113 and 227 below the respective
challenge directories). These were not arithmetic or execution firebreaks:
each deleted `StackCertificateSound.lean` merely imported the already
aggregated chunk proof and instantiated the generic soundness API. Moving that
unchanged bridge into `StackCertificateChunks.lean` preserves all individual
chunk `.olean` barriers.

## Certificate lessons

A certificate that stores the complete remaining program suffix at every
instruction is quadratic:

```text
n + (n - 1) + ... + 1
```

Prefer instruction indices, stack heights, compact local facts, and a generic
kernel-checked checker. Generated data is not trusted; a small soundness theorem
must validate it.

Keep challenge-local:

- frozen source, assembly, and bytes;
- generated certificate entries;
- bounded data/check chunks; and
- artifact identity hashes.

Share under `Challenge.EvmProof`:

- compact certificate representation;
- local checker;
- chunk composition lemmas;
- thawing/lookup logic; and
- one soundness theorem.

Do not concatenate all chunks into a giant reducible source term. Compose
opaque chunk summaries with a shallow theorem.

### Generic compact checker extraction

The completed ADD challenges originally duplicated both a roughly 100-line
finite checker core and a 224-line soundness bridge. The accepted extraction
puts the generic representation, checker, chunk-composition lemma,
suffix-restricted certificate, validity/boundedness proof, and final stack
bound in `Challenge.EvmProof.StackCertificate`. G1ADD and G2ADD retain their
frozen programs, numeric data, bounded decision chunks, and original public
theorem names.

Do not automatically put a new shared module in a broad umbrella. The compact
checker is imported precisely by its two ADD consumers and shared trust check;
unrelated bytecode proof support does not inherit the compiler stack-analysis
closure.

An all-`abbrev` compatibility layer initially kept chunk checking green but
broke both soundness files. Their deliberately scoped `unfold` and `dsimp`
steps used local data-projection names to control reduction. Retaining three
tiny local projections while sharing the large algorithms restored the proofs.
This is the appropriate trade: a handful of duplicated constructor lines can
be proof firebreaks even when the semantic algorithm should live once.

Warm before/after leaves were memory-neutral. G1 chunk 0 moved from
3,489,692 to 3,489,648 KiB RSS; a repeated G2 chunk 0 moved from 3,997,984 to
3,970,804 KiB. G1/G2 soundness moved from 2,444,200/2,111,160 KiB to
2,410,840/2,062,832 KiB. The shared axiom footprints match the old adapters.
Full shared, G1ADD, and G2ADD gates passed after extraction.

### Removing shallow certificate adapters

After the shared extraction, the aggregate `StackCertificateChunks.lean`
module already imported every bounded chunk and proved
`referenceStackLengthEntryChecks`. The remaining soundness module contained
only 72 lines that instantiated shared theorems from that aggregate result.
It was therefore safe to move those declarations into the aggregate module
and point compiler correctness and trust checks at it directly.

The characterization checks were changed first and failed on the missing
soundness names. After the declarations moved, both checks passed with their
exact axiom messages unchanged. Single-job aggregate-plus-check builds peaked
at 2,458,036 KiB for G1ADD and 2,127,740 KiB for G2ADD. Compiler correctness
also rebuilt successfully, followed by the public roots and every retained
check (2,342 G1ADD jobs and 2,534 G2ADD jobs). This is the useful deletion
rule: remove a module when it is only a shallow adapter above an already
aggregated opaque result.
Do not use this result to justify concatenating the bounded data/decision
chunks that feed that result.

## Measurement workflow

Before changing a proof boundary:

1. inspect `git status --short` and preserve unrelated user changes;
2. inspect active `lean`/`lake` processes and available memory;
3. select the narrowest representative target;
4. record commit, Lean version, cache state, command, other workers, elapsed
   time, maximum RSS, and exit status;
5. use `lake -Kjobs=1` for heavy proof roots;
6. stop and restage a declaration trending toward 6 GiB RSS;
7. compare cold with cold or warm with warm; and
8. distinguish source LOC, `.olean` size, import closure, runtime performance,
   and proof RSS.

Suggested command:

```sh
/usr/bin/time -v lake -Kjobs=1 build +Exact.Module.Target
```

Do not delete a shared build cache while another worker may use it. Use an
isolated worktree or build directory for a controlled cold measurement.

## Debugging workflow

When narrowing imports or changing a deep boundary:

1. **Reproduce at the smallest failing target.** Record the first unknown
   identifier or normalization boundary.
2. **Trace ownership.** Use `rg` to locate the declaration and inspect the
   complete owning module's imports.
3. **Form one hypothesis.** Decide whether the caller lacks a precise import,
   the declaration is misowned, or the proof relied on accidental reducibility.
4. **Test minimally.** Add one precise import, move one unchanged general
   theorem, or replace one broad simplification with one exact bridge.
5. **Build the leaf.** Require an actual zero exit status.
6. **Build the final root.** Hidden transitive dependencies often appear only
   in downstream recompilation.
7. **Question the architecture after a repeated pattern.** If successive files
   fail on the same heavy module, do not keep adding the heavy import. Establish
   a deep contract or correct ownership.
8. **Record the incident.** Include failed approach, observed RSS/error,
   successful boundary, and why it worked.

## What not to do

- Do not respond to OOM by merely raising heartbeats or memory limits.
- Do not assume `-Kjobs=1` fixes a single giant term.
- Do not combine files merely to lower the count.
- Do not delete checks merely to lower the count.
- Do not use a broad umbrella to make missing imports disappear.
- Do not add a heavy import before checking whether a general theorem is
  misowned.
- Do not use unrestricted `simp`, `unfold`, `dsimp`, or whole-program reduction
  across a large representation boundary.
- Do not introduce an independent duplicate implementation if one parametric
  program can support multiple interpreters.
- Do not use compiled/native decision shortcuts as evidence for exact EVM
  semantics.
- Do not resume G1MSM/G2MSM during ADD cleanup.
- Do not claim success from partial build logs; require exit status zero.

## Recommended migration sequence

1. Remove accidental broad imports from completed G1ADD/G2ADD roots.
2. Enforce the boundary with a tested, scoped policy rule.
3. Rebuild final roots and repair hidden dependencies with precise imports or
   corrected theorem ownership.
4. Inventory checks and define permanent public/trust/conformance/artifact/
   resource gates.
5. Consolidate one representative covered check cluster.
6. Publish one deep Fp operation contract and migrate one G1ADD source helper.
7. Publish one deep Fp2 operation contract and migrate one G2ADD source helper.
8. Spike a relational state/stage contract on one complete G1ADD branch.
9. Remove only proof-stage files demonstrated redundant by the new contracts.
10. Extract the generic compact certificate framework after baselining G1 and
    G2 chunks and final soundness.
11. Keep G1MSM/G2MSM paused until architecture and file-count policy are
    explicitly reopened.

## Candidate future skill shape

A future skill should be concise and action-oriented. Suggested name:
`engineer-memory-bounded-lean-proofs`.

Suggested trigger contexts:

- a Lean proof consumes several GiB or fails during normalization;
- concrete EVM/Yul execution is being refined to arithmetic semantics;
- an agent proposes splitting or merging many Lean files;
- a broad import is masking proof dependencies;
- generated compiler certificates are growing rapidly; or
- BLS field/curve proof architecture is being changed.

Suggested skill contents:

```text
engineer-memory-bounded-lean-proofs/
├── SKILL.md
├── agents/openai.yaml
├── references/
│   ├── incidents.md
│   ├── architecture.md
│   └── measurement.md
└── scripts/
    └── measure-lean-target.sh
```

Keep the core workflow and stop conditions in `SKILL.md`. Move the detailed
incidents in this document into `references/incidents.md`, architectural
patterns into `references/architecture.md`, and controlled build methodology
into `references/measurement.md`. A deterministic measurement script should
record command, commit, toolchain, cache-state label, wall time, maximum RSS,
and exit status without deleting shared artifacts.

Before creating the skill, agree its install location, initialize it with the
standard skill scaffold, generate its UI metadata from the final instructions,
validate it, and forward-test it on a raw failing proof artifact without
leaking the expected diagnosis.
