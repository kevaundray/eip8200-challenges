import Challenge.Ripemd160.Reference.Proofs.Bytecode.EntryTemplates
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat pc }

def mainStart (input : ByteArray) : State := atPC input 0x03ef

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-! The `path_*` definitions are compatibility views of the corresponding
`Artifact.entryPath_*` selected-site segments. New execution proofs should use
the selected-site paths, which carry compact decoder certificates. -/

def path_start : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨20, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨21, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2e), by rfl, by decide⟩,
   ⟨22, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_2e : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨35, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨36, .push ⟨2, by decide⟩ (UInt256.ofNat 0x46), by rfl, by decide⟩,
   ⟨37, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_46 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨52, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨53, .push ⟨2, by decide⟩ (UInt256.ofNat 0x5a), by rfl, by decide⟩,
   ⟨54, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_5a : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨67, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨68, .push ⟨2, by decide⟩ (UInt256.ofNat 0x73), by rfl, by decide⟩,
   ⟨69, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_73 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨83, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .push ⟨2, by decide⟩ (UInt256.ofNat 0x8e), by rfl, by decide⟩,
   ⟨85, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_8e : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨105, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨106, .push ⟨2, by decide⟩ (UInt256.ofNat 0x10f), by rfl, by decide⟩,
   ⟨107, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_10f : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨205, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨206, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b2), by rfl, by decide⟩,
   ⟨207, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b2 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨313, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨314, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1db), by rfl, by decide⟩,
   ⟨315, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1db : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨346, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 0x231), by rfl, by decide⟩,
   ⟨348, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_231 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨410, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, .push ⟨2, by decide⟩ (UInt256.ofNat 0x268), by rfl, by decide⟩,
   ⟨412, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_268 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨448, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c1), by rfl, by decide⟩,
   ⟨450, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3c1 : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨647, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨648, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩,
   ⟨649, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def entryPath := Artifact.entrySelectedPath

private def entryContext (input : ByteArray) (pc : Nat) :
    Challenge.EvmProof.CertifiedArtifact.ExecutionContext
      Artifact.referenceCertifiedArtifact (atPC input pc) := {
  code_eq := rfl
  fork_eq := rfl
  running := rfl
  notPrecompile := deployAddress_not_precompile
}

private theorem run_start (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_start (atPC input 0) =
        some (atPC input 0x1b, 11) := by
  simpa only [Artifact.entryPath_start, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runPushJump input 0 0x1b (by norm_num) (by norm_num)
      Artifact.validJumpDest_1b Artifact.entryDecoder_0 Artifact.entryDecoder_1

private theorem run_1b (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_1b (atPC input 0x1b) =
        some (atPC input 0x2e, 12) := by
  simpa only [Artifact.entryPath_1b, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x1b 0x2e (by norm_num) (by norm_num)
      Artifact.validJumpDest_2e Artifact.entryDecoder_20 Artifact.entryDecoder_21 Artifact.entryDecoder_22

private theorem run_2e (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_2e (atPC input 0x2e) =
        some (atPC input 0x46, 12) := by
  simpa only [Artifact.entryPath_2e, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x2e 0x46 (by norm_num) (by norm_num)
      Artifact.validJumpDest_46 Artifact.entryDecoder_35 Artifact.entryDecoder_36 Artifact.entryDecoder_37

private theorem run_46 (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_46 (atPC input 0x46) =
        some (atPC input 0x5a, 12) := by
  simpa only [Artifact.entryPath_46, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x46 0x5a (by norm_num) (by norm_num)
      Artifact.validJumpDest_5a Artifact.entryDecoder_52 Artifact.entryDecoder_53 Artifact.entryDecoder_54

private theorem run_5a (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_5a (atPC input 0x5a) =
        some (atPC input 0x73, 12) := by
  simpa only [Artifact.entryPath_5a, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x5a 0x73 (by norm_num) (by norm_num)
      Artifact.validJumpDest_73 Artifact.entryDecoder_67 Artifact.entryDecoder_68 Artifact.entryDecoder_69

private theorem run_73 (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_73 (atPC input 0x73) =
        some (atPC input 0x8e, 12) := by
  simpa only [Artifact.entryPath_73, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x73 0x8e (by norm_num) (by norm_num)
      Artifact.validJumpDest_8e Artifact.entryDecoder_83 Artifact.entryDecoder_84 Artifact.entryDecoder_85

private theorem run_8e (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_8e (atPC input 0x8e) =
        some (atPC input 0x10f, 12) := by
  simpa only [Artifact.entryPath_8e, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x8e 0x10f (by norm_num) (by norm_num)
      Artifact.validJumpDest_10f Artifact.entryDecoder_105 Artifact.entryDecoder_106 Artifact.entryDecoder_107

private theorem run_10f (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_10f (atPC input 0x10f) =
        some (atPC input 0x1b2, 12) := by
  simpa only [Artifact.entryPath_10f, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x10f 0x1b2 (by norm_num) (by norm_num)
      Artifact.validJumpDest_1b2 Artifact.entryDecoder_205 Artifact.entryDecoder_206 Artifact.entryDecoder_207

private theorem run_1b2 (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_1b2 (atPC input 0x1b2) =
        some (atPC input 0x1db, 12) := by
  simpa only [Artifact.entryPath_1b2, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x1b2 0x1db (by norm_num) (by norm_num)
      Artifact.validJumpDest_1db Artifact.entryDecoder_313 Artifact.entryDecoder_314 Artifact.entryDecoder_315

private theorem run_1db (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_1db (atPC input 0x1db) =
        some (atPC input 0x231, 12) := by
  simpa only [Artifact.entryPath_1db, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x1db 0x231 (by norm_num) (by norm_num)
      Artifact.validJumpDest_231 Artifact.entryDecoder_346 Artifact.entryDecoder_347 Artifact.entryDecoder_348

private theorem run_231 (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_231 (atPC input 0x231) =
        some (atPC input 0x268, 12) := by
  simpa only [Artifact.entryPath_231, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x231 0x268 (by norm_num) (by norm_num)
      Artifact.validJumpDest_268 Artifact.entryDecoder_410 Artifact.entryDecoder_411 Artifact.entryDecoder_412

private theorem run_268 (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_268 (atPC input 0x268) =
        some (atPC input 0x3c1, 12) := by
  simpa only [Artifact.entryPath_268, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x268 0x3c1 (by norm_num) (by norm_num)
      Artifact.validJumpDest_3c1 Artifact.entryDecoder_448 Artifact.entryDecoder_449 Artifact.entryDecoder_450

private theorem run_3c1 (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_3c1 (atPC input 0x3c1) =
        some (atPC input 0x3ee, 12) := by
  simpa only [Artifact.entryPath_3c1, atPC, EntryTemplates.atPC, Nat.reduceAdd,
    Challenge.EvmProof.Word.literal_eq_ofNat] using
    EntryTemplates.runJumpBlock input 0x3c1 0x3ee (by norm_num) (by norm_num)
      Artifact.validJumpDest_3ee Artifact.entryDecoder_647 Artifact.entryDecoder_648 Artifact.entryDecoder_649

private theorem run_3ee (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected
      Artifact.entryPath_3ee (atPC input 0x3ee) =
        some (mainStart input, 1) := by
  simpa only [Artifact.entryPath_3ee, mainStart, atPC,
    EntryTemplates.mainStart, EntryTemplates.atPC, Nat.reduceAdd] using
    EntryTemplates.runJumpdest input 0x3ee (by norm_num)
      Artifact.entryDecoder_682

private def selectedTrace (path : List Artifact.EntrySite)
    {start finish : State} {cost : Nat}
    (result : Artifact.referenceCertifiedArtifact.runSelected path start =
      some (finish, cost))
    (context : Challenge.EvmProof.CertifiedArtifact.ExecutionContext
      Artifact.referenceCertifiedArtifact start) :
    Challenge.EvmProof.GasSteps start finish :=
  (Artifact.referenceCertifiedArtifact.runSelected_sound
    path result context).1

/-! Compatibility segment traces. Their implementations consume the compact
selected-site paths above; new proofs should normally use `gasSteps_entry` and
`gasSteps_entry_cost` at the whole-entry boundary. -/

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (atPC input 0x1b) :=
  Challenge.EvmProof.GasSteps.cast
    (selectedTrace Artifact.entryPath_start (run_start input)
      (entryContext input 0)) rfl rfl

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b) (atPC input 0x2e) :=
  selectedTrace Artifact.entryPath_1b (run_1b input)
    (entryContext input 0x1b)

def gasSteps_2e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x2e) (atPC input 0x46) :=
  selectedTrace Artifact.entryPath_2e (run_2e input)
    (entryContext input 0x2e)

def gasSteps_46 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x46) (atPC input 0x5a) :=
  selectedTrace Artifact.entryPath_46 (run_46 input)
    (entryContext input 0x46)

def gasSteps_5a (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5a) (atPC input 0x73) :=
  selectedTrace Artifact.entryPath_5a (run_5a input)
    (entryContext input 0x5a)

def gasSteps_73 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x73) (atPC input 0x8e) :=
  selectedTrace Artifact.entryPath_73 (run_73 input)
    (entryContext input 0x73)

def gasSteps_8e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x8e) (atPC input 0x10f) :=
  selectedTrace Artifact.entryPath_8e (run_8e input)
    (entryContext input 0x8e)

def gasSteps_10f (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x10f) (atPC input 0x1b2) :=
  selectedTrace Artifact.entryPath_10f (run_10f input)
    (entryContext input 0x10f)

def gasSteps_1b2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b2) (atPC input 0x1db) :=
  selectedTrace Artifact.entryPath_1b2 (run_1b2 input)
    (entryContext input 0x1b2)

def gasSteps_1db (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1db) (atPC input 0x231) :=
  selectedTrace Artifact.entryPath_1db (run_1db input)
    (entryContext input 0x1db)

def gasSteps_231 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x231) (atPC input 0x268) :=
  selectedTrace Artifact.entryPath_231 (run_231 input)
    (entryContext input 0x231)

def gasSteps_268 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x268) (atPC input 0x3c1) :=
  selectedTrace Artifact.entryPath_268 (run_268 input)
    (entryContext input 0x268)

def gasSteps_3c1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3c1) (atPC input 0x3ee) :=
  selectedTrace Artifact.entryPath_3c1 (run_3c1 input)
    (entryContext input 0x3c1)

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) :=
  selectedTrace Artifact.entryPath_3ee (run_3ee input)
    (entryContext input 0x3ee)

private theorem run_entry (input : ByteArray) :
    Artifact.referenceCertifiedArtifact.runSelected entryPath (atPC input 0) =
      some (mainStart input, 156) := by
  let artifact := Artifact.referenceCertifiedArtifact
  have tail_3c1 := artifact.runSelected_append
    Artifact.entryPath_3c1 Artifact.entryPath_3ee
    (run_3c1 input) rfl (run_3ee input)
  have tail_268 := artifact.runSelected_append
    Artifact.entryPath_268 (Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_268 input) rfl tail_3c1
  have tail_231 := artifact.runSelected_append
    Artifact.entryPath_231 (Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_231 input) rfl tail_268
  have tail_1db := artifact.runSelected_append
    Artifact.entryPath_1db (Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_1db input) rfl tail_231
  have tail_1b2 := artifact.runSelected_append
    Artifact.entryPath_1b2 (Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_1b2 input) rfl tail_1db
  have tail_10f := artifact.runSelected_append
    Artifact.entryPath_10f (Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_10f input) rfl tail_1b2
  have tail_8e := artifact.runSelected_append
    Artifact.entryPath_8e (Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_8e input) rfl tail_10f
  have tail_73 := artifact.runSelected_append
    Artifact.entryPath_73 (Artifact.entryPath_8e ++ Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_73 input) rfl tail_8e
  have tail_5a := artifact.runSelected_append
    Artifact.entryPath_5a (Artifact.entryPath_73 ++ Artifact.entryPath_8e ++ Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_5a input) rfl tail_73
  have tail_46 := artifact.runSelected_append
    Artifact.entryPath_46 (Artifact.entryPath_5a ++ Artifact.entryPath_73 ++ Artifact.entryPath_8e ++ Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_46 input) rfl tail_5a
  have tail_2e := artifact.runSelected_append
    Artifact.entryPath_2e (Artifact.entryPath_46 ++ Artifact.entryPath_5a ++ Artifact.entryPath_73 ++ Artifact.entryPath_8e ++ Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_2e input) rfl tail_46
  have tail_1b := artifact.runSelected_append
    Artifact.entryPath_1b (Artifact.entryPath_2e ++ Artifact.entryPath_46 ++ Artifact.entryPath_5a ++ Artifact.entryPath_73 ++ Artifact.entryPath_8e ++ Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_1b input) rfl tail_2e
  have tail_start := artifact.runSelected_append
    Artifact.entryPath_start (Artifact.entryPath_1b ++ Artifact.entryPath_2e ++ Artifact.entryPath_46 ++ Artifact.entryPath_5a ++ Artifact.entryPath_73 ++ Artifact.entryPath_8e ++ Artifact.entryPath_10f ++ Artifact.entryPath_1b2 ++ Artifact.entryPath_1db ++ Artifact.entryPath_231 ++ Artifact.entryPath_268 ++ Artifact.entryPath_3c1 ++ Artifact.entryPath_3ee)
    (run_start input) rfl tail_1b
  simpa only [artifact, entryPath, Artifact.entrySelectedPath,
    List.append_assoc] using tail_start

private theorem entrySound (input : ByteArray) :
    ∃ trace : Challenge.EvmProof.GasSteps (atPC input 0) (mainStart input),
      trace.cost = 156 := by
  exact Challenge.EvmProof.CertifiedArtifact.runSelected_sound_exists
    (start := atPC input 0) (finish := mainStart input) (cost := 156)
    Artifact.referenceCertifiedArtifact entryPath (run_entry input)
      (entryContext input 0)

/-- Certified entry trace. Its exact cost is intentionally exposed through
`gasSteps_entry_cost` instead of reduction through the selected-site proof. -/
noncomputable def gasSteps_entry (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (mainStart input) :=
  Challenge.EvmProof.GasSteps.cast
    (Classical.choose (entrySound input)) rfl rfl

theorem gasSteps_entry_cost (input : ByteArray) :
    (gasSteps_entry input).cost = 156 := by
  simpa only [gasSteps_entry, Challenge.EvmProof.GasSteps.cast_cost] using
    Classical.choose_spec (entrySound input)

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Execution
