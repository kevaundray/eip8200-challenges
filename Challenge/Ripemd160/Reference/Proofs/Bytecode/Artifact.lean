import Challenge.EvmProof.CertifiedArtifact.FromBytecode
import Challenge.Ripemd160.Reference.Bytecode
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ArtifactSnapshots
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Structural certificate for the frozen RIPEMD-160 artifact

The instruction-boundary list below is generated from the reusable raw-bytecode
disassembler. Its assembly theorem ties every location used by the direct proof
to the exact frozen bytes.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

def referenceRows : Array Challenge.EvmProof.CertifiedArtifact.Entry :=
  Challenge.EvmProof.CertifiedArtifact.rowsOfBytecode referenceBytecode

def referenceInstructions : List Instr :=
  Challenge.EvmProof.CertifiedArtifact.instructions referenceRows

theorem referenceInstructions_count : referenceInstructions.length = 831 := by
  decide

private theorem referenceBytecodeCertificate :
    Challenge.EvmProof.CertifiedArtifact.BytecodeCertificate
      .Osaka referenceBytecode := by
  decide

theorem referenceRows_valid :
    Challenge.EvmProof.CertifiedArtifact.Table.Valid
      .Osaka referenceBytecode referenceRows := by
  exact Challenge.EvmProof.CertifiedArtifact.rowsOfBytecode_valid
    referenceBytecodeCertificate

theorem assemble_referenceInstructions :
    assemble referenceInstructions = referenceBytecode :=
  referenceRows_valid.assembly_eq

def referenceCertifiedArtifact :
    Challenge.EvmProof.CertifiedArtifact .Osaka referenceBytecode :=
  Challenge.EvmProof.CertifiedArtifact.fromBytecode referenceBytecodeCertificate

private def rowIndex (index : Fin 831) : Fin referenceRows.size :=
  ⟨index, by
    change index.val < 831
    exact index.isLt⟩

private abbrev SnapshotEntry :=
  Challenge.EvmProof.CertifiedArtifact.Entry

private def snapshotRows : List SnapshotEntry :=
  ArtifactSnapshots.indices.map (fun index => referenceRows[rowIndex index])

/-- One batch equality validates every cached entry used by compatibility
proofs, so later declarations never normalize the full disassembly again. -/
private theorem snapshotRows_eq : snapshotRows = ArtifactSnapshots.entries := by
  rfl

private def snapshotIndex (position : Fin 185) : Fin 831 :=
  ArtifactSnapshots.indices[position.val]'(by simp)

private def snapshotEntry (position : Fin 185) : SnapshotEntry :=
  ArtifactSnapshots.entries[position.val]'(by simp)

private theorem snapshotRow_eq (position : Fin 185) :
    referenceRows[rowIndex (snapshotIndex position)] = snapshotEntry position := by
  have equality := congrArg (fun rows : List SnapshotEntry => rows[position.val]?)
    snapshotRows_eq
  have indexGet : ArtifactSnapshots.indices[position.val]? =
      some (snapshotIndex position) := by simp [snapshotIndex]
  have entryGet : ArtifactSnapshots.entries[position.val]? =
      some (snapshotEntry position) := by simp [snapshotEntry]
  simp only [snapshotRows, List.getElem?_map, indexGet, Option.map_some,
    entryGet] at equality
  exact Option.some.inj equality

private def decoderPositions : List (Fin 185) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
   18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 90, 91, 92, 93, 94, 95,
   96, 97, 98, 99]

private def decoderPosition (position : Fin 39) : Fin 185 :=
  decoderPositions[position.val]'(by simp [decoderPositions])

private def selectedSnapshot (position : Fin 39) : SnapshotEntry :=
  snapshotEntry (decoderPosition position)

private theorem selectedRow_eq (position : Fin 39) :
    referenceRows[rowIndex (snapshotIndex (decoderPosition position))] =
      selectedSnapshot position :=
  snapshotRow_eq (decoderPosition position)

private def selectedDecoder (position : Fin 39) :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode (selectedSnapshot position) :=
  referenceCertifiedArtifact.decoderCertificate
    (rowIndex (snapshotIndex (decoderPosition position)))
    (selectedSnapshot position)
    (selectedRow_eq position)

theorem entryDecoder_0 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨0, .push 2 27⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 0

theorem entryDecoder_1 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨3, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 1

theorem entryDecoder_20 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨27, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 2

theorem entryDecoder_21 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨28, .push 2 46⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 3

theorem entryDecoder_22 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨31, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 4

theorem entryDecoder_35 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨46, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 5

theorem entryDecoder_36 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨47, .push 2 70⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 6

theorem entryDecoder_37 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨50, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 7

theorem entryDecoder_52 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨70, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 8

theorem entryDecoder_53 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨71, .push 2 90⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 9

theorem entryDecoder_54 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨74, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 10

theorem entryDecoder_67 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨90, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 11

theorem entryDecoder_68 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨91, .push 2 115⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 12

theorem entryDecoder_69 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨94, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 13

theorem entryDecoder_83 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨115, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 14

theorem entryDecoder_84 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨116, .push 2 142⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 15

theorem entryDecoder_85 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨119, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 16

theorem entryDecoder_105 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨142, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 17

theorem entryDecoder_106 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨143, .push 2 271⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 18

theorem entryDecoder_107 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨146, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 19

theorem entryDecoder_205 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨271, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 20

theorem entryDecoder_206 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨272, .push 2 434⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 21

theorem entryDecoder_207 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨275, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 22

theorem entryDecoder_313 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨434, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 23

theorem entryDecoder_314 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨435, .push 2 475⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 24

theorem entryDecoder_315 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨438, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 25

theorem entryDecoder_346 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨475, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 26

theorem entryDecoder_347 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨476, .push 2 561⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 27

theorem entryDecoder_348 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨479, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 28

theorem entryDecoder_410 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨561, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 29

theorem entryDecoder_411 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨562, .push 2 616⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 30

theorem entryDecoder_412 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨565, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 31

theorem entryDecoder_448 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨616, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 32

theorem entryDecoder_449 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨617, .push 2 961⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 33

theorem entryDecoder_450 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨620, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 34

theorem entryDecoder_647 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨961, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 35

theorem entryDecoder_648 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨962, .push 2 1006⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 36

theorem entryDecoder_649 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨965, .op .JUMP⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 37

theorem entryDecoder_682 :
    Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
      .Osaka referenceBytecode ⟨1006, .op .JUMPDEST⟩ :=
  by simpa [selectedSnapshot, snapshotEntry, decoderPosition,
    decoderPositions, ArtifactSnapshots.entries] using
      selectedDecoder 38

abbrev EntrySite := Challenge.EvmProof.CertifiedArtifact.SelectedEntry
  .Osaka referenceBytecode

def entryPath_start : List EntrySite :=
  [
   ⟨⟨0, .push 2 27⟩, entryDecoder_0⟩,
   ⟨⟨3, .op .JUMP⟩, entryDecoder_1⟩
  ]

def entryPath_1b : List EntrySite :=
  [
   ⟨⟨27, .op .JUMPDEST⟩, entryDecoder_20⟩,
   ⟨⟨28, .push 2 46⟩, entryDecoder_21⟩,
   ⟨⟨31, .op .JUMP⟩, entryDecoder_22⟩
  ]

def entryPath_2e : List EntrySite :=
  [
   ⟨⟨46, .op .JUMPDEST⟩, entryDecoder_35⟩,
   ⟨⟨47, .push 2 70⟩, entryDecoder_36⟩,
   ⟨⟨50, .op .JUMP⟩, entryDecoder_37⟩
  ]

def entryPath_46 : List EntrySite :=
  [
   ⟨⟨70, .op .JUMPDEST⟩, entryDecoder_52⟩,
   ⟨⟨71, .push 2 90⟩, entryDecoder_53⟩,
   ⟨⟨74, .op .JUMP⟩, entryDecoder_54⟩
  ]

def entryPath_5a : List EntrySite :=
  [
   ⟨⟨90, .op .JUMPDEST⟩, entryDecoder_67⟩,
   ⟨⟨91, .push 2 115⟩, entryDecoder_68⟩,
   ⟨⟨94, .op .JUMP⟩, entryDecoder_69⟩
  ]

def entryPath_73 : List EntrySite :=
  [
   ⟨⟨115, .op .JUMPDEST⟩, entryDecoder_83⟩,
   ⟨⟨116, .push 2 142⟩, entryDecoder_84⟩,
   ⟨⟨119, .op .JUMP⟩, entryDecoder_85⟩
  ]

def entryPath_8e : List EntrySite :=
  [
   ⟨⟨142, .op .JUMPDEST⟩, entryDecoder_105⟩,
   ⟨⟨143, .push 2 271⟩, entryDecoder_106⟩,
   ⟨⟨146, .op .JUMP⟩, entryDecoder_107⟩
  ]

def entryPath_10f : List EntrySite :=
  [
   ⟨⟨271, .op .JUMPDEST⟩, entryDecoder_205⟩,
   ⟨⟨272, .push 2 434⟩, entryDecoder_206⟩,
   ⟨⟨275, .op .JUMP⟩, entryDecoder_207⟩
  ]

def entryPath_1b2 : List EntrySite :=
  [
   ⟨⟨434, .op .JUMPDEST⟩, entryDecoder_313⟩,
   ⟨⟨435, .push 2 475⟩, entryDecoder_314⟩,
   ⟨⟨438, .op .JUMP⟩, entryDecoder_315⟩
  ]

def entryPath_1db : List EntrySite :=
  [
   ⟨⟨475, .op .JUMPDEST⟩, entryDecoder_346⟩,
   ⟨⟨476, .push 2 561⟩, entryDecoder_347⟩,
   ⟨⟨479, .op .JUMP⟩, entryDecoder_348⟩
  ]

def entryPath_231 : List EntrySite :=
  [
   ⟨⟨561, .op .JUMPDEST⟩, entryDecoder_410⟩,
   ⟨⟨562, .push 2 616⟩, entryDecoder_411⟩,
   ⟨⟨565, .op .JUMP⟩, entryDecoder_412⟩
  ]

def entryPath_268 : List EntrySite :=
  [
   ⟨⟨616, .op .JUMPDEST⟩, entryDecoder_448⟩,
   ⟨⟨617, .push 2 961⟩, entryDecoder_449⟩,
   ⟨⟨620, .op .JUMP⟩, entryDecoder_450⟩
  ]

def entryPath_3c1 : List EntrySite :=
  [
   ⟨⟨961, .op .JUMPDEST⟩, entryDecoder_647⟩,
   ⟨⟨962, .push 2 1006⟩, entryDecoder_648⟩,
   ⟨⟨965, .op .JUMP⟩, entryDecoder_649⟩
  ]

def entryPath_3ee : List EntrySite :=
  [
   ⟨⟨1006, .op .JUMPDEST⟩, entryDecoder_682⟩
  ]

/-- The compact certified sites traversed between deployment entry and the
main RIPEMD body. Each bounded segment can be checked independently, while
the combined path remains definitionally their append chain. -/
def entrySelectedPath : List EntrySite :=
  entryPath_start ++ entryPath_1b ++ entryPath_2e ++ entryPath_46 ++
  entryPath_5a ++ entryPath_73 ++ entryPath_8e ++ entryPath_10f ++
  entryPath_1b2 ++ entryPath_1db ++ entryPath_231 ++ entryPath_268 ++
  entryPath_3c1 ++ entryPath_3ee


def referenceArtifact : Challenge.EvmProof.ProgramArtifact where
  code := referenceBytecode
  instructions := referenceInstructions
  assembly_eq := assemble_referenceInstructions

theorem certifiedArtifact_instructions :
    Challenge.EvmProof.CertifiedArtifact.instructions
        referenceCertifiedArtifact.rows = referenceInstructions := by
  rfl

def instructionPC (index : Nat) : Nat :=
  referenceArtifact.instructionPC index

private theorem referenceArtifact_pc_snapshot (position : Fin 185) :
    referenceArtifact.instructionPC (snapshotIndex position).val =
      (snapshotEntry position).pc := by
  calc
    referenceArtifact.instructionPC (snapshotIndex position).val =
        Challenge.EvmProof.CertifiedArtifact.instructionPC referenceRows
          (snapshotIndex position).val := by
      rfl
    _ = referenceRows[rowIndex (snapshotIndex position)].pc :=
      (referenceRows_valid.pc_eq (rowIndex (snapshotIndex position))).symm
    _ = (snapshotEntry position).pc :=
      congrArg Challenge.EvmProof.CertifiedArtifact.Entry.pc
        (snapshotRow_eq position)

private theorem referenceInstructions_snapshot (position : Fin 185) :
    referenceInstructions[(snapshotIndex position).val]? =
      some (snapshotEntry position).instruction := by
  have rowEq := snapshotRow_eq position
  unfold referenceInstructions Challenge.EvmProof.CertifiedArtifact.instructions
  rw [List.getElem?_map]
  simp only [Array.getElem?_toList]
  have inBounds : (snapshotIndex position).val < referenceRows.size :=
    (rowIndex (snapshotIndex position)).isLt
  rw [Array.getElem?_eq_getElem inBounds]
  rw [Option.map_some]
  exact congrArg (fun row : Challenge.EvmProof.CertifiedArtifact.Entry =>
    some row.instruction) rowEq

private theorem referenceArtifact_instruction_snapshot (position : Fin 185) :
    referenceArtifact.instructions[(snapshotIndex position).val]? =
      some (snapshotEntry position).instruction := by
  exact referenceInstructions_snapshot position

/-- One of the straight-line stores which initializes RIPEMD's lookup tables,
round constants, and five-word initial chaining value. -/
structure InitStore where
  index : Nat
  valueWidth : Fin 33
  value : UInt256
  offsetWidth : Fin 33
  offset : UInt256

def initStores : List InitStore :=
  [⟨683, 31, 1780731860627700044960722568376592188711674974810043212252563479055960840, 2, 1184⟩,
   ⟨686, 32, 1374703749640218873849524064026661036561295975619335768036000015621818746370, 2, 1216⟩,
   ⟨689, 32, 1809286146446445343010337679715913357291520642540487409382712519614204477440, 2, 1248⟩,
   ⟨692, 32, 2286348414996307935469207465186628553155355030353023797310855598864584999170, 2, 1280⟩,
   ⟨695, 32, 6793533947442029545286681365244130742947859423983440781638017424580845963790, 2, 1312⟩,
   ⟨698, 32, 5454326014381509071620663843103927214778145566039445656282506490595801825280, 2, 1344⟩,
   ⟨701, 32, 5000281043567253289773844389228683908720941172611121566642559091978571025676, 2, 1376⟩,
   ⟨704, 32, 4998451946933852135137276647445154408072640462072745561656555001729660617996, 2, 1408⟩,
   ⟨707, 32, 4097353149147406276549177442451244923784709130172834976461593227075946283008, 2, 1440⟩,
   ⟨710, 32, 3634466825900925589093651101374881051901026410458987220032629834781140389131, 2, 1472⟩,
   ⟨713, 32, 4083287390302437702768465126624575726298108573653391417181074648310269415176, 2, 1504⟩,
   ⟨716, 32, 3627420088851531435467691758328083203359072412578514691593700216701345333248, 2, 1536⟩,
   ⟨719, 0, 0, 2, 1568⟩,
   ⟨722, 4, 1518500249, 2, 1600⟩,
   ⟨725, 4, 1859775393, 2, 1632⟩,
   ⟨728, 4, 2400959708, 2, 1664⟩,
   ⟨731, 4, 2840853838, 2, 1696⟩,
   ⟨734, 4, 1352829926, 2, 1728⟩,
   ⟨737, 4, 1548603684, 2, 1760⟩,
   ⟨740, 4, 1836072691, 2, 1792⟩,
   ⟨743, 4, 2053994217, 2, 1824⟩,
   ⟨746, 0, 0, 2, 1856⟩,
   ⟨749, 4, 1732584193, 1, 32⟩,
   ⟨752, 4, 4023233417, 1, 64⟩,
   ⟨755, 4, 2562383102, 1, 96⟩,
   ⟨758, 4, 271733878, 1, 128⟩,
   ⟨761, 4, 3285377520, 1, 160⟩]

@[simp] theorem referenceArtifact_pc_683 :
    referenceArtifact.instructionPC 683 = 0x3ef := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 100

@[simp] theorem referenceArtifact_pc_684 :
    referenceArtifact.instructionPC 684 = 0x40f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 101

@[simp] theorem referenceArtifact_pc_685 :
    referenceArtifact.instructionPC 685 = 0x412 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 102

@[simp] theorem referenceArtifact_pc_686 :
    referenceArtifact.instructionPC 686 = 0x413 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 103

@[simp] theorem referenceArtifact_pc_687 :
    referenceArtifact.instructionPC 687 = 0x434 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 104

@[simp] theorem referenceArtifact_pc_688 :
    referenceArtifact.instructionPC 688 = 0x437 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 105

@[simp] theorem referenceArtifact_pc_689 :
    referenceArtifact.instructionPC 689 = 0x438 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 106

@[simp] theorem referenceArtifact_pc_690 :
    referenceArtifact.instructionPC 690 = 0x459 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 107

@[simp] theorem referenceArtifact_pc_691 :
    referenceArtifact.instructionPC 691 = 0x45c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 108

@[simp] theorem referenceArtifact_pc_692 :
    referenceArtifact.instructionPC 692 = 0x45d := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 109

@[simp] theorem referenceArtifact_pc_693 :
    referenceArtifact.instructionPC 693 = 0x47e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 110

@[simp] theorem referenceArtifact_pc_694 :
    referenceArtifact.instructionPC 694 = 0x481 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 111

@[simp] theorem referenceArtifact_pc_695 :
    referenceArtifact.instructionPC 695 = 0x482 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 112

@[simp] theorem referenceArtifact_pc_696 :
    referenceArtifact.instructionPC 696 = 0x4a3 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 113

@[simp] theorem referenceArtifact_pc_697 :
    referenceArtifact.instructionPC 697 = 0x4a6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 114

@[simp] theorem referenceArtifact_pc_698 :
    referenceArtifact.instructionPC 698 = 0x4a7 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 115

@[simp] theorem referenceArtifact_pc_699 :
    referenceArtifact.instructionPC 699 = 0x4c8 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 116

@[simp] theorem referenceArtifact_pc_700 :
    referenceArtifact.instructionPC 700 = 0x4cb := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 117

@[simp] theorem referenceArtifact_pc_701 :
    referenceArtifact.instructionPC 701 = 0x4cc := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 118

@[simp] theorem referenceArtifact_pc_702 :
    referenceArtifact.instructionPC 702 = 0x4ed := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 119

@[simp] theorem referenceArtifact_pc_703 :
    referenceArtifact.instructionPC 703 = 0x4f0 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 120

@[simp] theorem referenceArtifact_pc_704 :
    referenceArtifact.instructionPC 704 = 0x4f1 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 121

@[simp] theorem referenceArtifact_pc_705 :
    referenceArtifact.instructionPC 705 = 0x512 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 122

@[simp] theorem referenceArtifact_pc_706 :
    referenceArtifact.instructionPC 706 = 0x515 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 123

@[simp] theorem referenceArtifact_pc_707 :
    referenceArtifact.instructionPC 707 = 0x516 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 124

@[simp] theorem referenceArtifact_pc_708 :
    referenceArtifact.instructionPC 708 = 0x537 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 125

@[simp] theorem referenceArtifact_pc_709 :
    referenceArtifact.instructionPC 709 = 0x53a := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 126

@[simp] theorem referenceArtifact_pc_710 :
    referenceArtifact.instructionPC 710 = 0x53b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 127

@[simp] theorem referenceArtifact_pc_711 :
    referenceArtifact.instructionPC 711 = 0x55c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 128

@[simp] theorem referenceArtifact_pc_712 :
    referenceArtifact.instructionPC 712 = 0x55f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 129

@[simp] theorem referenceArtifact_pc_713 :
    referenceArtifact.instructionPC 713 = 0x560 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 130

@[simp] theorem referenceArtifact_pc_714 :
    referenceArtifact.instructionPC 714 = 0x581 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 131

@[simp] theorem referenceArtifact_pc_715 :
    referenceArtifact.instructionPC 715 = 0x584 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 132

@[simp] theorem referenceArtifact_pc_716 :
    referenceArtifact.instructionPC 716 = 0x585 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 133

@[simp] theorem referenceArtifact_pc_717 :
    referenceArtifact.instructionPC 717 = 0x5a6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 134

@[simp] theorem referenceArtifact_pc_718 :
    referenceArtifact.instructionPC 718 = 0x5a9 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 135

@[simp] theorem referenceArtifact_pc_719 :
    referenceArtifact.instructionPC 719 = 0x5aa := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 136

@[simp] theorem referenceArtifact_pc_720 :
    referenceArtifact.instructionPC 720 = 0x5ab := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 137

@[simp] theorem referenceArtifact_pc_721 :
    referenceArtifact.instructionPC 721 = 0x5ae := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 138

@[simp] theorem referenceArtifact_pc_722 :
    referenceArtifact.instructionPC 722 = 0x5af := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 139

@[simp] theorem referenceArtifact_pc_723 :
    referenceArtifact.instructionPC 723 = 0x5b4 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 140

@[simp] theorem referenceArtifact_pc_724 :
    referenceArtifact.instructionPC 724 = 0x5b7 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 141

@[simp] theorem referenceArtifact_pc_725 :
    referenceArtifact.instructionPC 725 = 0x5b8 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 142

@[simp] theorem referenceArtifact_pc_726 :
    referenceArtifact.instructionPC 726 = 0x5bd := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 143

@[simp] theorem referenceArtifact_pc_727 :
    referenceArtifact.instructionPC 727 = 0x5c0 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 144

@[simp] theorem referenceArtifact_pc_728 :
    referenceArtifact.instructionPC 728 = 0x5c1 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 145

@[simp] theorem referenceArtifact_pc_729 :
    referenceArtifact.instructionPC 729 = 0x5c6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 146

@[simp] theorem referenceArtifact_pc_730 :
    referenceArtifact.instructionPC 730 = 0x5c9 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 147

@[simp] theorem referenceArtifact_pc_731 :
    referenceArtifact.instructionPC 731 = 0x5ca := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 148

@[simp] theorem referenceArtifact_pc_732 :
    referenceArtifact.instructionPC 732 = 0x5cf := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 149

@[simp] theorem referenceArtifact_pc_733 :
    referenceArtifact.instructionPC 733 = 0x5d2 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 150

@[simp] theorem referenceArtifact_pc_734 :
    referenceArtifact.instructionPC 734 = 0x5d3 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 151

@[simp] theorem referenceArtifact_pc_735 :
    referenceArtifact.instructionPC 735 = 0x5d8 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 152

@[simp] theorem referenceArtifact_pc_736 :
    referenceArtifact.instructionPC 736 = 0x5db := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 153

@[simp] theorem referenceArtifact_pc_737 :
    referenceArtifact.instructionPC 737 = 0x5dc := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 154

@[simp] theorem referenceArtifact_pc_738 :
    referenceArtifact.instructionPC 738 = 0x5e1 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 155

@[simp] theorem referenceArtifact_pc_739 :
    referenceArtifact.instructionPC 739 = 0x5e4 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 156

@[simp] theorem referenceArtifact_pc_740 :
    referenceArtifact.instructionPC 740 = 0x5e5 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 157

@[simp] theorem referenceArtifact_pc_741 :
    referenceArtifact.instructionPC 741 = 0x5ea := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 158

@[simp] theorem referenceArtifact_pc_742 :
    referenceArtifact.instructionPC 742 = 0x5ed := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 159

@[simp] theorem referenceArtifact_pc_743 :
    referenceArtifact.instructionPC 743 = 0x5ee := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 160

@[simp] theorem referenceArtifact_pc_744 :
    referenceArtifact.instructionPC 744 = 0x5f3 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 161

@[simp] theorem referenceArtifact_pc_745 :
    referenceArtifact.instructionPC 745 = 0x5f6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 162

@[simp] theorem referenceArtifact_pc_746 :
    referenceArtifact.instructionPC 746 = 0x5f7 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 163

@[simp] theorem referenceArtifact_pc_747 :
    referenceArtifact.instructionPC 747 = 0x5f8 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 164

@[simp] theorem referenceArtifact_pc_748 :
    referenceArtifact.instructionPC 748 = 0x5fb := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 165

@[simp] theorem referenceArtifact_pc_749 :
    referenceArtifact.instructionPC 749 = 0x5fc := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 166

@[simp] theorem referenceArtifact_pc_750 :
    referenceArtifact.instructionPC 750 = 0x601 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 167

@[simp] theorem referenceArtifact_pc_751 :
    referenceArtifact.instructionPC 751 = 0x603 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 168

@[simp] theorem referenceArtifact_pc_752 :
    referenceArtifact.instructionPC 752 = 0x604 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 169

@[simp] theorem referenceArtifact_pc_753 :
    referenceArtifact.instructionPC 753 = 0x609 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 170

@[simp] theorem referenceArtifact_pc_754 :
    referenceArtifact.instructionPC 754 = 0x60b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 171

@[simp] theorem referenceArtifact_pc_755 :
    referenceArtifact.instructionPC 755 = 0x60c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 172

@[simp] theorem referenceArtifact_pc_756 :
    referenceArtifact.instructionPC 756 = 0x611 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 173

@[simp] theorem referenceArtifact_pc_757 :
    referenceArtifact.instructionPC 757 = 0x613 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 174

@[simp] theorem referenceArtifact_pc_758 :
    referenceArtifact.instructionPC 758 = 0x614 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 175

@[simp] theorem referenceArtifact_pc_759 :
    referenceArtifact.instructionPC 759 = 0x619 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 176

@[simp] theorem referenceArtifact_pc_760 :
    referenceArtifact.instructionPC 760 = 0x61b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 177

@[simp] theorem referenceArtifact_pc_761 :
    referenceArtifact.instructionPC 761 = 0x61c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 178

@[simp] theorem referenceArtifact_pc_762 :
    referenceArtifact.instructionPC 762 = 0x621 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 179

@[simp] theorem referenceArtifact_pc_763 :
    referenceArtifact.instructionPC 763 = 0x623 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 180


@[simp] theorem referenceArtifact_pc_764 :
    referenceArtifact.instructionPC 764 = 0x624 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 181

@[simp] theorem referenceArtifact_pc_765 :
    referenceArtifact.instructionPC 765 = 0x627 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 182

@[simp] theorem referenceArtifact_pc_766 :
    referenceArtifact.instructionPC 766 = 0x628 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 183

@[simp] theorem referenceArtifact_pc_767 :
    referenceArtifact.instructionPC 767 = 0x62b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 184

@[simp] theorem referenceArtifact_pc_0 :
    referenceArtifact.instructionPC 0 = 0x0 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 0

@[simp] theorem referenceArtifact_pc_1 :
    referenceArtifact.instructionPC 1 = 0x3 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 1

@[simp] theorem referenceArtifact_pc_20 :
    referenceArtifact.instructionPC 20 = 0x1b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 2

@[simp] theorem referenceArtifact_pc_21 :
    referenceArtifact.instructionPC 21 = 0x1c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 3

@[simp] theorem referenceArtifact_pc_22 :
    referenceArtifact.instructionPC 22 = 0x1f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 4

@[simp] theorem referenceArtifact_pc_35 :
    referenceArtifact.instructionPC 35 = 0x2e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 5

@[simp] theorem referenceArtifact_pc_36 :
    referenceArtifact.instructionPC 36 = 0x2f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 6

@[simp] theorem referenceArtifact_pc_37 :
    referenceArtifact.instructionPC 37 = 0x32 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 7

@[simp] theorem referenceArtifact_pc_52 :
    referenceArtifact.instructionPC 52 = 0x46 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 8

@[simp] theorem referenceArtifact_pc_53 :
    referenceArtifact.instructionPC 53 = 0x47 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 9

@[simp] theorem referenceArtifact_pc_54 :
    referenceArtifact.instructionPC 54 = 0x4a := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 10

@[simp] theorem referenceArtifact_pc_67 :
    referenceArtifact.instructionPC 67 = 0x5a := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 11

@[simp] theorem referenceArtifact_pc_68 :
    referenceArtifact.instructionPC 68 = 0x5b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 12

@[simp] theorem referenceArtifact_pc_69 :
    referenceArtifact.instructionPC 69 = 0x5e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 13

@[simp] theorem referenceArtifact_pc_83 :
    referenceArtifact.instructionPC 83 = 0x73 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 14

@[simp] theorem referenceArtifact_pc_84 :
    referenceArtifact.instructionPC 84 = 0x74 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 15

@[simp] theorem referenceArtifact_pc_85 :
    referenceArtifact.instructionPC 85 = 0x77 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 16

@[simp] theorem referenceArtifact_pc_105 :
    referenceArtifact.instructionPC 105 = 0x8e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 17

@[simp] theorem referenceArtifact_pc_106 :
    referenceArtifact.instructionPC 106 = 0x8f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 18

@[simp] theorem referenceArtifact_pc_107 :
    referenceArtifact.instructionPC 107 = 0x92 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 19

@[simp] theorem referenceArtifact_pc_205 :
    referenceArtifact.instructionPC 205 = 0x10f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 20

@[simp] theorem referenceArtifact_pc_206 :
    referenceArtifact.instructionPC 206 = 0x110 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 21

@[simp] theorem referenceArtifact_pc_207 :
    referenceArtifact.instructionPC 207 = 0x113 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 22

@[simp] theorem referenceArtifact_pc_313 :
    referenceArtifact.instructionPC 313 = 0x1b2 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 23

@[simp] theorem referenceArtifact_pc_314 :
    referenceArtifact.instructionPC 314 = 0x1b3 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 24

@[simp] theorem referenceArtifact_pc_315 :
    referenceArtifact.instructionPC 315 = 0x1b6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 25

@[simp] theorem referenceArtifact_pc_346 :
    referenceArtifact.instructionPC 346 = 0x1db := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 26

@[simp] theorem referenceArtifact_pc_347 :
    referenceArtifact.instructionPC 347 = 0x1dc := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 27

@[simp] theorem referenceArtifact_pc_348 :
    referenceArtifact.instructionPC 348 = 0x1df := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 28

@[simp] theorem referenceArtifact_pc_410 :
    referenceArtifact.instructionPC 410 = 0x231 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 90

@[simp] theorem referenceArtifact_pc_411 :
    referenceArtifact.instructionPC 411 = 0x232 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 91

@[simp] theorem referenceArtifact_pc_412 :
    referenceArtifact.instructionPC 412 = 0x235 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 92

@[simp] theorem referenceArtifact_pc_448 :
    referenceArtifact.instructionPC 448 = 0x268 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 93

@[simp] theorem referenceArtifact_pc_449 :
    referenceArtifact.instructionPC 449 = 0x269 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 94

@[simp] theorem referenceArtifact_pc_450 :
    referenceArtifact.instructionPC 450 = 0x26c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 95

@[simp] theorem referenceArtifact_pc_647 :
    referenceArtifact.instructionPC 647 = 0x3c1 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 96

@[simp] theorem referenceArtifact_pc_648 :
    referenceArtifact.instructionPC 648 = 0x3c2 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 97

@[simp] theorem referenceArtifact_pc_649 :
    referenceArtifact.instructionPC 649 = 0x3c5 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 98

@[simp] theorem referenceArtifact_pc_682 :
    referenceArtifact.instructionPC 682 = 0x3ee := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 99

@[simp] theorem validJumpDest_1b :
    Decode.isValidJumpDest referenceBytecode 0x1b = true := by
  have destination : referenceArtifact.instructions[20]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 2
  have h := referenceArtifact.isValidJumpDest_index 20 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 20) = true at h
  simpa using h

@[simp] theorem validJumpDest_2e :
    Decode.isValidJumpDest referenceBytecode 0x2e = true := by
  have destination : referenceArtifact.instructions[35]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 5
  have h := referenceArtifact.isValidJumpDest_index 35 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 35) = true at h
  simpa using h

@[simp] theorem validJumpDest_46 :
    Decode.isValidJumpDest referenceBytecode 0x46 = true := by
  have destination : referenceArtifact.instructions[52]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 8
  have h := referenceArtifact.isValidJumpDest_index 52 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 52) = true at h
  simpa using h

@[simp] theorem validJumpDest_5a :
    Decode.isValidJumpDest referenceBytecode 0x5a = true := by
  have destination : referenceArtifact.instructions[67]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 11
  have h := referenceArtifact.isValidJumpDest_index 67 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 67) = true at h
  simpa using h

@[simp] theorem validJumpDest_73 :
    Decode.isValidJumpDest referenceBytecode 0x73 = true := by
  have destination : referenceArtifact.instructions[83]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 14
  have h := referenceArtifact.isValidJumpDest_index 83 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 83) = true at h
  simpa using h

@[simp] theorem validJumpDest_8e :
    Decode.isValidJumpDest referenceBytecode 0x8e = true := by
  have destination : referenceArtifact.instructions[105]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 17
  have h := referenceArtifact.isValidJumpDest_index 105 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 105) = true at h
  simpa using h

@[simp] theorem validJumpDest_10f :
    Decode.isValidJumpDest referenceBytecode 0x10f = true := by
  have destination : referenceArtifact.instructions[205]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 20
  have h := referenceArtifact.isValidJumpDest_index 205 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 205) = true at h
  simpa using h

@[simp] theorem validJumpDest_1b2 :
    Decode.isValidJumpDest referenceBytecode 0x1b2 = true := by
  have destination : referenceArtifact.instructions[313]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 23
  have h := referenceArtifact.isValidJumpDest_index 313 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 313) = true at h
  simpa using h

@[simp] theorem validJumpDest_1db :
    Decode.isValidJumpDest referenceBytecode 0x1db = true := by
  have destination : referenceArtifact.instructions[346]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 26
  have h := referenceArtifact.isValidJumpDest_index 346 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 346) = true at h
  simpa using h

@[simp] theorem validJumpDest_231 :
    Decode.isValidJumpDest referenceBytecode 0x231 = true := by
  have destination : referenceArtifact.instructions[410]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 90
  have h := referenceArtifact.isValidJumpDest_index 410 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 410) = true at h
  simpa using h

@[simp] theorem validJumpDest_268 :
    Decode.isValidJumpDest referenceBytecode 0x268 = true := by
  have destination : referenceArtifact.instructions[448]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 93
  have h := referenceArtifact.isValidJumpDest_index 448 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 448) = true at h
  simpa using h

@[simp] theorem validJumpDest_3c1 :
    Decode.isValidJumpDest referenceBytecode 0x3c1 = true := by
  have destination : referenceArtifact.instructions[647]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 96
  have h := referenceArtifact.isValidJumpDest_index 647 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 647) = true at h
  simpa using h

@[simp] theorem validJumpDest_3ee :
    Decode.isValidJumpDest referenceBytecode 0x3ee = true := by
  have destination : referenceArtifact.instructions[682]? =
      some (.op .JUMPDEST) := by
    simpa [referenceArtifact, snapshotIndex, snapshotEntry,
      ArtifactSnapshots.indices, ArtifactSnapshots.entries] using
        referenceInstructions_snapshot 99
  have h := referenceArtifact.isValidJumpDest_index 682 destination
  change Decode.isValidJumpDest referenceBytecode
    (referenceArtifact.instructionPC 682) = true at h
  simpa using h

@[simp] theorem refPc349 :
    referenceArtifact.instructionPC 349 = 0x1e0 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 29
@[simp] theorem pc349 :
    instructionPC 349 = 0x1e0 := by
  exact refPc349

@[simp] theorem refPc350 :
    referenceArtifact.instructionPC 350 = 0x1e1 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 30
@[simp] theorem pc350 :
    instructionPC 350 = 0x1e1 := by
  exact refPc350

@[simp] theorem refPc351 :
    referenceArtifact.instructionPC 351 = 0x1e2 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 31
@[simp] theorem pc351 :
    instructionPC 351 = 0x1e2 := by
  exact refPc351

@[simp] theorem refPc352 :
    referenceArtifact.instructionPC 352 = 0x1e4 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 32
@[simp] theorem pc352 :
    instructionPC 352 = 0x1e4 := by
  exact refPc352

@[simp] theorem refPc353 :
    referenceArtifact.instructionPC 353 = 0x1e5 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 33
@[simp] theorem pc353 :
    instructionPC 353 = 0x1e5 := by
  exact refPc353

@[simp] theorem refPc354 :
    referenceArtifact.instructionPC 354 = 0x1e6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 34
@[simp] theorem pc354 :
    instructionPC 354 = 0x1e6 := by
  exact refPc354

@[simp] theorem refPc355 :
    referenceArtifact.instructionPC 355 = 0x1e8 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 35
@[simp] theorem pc355 :
    instructionPC 355 = 0x1e8 := by
  exact refPc355

@[simp] theorem refPc356 :
    referenceArtifact.instructionPC 356 = 0x1e9 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 36
@[simp] theorem pc356 :
    instructionPC 356 = 0x1e9 := by
  exact refPc356

@[simp] theorem refPc357 :
    referenceArtifact.instructionPC 357 = 0x1eb := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 37
@[simp] theorem pc357 :
    instructionPC 357 = 0x1eb := by
  exact refPc357

@[simp] theorem refPc358 :
    referenceArtifact.instructionPC 358 = 0x1ec := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 38
@[simp] theorem pc358 :
    instructionPC 358 = 0x1ec := by
  exact refPc358

@[simp] theorem refPc359 :
    referenceArtifact.instructionPC 359 = 0x1ed := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 39
@[simp] theorem pc359 :
    instructionPC 359 = 0x1ed := by
  exact refPc359

@[simp] theorem refPc360 :
    referenceArtifact.instructionPC 360 = 0x1ee := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 40
@[simp] theorem pc360 :
    instructionPC 360 = 0x1ee := by
  exact refPc360

@[simp] theorem refPc361 :
    referenceArtifact.instructionPC 361 = 0x1ef := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 41
@[simp] theorem pc361 :
    instructionPC 361 = 0x1ef := by
  exact refPc361

@[simp] theorem refPc362 :
    referenceArtifact.instructionPC 362 = 0x1f0 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 42
@[simp] theorem pc362 :
    instructionPC 362 = 0x1f0 := by
  exact refPc362

@[simp] theorem refPc363 :
    referenceArtifact.instructionPC 363 = 0x1f3 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 43
@[simp] theorem pc363 :
    instructionPC 363 = 0x1f3 := by
  exact refPc363

@[simp] theorem refPc364 :
    referenceArtifact.instructionPC 364 = 0x1f4 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 44
@[simp] theorem pc364 :
    instructionPC 364 = 0x1f4 := by
  exact refPc364

@[simp] theorem refPc365 :
    referenceArtifact.instructionPC 365 = 0x1f6 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 45
@[simp] theorem pc365 :
    instructionPC 365 = 0x1f6 := by
  exact refPc365

@[simp] theorem refPc366 :
    referenceArtifact.instructionPC 366 = 0x1f7 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 46
@[simp] theorem pc366 :
    instructionPC 366 = 0x1f7 := by
  exact refPc366

@[simp] theorem refPc367 :
    referenceArtifact.instructionPC 367 = 0x1fa := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 47
@[simp] theorem pc367 :
    instructionPC 367 = 0x1fa := by
  exact refPc367

@[simp] theorem refPc368 :
    referenceArtifact.instructionPC 368 = 0x1fb := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 48
@[simp] theorem pc368 :
    instructionPC 368 = 0x1fb := by
  exact refPc368

@[simp] theorem refPc369 :
    referenceArtifact.instructionPC 369 = 0x1fc := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 49
@[simp] theorem pc369 :
    instructionPC 369 = 0x1fc := by
  exact refPc369

@[simp] theorem refPc370 :
    referenceArtifact.instructionPC 370 = 0x1fd := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 50
@[simp] theorem pc370 :
    instructionPC 370 = 0x1fd := by
  exact refPc370

@[simp] theorem refPc371 :
    referenceArtifact.instructionPC 371 = 0x1ff := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 51
@[simp] theorem pc371 :
    instructionPC 371 = 0x1ff := by
  exact refPc371

@[simp] theorem refPc372 :
    referenceArtifact.instructionPC 372 = 0x200 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 52
@[simp] theorem pc372 :
    instructionPC 372 = 0x200 := by
  exact refPc372

@[simp] theorem refPc373 :
    referenceArtifact.instructionPC 373 = 0x202 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 53
@[simp] theorem pc373 :
    instructionPC 373 = 0x202 := by
  exact refPc373

@[simp] theorem refPc374 :
    referenceArtifact.instructionPC 374 = 0x203 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 54
@[simp] theorem pc374 :
    instructionPC 374 = 0x203 := by
  exact refPc374

@[simp] theorem refPc375 :
    referenceArtifact.instructionPC 375 = 0x204 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 55
@[simp] theorem pc375 :
    instructionPC 375 = 0x204 := by
  exact refPc375

@[simp] theorem refPc376 :
    referenceArtifact.instructionPC 376 = 0x207 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 56
@[simp] theorem pc376 :
    instructionPC 376 = 0x207 := by
  exact refPc376

@[simp] theorem refPc377 :
    referenceArtifact.instructionPC 377 = 0x208 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 57
@[simp] theorem pc377 :
    instructionPC 377 = 0x208 := by
  exact refPc377

@[simp] theorem refPc378 :
    referenceArtifact.instructionPC 378 = 0x209 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 58
@[simp] theorem pc378 :
    instructionPC 378 = 0x209 := by
  exact refPc378

@[simp] theorem refPc379 :
    referenceArtifact.instructionPC 379 = 0x20a := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 59
@[simp] theorem pc379 :
    instructionPC 379 = 0x20a := by
  exact refPc379

@[simp] theorem refPc380 :
    referenceArtifact.instructionPC 380 = 0x20c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 60
@[simp] theorem pc380 :
    instructionPC 380 = 0x20c := by
  exact refPc380

@[simp] theorem refPc381 :
    referenceArtifact.instructionPC 381 = 0x20d := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 61
@[simp] theorem pc381 :
    instructionPC 381 = 0x20d := by
  exact refPc381

@[simp] theorem refPc382 :
    referenceArtifact.instructionPC 382 = 0x20e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 62
@[simp] theorem pc382 :
    instructionPC 382 = 0x20e := by
  exact refPc382

@[simp] theorem refPc383 :
    referenceArtifact.instructionPC 383 = 0x20f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 63
@[simp] theorem pc383 :
    instructionPC 383 = 0x20f := by
  exact refPc383

@[simp] theorem refPc384 :
    referenceArtifact.instructionPC 384 = 0x212 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 64
@[simp] theorem pc384 :
    instructionPC 384 = 0x212 := by
  exact refPc384

@[simp] theorem refPc385 :
    referenceArtifact.instructionPC 385 = 0x213 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 65
@[simp] theorem pc385 :
    instructionPC 385 = 0x213 := by
  exact refPc385

@[simp] theorem refPc386 :
    referenceArtifact.instructionPC 386 = 0x215 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 66
@[simp] theorem pc386 :
    instructionPC 386 = 0x215 := by
  exact refPc386

@[simp] theorem refPc387 :
    referenceArtifact.instructionPC 387 = 0x216 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 67
@[simp] theorem pc387 :
    instructionPC 387 = 0x216 := by
  exact refPc387

@[simp] theorem refPc388 :
    referenceArtifact.instructionPC 388 = 0x217 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 68
@[simp] theorem pc388 :
    instructionPC 388 = 0x217 := by
  exact refPc388

@[simp] theorem refPc389 :
    referenceArtifact.instructionPC 389 = 0x219 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 69
@[simp] theorem pc389 :
    instructionPC 389 = 0x219 := by
  exact refPc389

@[simp] theorem refPc390 :
    referenceArtifact.instructionPC 390 = 0x21a := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 70
@[simp] theorem pc390 :
    instructionPC 390 = 0x21a := by
  exact refPc390

@[simp] theorem refPc391 :
    referenceArtifact.instructionPC 391 = 0x21b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 71
@[simp] theorem pc391 :
    instructionPC 391 = 0x21b := by
  exact refPc391

@[simp] theorem refPc392 :
    referenceArtifact.instructionPC 392 = 0x21c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 72
@[simp] theorem pc392 :
    instructionPC 392 = 0x21c := by
  exact refPc392

@[simp] theorem refPc393 :
    referenceArtifact.instructionPC 393 = 0x21d := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 73
@[simp] theorem pc393 :
    instructionPC 393 = 0x21d := by
  exact refPc393

@[simp] theorem refPc394 :
    referenceArtifact.instructionPC 394 = 0x21e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 74
@[simp] theorem pc394 :
    instructionPC 394 = 0x21e := by
  exact refPc394

@[simp] theorem refPc395 :
    referenceArtifact.instructionPC 395 = 0x21f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 75
@[simp] theorem pc395 :
    instructionPC 395 = 0x21f := by
  exact refPc395

@[simp] theorem refPc396 :
    referenceArtifact.instructionPC 396 = 0x220 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 76
@[simp] theorem pc396 :
    instructionPC 396 = 0x220 := by
  exact refPc396

@[simp] theorem refPc397 :
    referenceArtifact.instructionPC 397 = 0x222 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 77
@[simp] theorem pc397 :
    instructionPC 397 = 0x222 := by
  exact refPc397

@[simp] theorem refPc398 :
    referenceArtifact.instructionPC 398 = 0x223 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 78
@[simp] theorem pc398 :
    instructionPC 398 = 0x223 := by
  exact refPc398

@[simp] theorem refPc399 :
    referenceArtifact.instructionPC 399 = 0x224 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 79
@[simp] theorem pc399 :
    instructionPC 399 = 0x224 := by
  exact refPc399

@[simp] theorem refPc400 :
    referenceArtifact.instructionPC 400 = 0x225 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 80
@[simp] theorem pc400 :
    instructionPC 400 = 0x225 := by
  exact refPc400

@[simp] theorem refPc401 :
    referenceArtifact.instructionPC 401 = 0x226 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 81
@[simp] theorem pc401 :
    instructionPC 401 = 0x226 := by
  exact refPc401

@[simp] theorem refPc402 :
    referenceArtifact.instructionPC 402 = 0x229 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 82
@[simp] theorem pc402 :
    instructionPC 402 = 0x229 := by
  exact refPc402

@[simp] theorem refPc403 :
    referenceArtifact.instructionPC 403 = 0x22a := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 83
@[simp] theorem pc403 :
    instructionPC 403 = 0x22a := by
  exact refPc403

@[simp] theorem refPc404 :
    referenceArtifact.instructionPC 404 = 0x22b := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 84
@[simp] theorem pc404 :
    instructionPC 404 = 0x22b := by
  exact refPc404

@[simp] theorem refPc405 :
    referenceArtifact.instructionPC 405 = 0x22c := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 85
@[simp] theorem pc405 :
    instructionPC 405 = 0x22c := by
  exact refPc405

@[simp] theorem refPc406 :
    referenceArtifact.instructionPC 406 = 0x22d := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 86
@[simp] theorem pc406 :
    instructionPC 406 = 0x22d := by
  exact refPc406

@[simp] theorem refPc407 :
    referenceArtifact.instructionPC 407 = 0x22e := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 87
@[simp] theorem pc407 :
    instructionPC 407 = 0x22e := by
  exact refPc407

@[simp] theorem refPc408 :
    referenceArtifact.instructionPC 408 = 0x22f := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 88
@[simp] theorem pc408 :
    instructionPC 408 = 0x22f := by
  exact refPc408

@[simp] theorem refPc409 :
    referenceArtifact.instructionPC 409 = 0x230 := by
  simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
    ArtifactSnapshots.entries] using referenceArtifact_pc_snapshot 89
@[simp] theorem pc409 :
    instructionPC 409 = 0x230 := by
  exact refPc409

theorem initStore_valid (w : InitStore) (hw : w ∈ initStores) :
    referenceInstructions[w.index]? = some (.push w.valueWidth w.value) ∧
    instructionPC (w.index + 1) = instructionPC w.index + w.valueWidth.val + 1 ∧
    referenceInstructions[w.index + 1]? = some (.push w.offsetWidth w.offset) ∧
    instructionPC (w.index + 2) = instructionPC (w.index + 1) + w.offsetWidth.val + 1 ∧
    referenceInstructions[w.index + 2]? = some (.op .MSTORE) ∧
    instructionPC (w.index + 3) = instructionPC (w.index + 2) + 1 := by
  simp only [initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 100
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 101
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 102
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 103
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 104
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 105
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 106
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 107
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 108
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 109
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 110
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 111
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 112
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 113
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 114
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 115
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 116
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 117
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 118
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 119
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 120
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 121
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 122
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 123
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 124
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 125
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 126
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 127
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 128
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 129
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 130
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 131
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 132
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 133
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 134
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 135
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 136
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 137
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 138
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 139
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 140
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 141
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 142
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 143
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 144
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 145
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 146
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 147
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 148
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 149
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 150
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 151
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 152
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 153
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 154
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 155
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 156
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 157
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 158
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 159
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 160
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 161
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 162
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 163
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 164
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 165
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 166
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 167
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 168
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 169
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 170
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 171
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 172
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 173
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 174
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 175
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 176
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 177
  · refine ⟨?_, by norm_num [instructionPC], ?_,
      by norm_num [instructionPC], ?_, by norm_num [instructionPC]⟩
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 178
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 179
    · simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using referenceInstructions_snapshot 180

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Cached located path for the main-body call into `pad`. -/
def padEnterPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨764, .push ⟨2, by decide⟩ (UInt256.ofNat 0x62c), by
      have h := referenceArtifact_instruction_snapshot 181
      simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] at h
      exact h.trans (by rfl), by decide⟩,
   ⟨765, .push ⟨0, by decide⟩ ⟨0⟩, by
      have h := referenceArtifact_instruction_snapshot 182
      simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] at h
      exact h.trans (by rfl), by decide⟩,
   ⟨766, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1e0), by
      have h := referenceArtifact_instruction_snapshot 183
      simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] at h
      exact h.trans (by rfl), by decide⟩,
   ⟨767, .op .JUMP, by
      simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices,
        ArtifactSnapshots.entries] using
          referenceArtifact_instruction_snapshot 184,
      wfOp (by decide) trivial rfl⟩]

/-- Cached located path for RIPEMD padded-length arithmetic. -/
def padLengthPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨349, .op .JUMPDEST, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 29, wfOp (by decide) trivial rfl⟩,
   ⟨350, .op .CALLDATASIZE, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 30, wfOp (by decide) trivial rfl⟩,
   ⟨351, .push ⟨1, by decide⟩ (UInt256.ofNat 72), by have h := referenceArtifact_instruction_snapshot 31; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨352, .op (.Dup ⟨1, by decide⟩), by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 32, wfOp (by decide) trivial rfl⟩,
   ⟨353, .op .ADD, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 33, wfOp (by decide) trivial rfl⟩,
   ⟨354, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by have h := referenceArtifact_instruction_snapshot 34; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨355, .op .SHR, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 35, wfOp (by decide) trivial rfl⟩,
   ⟨356, .push ⟨1, by decide⟩ (UInt256.ofNat 6), by have h := referenceArtifact_instruction_snapshot 36; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨357, .op .SHL, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 37, wfOp (by decide) trivial rfl⟩,
   ⟨358, .op (.Swap ⟨1, by decide⟩), by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 38, wfOp (by decide) trivial rfl⟩,
   ⟨359, .op .POP, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 39, wfOp (by decide) trivial rfl⟩]

/-- Cached located path for copying calldata and setting up the footer loop. -/
def padSetupPath : List
    (Challenge.EvmProof.Stepper.Located referenceArtifact .Osaka) :=
  [⟨360, .op (.Dup ⟨0, by decide⟩), by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 40, wfOp (by decide) trivial rfl⟩,
   ⟨361, .push ⟨0, by decide⟩ ⟨0⟩, by have h := referenceArtifact_instruction_snapshot 41; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨362, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by have h := referenceArtifact_instruction_snapshot 42; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨363, .op .CALLDATACOPY, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 43, wfOp (by decide) trivial rfl⟩,
   ⟨364, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by have h := referenceArtifact_instruction_snapshot 44; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨365, .op (.Dup ⟨1, by decide⟩), by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 45, wfOp (by decide) trivial rfl⟩,
   ⟨366, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by have h := referenceArtifact_instruction_snapshot 46; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨367, .op .ADD, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 47, wfOp (by decide) trivial rfl⟩,
   ⟨368, .op .MSTORE8, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 48, wfOp (by decide) trivial rfl⟩,
   ⟨369, .op (.Dup ⟨0, by decide⟩), by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 49, wfOp (by decide) trivial rfl⟩,
   ⟨370, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by have h := referenceArtifact_instruction_snapshot 50; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨371, .op .SHL, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 51, wfOp (by decide) trivial rfl⟩,
   ⟨372, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by have h := referenceArtifact_instruction_snapshot 52; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨373, .op (.Dup ⟨3, by decide⟩), by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 53, wfOp (by decide) trivial rfl⟩,
   ⟨374, .op .SUB, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 54, wfOp (by decide) trivial rfl⟩,
   ⟨375, .push ⟨2, by decide⟩ (UInt256.ofNat 0x800), by have h := referenceArtifact_instruction_snapshot 55; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨376, .op .ADD, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 56, wfOp (by decide) trivial rfl⟩,
   ⟨377, .push ⟨0, by decide⟩ ⟨0⟩, by have h := referenceArtifact_instruction_snapshot 57; simp [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] at h; exact h.trans (by rfl), by decide⟩,
   ⟨378, .op .JUMPDEST, by simpa [snapshotIndex, snapshotEntry, ArtifactSnapshots.indices, ArtifactSnapshots.entries] using referenceArtifact_instruction_snapshot 58, wfOp (by decide) trivial rfl⟩]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
