import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.EntryTemplates

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat pc }

def mainStart (input : ByteArray) : State := atPC input 0x03ef

abbrev Entry := Challenge.EvmProof.CertifiedArtifact.Entry
abbrev Certificate (entry : Entry) : Prop :=
  Challenge.EvmProof.CertifiedArtifact.DecoderCertificate
    .Osaka referenceBytecode entry

theorem runPushJump (input : ByteArray) (current target : Nat)
    (hcurrent : current + 3 < 2 ^ 256) (htarget : target < 2 ^ 256)
    (hvalid : Decode.isValidJumpDest referenceBytecode target = true)
    (pushDecoder : Certificate
      ⟨current, .push 2 (UInt256.ofNat target)⟩)
    (jumpDecoder : Certificate ⟨current + 3, .op .JUMP⟩) :
    Artifact.referenceCertifiedArtifact.runSelected
      [⟨⟨current, .push 2 (UInt256.ofNat target)⟩, pushDecoder⟩,
       ⟨⟨current + 3, .op .JUMP⟩, jumpDecoder⟩]
      (atPC input current) = some (atPC input target, 11) := by
  have hcurrent' : current < 2 ^ 256 := by omega
  have hcurrentWord : (UInt256.ofNat current).toNat = current := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hcurrent']
  have htargetWord : (UInt256.ofNat target).toNat = target := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt htarget]
  have hpc : UInt256.ofNat current + UInt256.ofNat 3 =
      UInt256.ofNat (current + 3) := addSmall current 3 hcurrent
  norm_num at hcurrent
  simp [Challenge.EvmProof.CertifiedArtifact.runSelected_cons,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Stepper.instrCost, Gas.baseCost, atPC, initialState,
    hpc, hcurrent, hcurrentWord, htargetWord, hvalid]

theorem runJumpBlock (input : ByteArray) (current target : Nat)
    (hcurrent : current + 4 < 2 ^ 256) (htarget : target < 2 ^ 256)
    (hvalid : Decode.isValidJumpDest referenceBytecode target = true)
    (jumpdestDecoder : Certificate ⟨current, .op .JUMPDEST⟩)
    (pushDecoder : Certificate
      ⟨current + 1, .push 2 (UInt256.ofNat target)⟩)
    (jumpDecoder : Certificate ⟨current + 4, .op .JUMP⟩) :
    Artifact.referenceCertifiedArtifact.runSelected
      [⟨⟨current, .op .JUMPDEST⟩, jumpdestDecoder⟩,
       ⟨⟨current + 1, .push 2 (UInt256.ofNat target)⟩, pushDecoder⟩,
       ⟨⟨current + 4, .op .JUMP⟩, jumpDecoder⟩]
      (atPC input current) = some (atPC input target, 12) := by
  have hcurrent' : current < 2 ^ 256 := by omega
  have hsucc : current + 1 < 2 ^ 256 := by omega
  have hcurrentWord : (UInt256.ofNat current).toNat = current := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hcurrent']
  have htargetWord : (UInt256.ofNat target).toNat = target := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt htarget]
  have hpc1 : (UInt256.ofNat current).succ =
      UInt256.ofNat (current + 1) := succSmall current hsucc
  have hpc4 : UInt256.ofNat (current + 1) + UInt256.ofNat 3 =
      UInt256.ofNat (current + 4) := by
    rw [show current + 4 = (current + 1) + 3 by omega]
    exact addSmall (current + 1) 3 (by omega)
  norm_num at hcurrent hsucc
  simp [Challenge.EvmProof.CertifiedArtifact.runSelected_cons,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Stepper.instrCost, Gas.baseCost, atPC, initialState,
    hpc1, hpc4, hcurrent, hsucc, hcurrentWord, htargetWord, hvalid]

theorem runJumpdest (input : ByteArray) (current : Nat)
    (hcurrent : current + 1 < 2 ^ 256)
    (decoder : Certificate ⟨current, .op .JUMPDEST⟩) :
    Artifact.referenceCertifiedArtifact.runSelected
      [⟨⟨current, .op .JUMPDEST⟩, decoder⟩] (atPC input current) =
        some (atPC input (current + 1), 1) := by
  have hcurrent' : current < 2 ^ 256 := by omega
  have hcurrentWord : (UInt256.ofNat current).toNat = current := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hcurrent']
  simp [Challenge.EvmProof.CertifiedArtifact.runSelected_cons,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Stepper.instrCost, Gas.baseCost, atPC, initialState,
    succSmall current hcurrent, hcurrentWord]

end Challenge.Ripemd160.Reference.Proofs.Bytecode.EntryTemplates
