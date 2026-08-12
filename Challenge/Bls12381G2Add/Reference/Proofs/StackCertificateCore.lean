import Challenge.Bls12381G2Add.Reference.Proofs.FrozenStackCertificate
import Challenge.EvmProof.StackCertificate

set_option warningAsError true

/-!
# Chunked G2ADD stack-certificate checking

Challenge-local aliases instantiate the shared compact checker with the frozen
G2ADD program and data. Bounded chunks remain separate compilation units.
-/

namespace Challenge.Bls12381G2Add.Reference.Proofs.Compilation

open YulEvmCompiler

abbrev stackKeyChecks (entries : List CertEntry) : Bool :=
  Challenge.EvmProof.StackCertificate.keyChecks
    referenceOptimizedAssembly entries

abbrev stackInitialCheck : Bool :=
  Challenge.EvmProof.StackCertificate.initialCheck
    referenceOptimizedAssembly referenceStackCertificate

abbrev stackEntryChecks (entries : List CertEntry) : Bool :=
  Challenge.EvmProof.StackCertificate.entryChecks
    referenceOptimizedAssembly referenceStackCertificate entries

abbrev stackIndexedEntryChecks (entries : List CertEntry) : Bool :=
  Challenge.EvmProof.StackCertificate.indexedEntryChecks
    referenceOptimizedAssembly referenceStackCertificate entries

abbrev FrozenCertValue :=
  Challenge.EvmProof.StackCertificate.FrozenCertValue

def thawCertValue (value : FrozenCertValue) : CertValue :=
  (value.1.map decodeStackSlot, value.2.1,
    value.2.2.map decodeStackSlot)

def frozenLayoutAt (key : Nat) : Option CertValue :=
  (frozenStackEntries.find? fun entry => entry.1 == key).map fun entry =>
    thawCertValue (entry.2.1, entry.2.2.1, entry.2.2.2)

def referenceLengthLookup : CertLookup :=
  fun suffix => frozenLayoutAt suffix.length

abbrev stackLengthEntryChecks (entries : List CertEntry) : Bool :=
  Challenge.EvmProof.StackCertificate.lengthEntryChecks
    referenceOptimizedAssembly referenceLengthLookup entries

theorem stackIndexedEntryChecks_eq (entries : List CertEntry) :
    stackIndexedEntryChecks entries = stackEntryChecks entries :=
  Challenge.EvmProof.StackCertificate.indexedEntryChecks_eq
    referenceOptimizedAssembly referenceStackCertificate entries

theorem checkCert_eq_chunkChecks :
    checkCert referenceOptimizedAssembly referenceStackCertificate =
      (stackKeyChecks referenceStackCertificate.entries &&
        (stackInitialCheck &&
          stackEntryChecks referenceStackCertificate.entries)) :=
  Challenge.EvmProof.StackCertificate.checkCert_eq_chunkChecks
    referenceOptimizedAssembly referenceStackCertificate

theorem all_take_drop {α : Type} (f : α → Bool) (xs : List α) (n : Nat)
    (hhead : (xs.take n).all f = true)
    (htail : (xs.drop n).all f = true) : xs.all f = true :=
  Challenge.EvmProof.StackCertificate.all_take_drop f xs n hhead htail

theorem stackLengthEntryChecks_take_drop (entries : List CertEntry) (n : Nat)
    (hhead : stackLengthEntryChecks (entries.take n) = true)
    (htail : stackLengthEntryChecks (entries.drop n) = true) :
    stackLengthEntryChecks entries = true :=
  Challenge.EvmProof.StackCertificate.lengthEntryChecks_take_drop
    referenceOptimizedAssembly referenceLengthLookup entries n hhead htail

end Challenge.Bls12381G2Add.Reference.Proofs.Compilation
