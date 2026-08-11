import Challenge.EvmProof.ProfiledLowerCorrect
import YulEvmCompiler.Correctness

set_option warningAsError true

/-!
# Profiled Yul compiler correctness

This theorem composes the pinned Yul-to-assembly proof with the local profiled
Phase B.  It differs from `YulEvmCompiler.compile_correct` only by requiring a
caller profile at the initial target state and by routing successful calls
through `ProfiledCallsRealized`.
-/

namespace Challenge.EvmProof

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Outcome Ident VEnv)
open YulSemantics.EVM (U256 EvmState Op evmWithExternal)
open YulEvmCompiler

variable [model : ExternalModel]
local notation "yulD" => evmWithExternal model.calls model.creates

/-- End-to-end compiler correctness for a model whose successful calls carry
and preserve the target caller profile. -/
theorem profiled_compile_correct {config : PrecompileConfig}
    (hcalls : ProfiledCallsRealized model.calls config)
    (hcreates : model.creates = YulSemantics.EVM.ExternalCreates.none)
    {prog : YulSemantics.Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    {yst0 : EvmState} {V' : VEnv yulD} {yst' : EvmState} {o : Outcome}
    (hrun : YulSemantics.Run yulD prog yst0 V' yst' o) :
    ∃ b : Nat, ∀ s0 : State,
      FrameOK (assemble is) s0 → StateMatch yst0 s0 →
      CallerProfile config s0 →
      s0.pc = UInt256.ofNat 0 → s0.stack = [] → b ≤ s0.gasAvailable →
      ∃ s', Steps s0 s' ∧ s'.callStack = [] ∧ StateMatch yst' s' ∧
        ((o = .normal ∧ s'.halt = .Success ∧ s'.hReturn = .empty) ∨
         (o = .halt ∧ HaltedMatch yst' s')) := by
  rcases hpa : compileProgram prog with _ | asm
  · simp [compile, hpa] at hcomp
  · simp only [compile, hpa, bind, Option.bind] at hcomp
    obtain ⟨hstk, hcomp⟩ :
        stackOK2 (optimizeAsm asm) = true ∧
          lowerProg (optimizeAsm asm) = some is := by
      split at hcomp
      · next h => exact ⟨h, hcomp⟩
      · exact absurd hcomp (by simp)
    obtain ⟨scope, n0, Γ', n', hh, hnd, hcs, hwf⟩ :=
      compileProgramAsm_inv hpa
    have hnodup : (labelDefs asm).Nodup := (wfCheck_iff.mp hwf).nodup
    cases hrun with
    | block hbody =>
      have hM := SimA.sim hnodup hbody
      have hout := hM [scope] none none n0 asm Γ' n' trivial trivial hcs
      have hΦ0 : SimA.FEnvOK asm
          (YulSemantics.hoist yulD prog :: []) [scope] :=
        SimA.hoist_ok SimA.FEnvOK.nil hh hnd hcs (List.infix_refl asm)
      have hlen : (assembleBytes is).length = codeSize (optimizeAsm asm) :=
        lowerFrag_length hcomp
      have hsmallO : codeSize (optimizeAsm asm) < 256 ^ labelWidth := by
        have hopt := codeSize_optimizeAsm_le asm
        have hsmall := (wfCheck_iff.mp hwf).small
        omega
      cases o with
      | normal =>
        obtain ⟨-, -, hsimS⟩ := hout
        have hsteps0 := (hsimS hΦ0) [] [] [] (by simp)
        simp only [List.append_nil] at hsteps0
        have hstepsO := Peephole.optimizeAsm_asteps hnodup hsteps0
        obtain ⟨bnd, Hb⟩ := profiled_asteps_sim hcalls hcreates hcomp hsmallO
          hstepsO (List.suffix_refl (optimizeAsm asm))
          (stackOK2_run_bound hstk yst0)
        refine ⟨bnd, ?_⟩
        intro s0 hf hm hprofile hpc hstk0 hgas
        have hcm0 : ConfMatch (optimizeAsm asm) is
            ⟨optimizeAsm asm, [], yst0⟩ s0 :=
          ⟨by simpa using hf, hm, by rw [hpc]; simp,
            by rw [hstk0]; simp⟩
        obtain ⟨s1, hsteps1, hcm1, -, -⟩ :=
          Hb s0 hcm0 hprofile hgas
        have hpc1 : s1.pc = UInt256.ofNat (assembleBytes is).length := by
          rw [hcm1.pc]
          simp [hlen]
        have hframe1 : FrameOK (assemble is) s1 := by
          simpa using hcm1.frame
        obtain ⟨s2, hstep2, hsm2, hcs2, hhalt2, hret2⟩ :=
          stopStep (is := is) hframe1 hcm1.smatch
            (assemble_eq_mkCode is) hpc1 (by
              have hb := stackOK2_run_bound hstk yst0 _ hstepsO
              have hp : Operation.pushArity Operation.STOP = 0 := rfl
              have hq : Operation.popArity Operation.STOP = 0 := rfl
              dsimp only at hb
              rw [hcm1.stack]
              simp only [mapStk, List.length_map, hp, hq]
              omega)
        exact ⟨s2, hsteps1.snoc hstep2, hcs2, hsm2,
          Or.inl ⟨rfl, hhalt2, hret2⟩⟩
      | halt =>
        have hAS := hout hΦ0
        obtain ⟨conf, hsteps0, hhalt0⟩ := hAS [] [] [] (by simp)
        simp only [List.append_nil] at hsteps0
        obtain ⟨confO, hstepsO, hhaltO⟩ :=
          Peephole.optimizeAsm_ahalt hnodup hsteps0 hhalt0
        obtain ⟨b1, H1⟩ := profiled_asteps_sim hcalls hcreates hcomp
          hsmallO hstepsO (List.suffix_refl (optimizeAsm asm))
          (stackOK2_run_bound hstk yst0)
        obtain ⟨b2, H2⟩ := ahalt_sim hcomp hhaltO
          (hstepsO.suffix (List.suffix_refl (optimizeAsm asm)))
          (stackOK2_run_bound hstk yst0 confO hstepsO)
        refine ⟨b1 + b2, ?_⟩
        intro s0 hf hm hprofile hpc hstk0 hgas
        have hcm0 : ConfMatch (optimizeAsm asm) is
            ⟨optimizeAsm asm, [], yst0⟩ s0 :=
          ⟨by simpa using hf, hm, by rw [hpc]; simp,
            by rw [hstk0]; simp⟩
        obtain ⟨s1, htarget1, hm1, -, hgas1⟩ :=
          H1 s0 hcm0 hprofile (by omega)
        obtain ⟨s2, htarget2, hsm2, hcs2, hhm2⟩ :=
          H2 s1 hm1 (by omega)
        exact ⟨s2, htarget1.append htarget2, hcs2, hsm2,
          Or.inr ⟨rfl, hhm2⟩⟩
      | «break» =>
          rcases hout with ⟨lc, hlc, -⟩
          exact absurd hlc (by simp)
      | «continue» =>
          rcases hout with ⟨lc, hlc, -⟩
          exact absurd hlc (by simp)
      | leave =>
          rcases hout with ⟨fc, hfc, -⟩
          exact absurd hfc (by simp)

end Challenge.EvmProof
