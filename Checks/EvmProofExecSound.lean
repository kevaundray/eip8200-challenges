import Challenge.EvmProof.ExecSound

set_option warningAsError true

open YulSemantics

example {E : ExecDialect} [DecidableEq E.toDialect.Value]
    (hbuiltin : ∀ op args st result,
      E.builtinFn op args st = some result →
        E.toDialect.Builtin op args st result)
    {fuel program st0 V' st' outcome}
    (h : Interp.run E fuel program st0 = .ok (V', st', outcome)) :
    Run E.toDialect program st0 V' st' outcome :=
  Interp.run_sound_of hbuiltin h

/-- info: 'YulSemantics.Interp.sound_all_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.sound_all_of

/-- info: 'YulSemantics.Interp.run_sound_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms YulSemantics.Interp.run_sound_of
