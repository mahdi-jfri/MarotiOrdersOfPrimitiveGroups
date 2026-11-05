module

import Maroti
import all Maroti.Assembly.Classification
import all Maroti.Main

/-!
Adapted from AxiomMath/CFSGCorollary, Checks/ImportBoundary.lean, Apache-2.0.

# The theorem does not use AxiomMath/CFSG's proof of the classification

Fails the build if `Maroti.theorem_1_1_of_families` or `Maroti.theorem_1_1_of_classification`
depends on `CFSG.Certified.classification_finite_simple_groups` or the declarations
it is built from. The script `tools/import_boundary.py` checks the other half: no module that
proves the classification is reachable from `Maroti` through imports of any kind. That script reads
source headers, because loading the `.olean` files of all of CFSG in one Lean process takes too
many memory maps. Thus the classification enters only through the explicit hypothesis
`hCFSG : TauCeti.ClassificationStatement.{0}`.
-/

open Lean in
run_meta do
  let env ← getEnv
  let forbiddenConstants : NameSet := NameSet.ofList [
    `CFSG.Certified.classification_finite_simple_groups,
    `CFSG.classification_finite_simple_groups,
    `CFSG.Assembly.classification,
    `CFSG.Assembly.kProper_classification,
    `CFSG.Assembly.charTwo_classification,
    `CFSG.Assembly.disconnected_involution_graph,
    `CFSG.Assembly.low_two_rank,
    `CFSG.Assembly.component_dichotomy,
    `CFSG.Assembly.component_type,
    `CFSG.Assembly.quasithin,
    `CFSG.Assembly.rank_three_even,
    `CFSG.Assembly.large_even
  ]
  let roots : Array Name :=
    #[``Maroti.theorem_1_1_of_families, ``Maroti.theorem_1_1_of_classification]
  let mut seen : NameSet := {}
  let mut constants := roots
  while !constants.isEmpty do
    let c := constants.back!
    constants := constants.pop
    if seen.contains c then continue
    seen := seen.insert c
    if forbiddenConstants.contains c then
      throwError "the theorem depends on forbidden classification declaration {c}"
    let some i := env.getModuleIdxFor? c | throwError "{c} is not imported"
    let m := env.header.moduleNames[i.toNat]!
    if m == `Maroti.Assembly.Classification || m == `Maroti.Main then
      let some ci := env.find? c | throwError "unknown constant {c}"
      let some v := ci.value? (allowOpaque := true) | throwError "the value of {c} is not available"
      constants := constants ++ ci.type.getUsedConstants ++ v.getUsedConstants
    else if (`Maroti).isPrefixOf m then
      let some ci := env.find? c | throwError "unknown constant {c}"
      constants := constants ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        constants := constants ++ v.getUsedConstants
  logInfo m!"ImportBoundary check passed ({seen.size} constants checked)"
