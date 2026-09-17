import QuantumFoundations.BornRule.RCNote

/-!
# Journal audit: refinement-consistency Born note

This publication-facing audit checks the exact six-declaration theorem surface
of the compact refinement-consistency note.  The module adds no theorem body;
it only verifies declaration visibility with `#check` and reports the kernel
trust base with `#print axioms`.

The audited declarations are:

- `refinement_binaryGenerated`: every finite projective refinement is generated
  by elementary binary splits;
- `splitRCBornCalibration_projector`: elementary split consistency together
  with normalization, positivity and projective null support forces the
  pure-state Born weights in dimension at least three;
- `sharpness_remove_norm`: normalization fixes the global scale;
- `sharpness_remove_null`: projective null support fixes the target state;
- `sharpness_remove_rc`: refinement consistency removes resolution/context
  dependence;
- `sharpness_remove_pos`: positivity excludes the Hermitian cross-term witness.
-/

open QuantumFoundations.BornRule

-- ── Public-contract visibility ──────────────────────────────────────

#check @refinement_binaryGenerated
#check @splitRCBornCalibration_projector
#check @sharpness_remove_norm
#check @sharpness_remove_null
#check @sharpness_remove_rc
#check @sharpness_remove_pos

-- ── Trust-base audit ─────────────────────────────────────────────────

#print axioms QuantumFoundations.BornRule.refinement_binaryGenerated
#print axioms QuantumFoundations.BornRule.splitRCBornCalibration_projector
#print axioms QuantumFoundations.BornRule.sharpness_remove_norm
#print axioms QuantumFoundations.BornRule.sharpness_remove_null
#print axioms QuantumFoundations.BornRule.sharpness_remove_rc
#print axioms QuantumFoundations.BornRule.sharpness_remove_pos
