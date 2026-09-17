import QuantumFoundations.BornRule.RCBornCalibration
import QuantumFoundations.BornRule.RCSharpnessResolution
import QuantumFoundations.BornRule.RCSharpnessPositivity

/-!
# Refinement-consistency Born note facade

This module is the compact publication-facing entry point for the refinement-
consistency note.  It deliberately adds no new mathematical result: it exposes
only the structural split-generation theorem, the Born-calibration theorem, and
the four relative-sharpness witnesses.

The intended public theorem surface is:

- `refinement_binaryGenerated`;
- `splitRCBornCalibration_projector`;
- `sharpness_remove_norm`;
- `sharpness_remove_null`;
- `sharpness_remove_rc`;
- `sharpness_remove_pos`.

The mathematical scope is intentionally frozen here.  Auxiliary constructions
used by the proofs remain implementation details of the imported modules.
-/
