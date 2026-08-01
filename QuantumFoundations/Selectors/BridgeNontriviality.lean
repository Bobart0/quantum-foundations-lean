import QuantumFoundations.Selectors.BridgeNonvacuity
import QuantumFoundations.Selectors.Nonvacuity

namespace QuantumFoundations.Selector

theorem covariance_without_nsnc1 :
    IsCovariant (tSelector 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)) ∧
      ¬ NSNC1 (tSelector 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)) := by
  exact tSelector_half_covariant_not_nsnc1

end QuantumFoundations.Selector
