import QuantumFoundations.Selectors.AncillaNeutrality
import QuantumFoundations.Selectors.TensorMultiplicativity

namespace QuantumFoundations.Selector

open QuantumFoundations.FiniteTensor

theorem bridge_tensor_decomposition_nonempty {n a : ℕ} :
    Nonempty (TensorDecomposition n a) := tensorDecomposition_nonempty n a

end QuantumFoundations.Selector
