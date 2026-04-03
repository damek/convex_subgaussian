import ConvexSubgaussian.CoreDefs
import ConvexSubgaussian.GaussianAsymptotics
import ConvexSubgaussian.GaussianMain

/-!
# ConvexSubgaussian

Umbrella import for the public one-dimensional Gaussian comparison
formalization.

Readers should usually start with:

- `ConvexSubgaussian.GaussianMain`
- `ConvexSubgaussian.GaussianAsymptotics`

The endpoint theorem `ConvexSubgaussian.sharp_convexSubgaussianComparison`
lives in `GaussianMain`. The paper constants and the public intermediate
domination and sharpness results live in `GaussianAsymptotics`.
-/
