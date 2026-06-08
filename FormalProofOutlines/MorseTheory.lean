-- This document is a lean benchmark file for the "Homotopy types in terms of critical values" theorem.
-- Written by Ziyang Qin, with edits by Daniel Halpern-Leistner

import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
  We work with smooth real manifolds modelled on a normed space.
  Throughout, `M` is a smooth manifold with corners modelled on `H` via `I`,
  where `H` is modelled on a real normed space `E`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! NODE
  \name: IsCriticalPoint
  \inputs: []
  \type: definition
  \natural: A point $p \in M$ is a critical point of a smooth function $f: M \to \mathbb{R}$ if the differential of $f$ vanishes at $p$.
  \NL_proof:
-/
def IsCriticalPoint (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M] (f : M → ℝ) (p : M) : Prop :=
  mfderiv I (modelWithCornersSelf ℝ ℝ) f p = 0

/-! NODE
  \name: IntrinsicHessian
  \inputs: ["IsCriticalPoint"]
  \type: definition
  \natural: The intrinsic Hessian of $f$ at a critical point $p$ is the symmetric bilinear form
  $H_p f : T_p M \times T_p M \to \mathbb{R}$ defined (intrinsically, independent of chart) as the
  second-order term of the Taylor expansion of $f$ at $p$.  It is well-defined as a bilinear form
  on the tangent space precisely because $p$ is a critical point.
  \NL_proof:
-/
noncomputable def IntrinsicHessian (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M] (f : M → ℝ) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ := sorry

/-! NODE
  \name: NonDegenerateCriticalPoint
  \inputs: ["IsCriticalPoint", "IntrinsicHessian"]
  \type: definition
  \natural: A point $p$ is a non-degenerate critical point of a smooth function $f$ if it is a
  critical point and the Hessian of $f$ at $p$ is non-degenerate.  The index $\mathtt{idx}$ is the
  number of negative eigenvalues of the Hessian (i.e., the dimension of the maximal subspace on
  which the Hessian is negative-definite).
  \NL_proof:
-/
def NonDegenerateCriticalPoint (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M] (f : M → ℝ) (p : M) (idx : ℕ) : Prop :=
  IsCriticalPoint I f p ∧
  -- Non-degeneracy: the Hessian has trivial kernel
  (∀ v : TangentSpace I p,
      (∀ w : TangentSpace I p, (IntrinsicHessian I f p v) w = 0) → v = 0) ∧
  -- Index: there exists a subspace of dimension idx that is negative-definite for the Hessian,
  -- and it is maximal with this property
  (∃ V : Submodule ℝ (TangentSpace I p),
    Module.finrank ℝ V = idx ∧
    (∀ v ∈ V, v ≠ 0 → (IntrinsicHessian I f p v) v < 0) ∧
    (∀ W : Submodule ℝ (TangentSpace I p),
        (∀ w ∈ W, w ≠ 0 → (IntrinsicHessian I f p w) w < 0) →
        Module.finrank ℝ W ≤ idx))

/-! NODE
  \name: SublevelSet
  \inputs: []
  \type: definition
  \natural: The sublevel set $M^c$ is the set of all points $x \in M$ such that $f(x) \le c$.
  \NL_proof:
-/
def SublevelSet (f : M → ℝ) (c : ℝ) : Set M :=
  {x : M | f x ≤ c}

/-! NODE
  \name: MorseLemma
  \inputs: ["NonDegenerateCriticalPoint"]
  \type: theorem
  \natural: (Morse Lemma) Let $p$ be a non-degenerate critical point of $f$ of index $\mathtt{idx}$.
  There exists a chart $(U, x)$ around $p$ such that $x(p) = 0$ and
  $f = f(p) - x_1^2 - \dots - x_{\mathtt{idx}}^2 + x_{\mathtt{idx}+1}^2 + \dots + x_n^2$ on $U$.
  \NL_proof: By Taylor expansion and induction using the non-degeneracy of the Hessian.
-/
theorem MorseLemma [IsManifold I ⊤ M] (f : M → ℝ) (p : M) (idx : ℕ)
    (h : NonDegenerateCriticalPoint I f p idx) : True := sorry

/-! NODE
  \name: GradientLikeVectorField
  \inputs: []
  \type: definition
  \natural: A vector field $X$ on $M$ is gradient-like for $f$ if $X(f) > 0$ away from critical
  points, and near any critical point, it matches the negative gradient of $f$ in Morse coordinates.
  \NL_proof:
-/
def GradientLikeVectorField (f : M → ℝ) (X : (p : M) → TangentSpace I p) : Prop := sorry

/-! NODE
  \name: HandleAttachment
  \inputs: []
  \type: definition
  \natural: A topological space $Y$ is obtained from $X$ by attaching a $\mathtt{idx}$-handle if
  $Y$ is homotopy equivalent to the pushout of
  $X \hookleftarrow S^{\mathtt{idx}-1} \times D^{n-\mathtt{idx}} \hookrightarrow
   D^{\mathtt{idx}} \times D^{n-\mathtt{idx}}$.
  \NL_proof:
-/
def HandleAttachment (X : Set M) (Y : Set M) (idx : ℕ) : Prop := sorry

/-! NODE
  \name: DeformationRetract
  \inputs: ["GradientLikeVectorField"]
  \type: definition
  \natural: A subset $A$ is a deformation retract of $B$ if there is a continuous map
  $H : B \times [0, 1] \to B$ taking $B$ to $A$ at $t=1$, while fixing $A$.  In Morse theory,
  this is constructed via the flow of a gradient-like vector field.
  \NL_proof:
-/
def DeformationRetract (A : Set M) (B : Set M) : Prop := sorry

/-! NODE
  \name: HomotopyTypesCriticalValues
  \inputs: ["IsCriticalPoint", "NonDegenerateCriticalPoint", "SublevelSet", "MorseLemma",
            "GradientLikeVectorField", "HandleAttachment", "DeformationRetract"]
  \type: theorem
  \natural: Let $f: M \to \mathbb{R}$ be a smooth function, and let $p$ be a non-degenerate
  critical point with index $\mathtt{idx}$.  Setting $f(p) = c$, suppose that
  $f^{-1}[c-\epsilon,c+\epsilon]$ is compact and contains no critical point of $f$ other than $p$,
  for some $\epsilon > 0$.  Then, for all sufficiently small $\epsilon$, the set $M^{c+\epsilon}$
  has the homotopy type of $M^{c-\epsilon}$ with a $\mathtt{idx}$-cell attached.
  \NL_proof: We first use `MorseLemma` around $p$ to find a chart where $f$ is exactly quadratic.
  Then we construct a `GradientLikeVectorField` $X$ matching the negative gradient inside the chart
  and strictly decreasing $f$ outside.  We construct a thickened handle region
  $H \cong D^{\mathtt{idx}} \times D^{n-\mathtt{idx}}$ around $p$.  Using the flow of $X$ we prove
  a `DeformationRetract` from $M^{c+\epsilon} \setminus H$ into $M^{c-\epsilon}$.  Since $H$ is
  attached to $M^{c-\epsilon}$ via its boundary, this is a `HandleAttachment`, showing
  $M^{c+\epsilon}$ is homotopy equivalent to $M^{c-\epsilon}$ with an $\mathtt{idx}$-cell attached.
-/
theorem HomotopyTypesCriticalValues
    [IsManifold I ⊤ M] (f : M → ℝ) (p : M) (idx : ℕ) (c : ℝ) (ε : ℝ)
    (hc : f p = c)
    (h_nondeg : NonDegenerateCriticalPoint I f p idx)
    (h_compact : IsCompact (f ⁻¹' (Set.Icc (c - ε) (c + ε))))
    (h_no_other_crit : ∀ q ∈ f ⁻¹' (Set.Icc (c - ε) (c + ε)),
        q ≠ p → ¬ IsCriticalPoint I f q)
    (h_eps_pos : ε > 0) :
    ∃ ε₀ > 0, ∀ ε' ∈ Set.Ioo 0 ε₀, ε' < ε →
      HandleAttachment (SublevelSet f (c - ε')) (SublevelSet f (c + ε')) idx := by
  sorry

/-! ============================================================
    UNIT TEST: standard quadratic form on ℝ^(p+n+z)

    For non-negative integers p, n, z with p + n + z > 0, consider the function
      q(x) = x₀² + … + x_{p-1}²  −  x_p² − … − x_{p+n-1}²
    on ℝ^(p+n+z) (the last z coordinates do not appear).

    We assert (with sorry'd proofs) that:
      1. 0 is a critical point of q.
      2. If z > 0, the critical point is degenerate (z-dimensional kernel).
      3. If z = 0, the critical point is non-degenerate with index n.

    This serves as a sanity-check on the definitions of IsCriticalPoint,
    IntrinsicHessian, and NonDegenerateCriticalPoint.
    ============================================================ -/

section QuadraticFormUnitTest

/-
  We use the standard flat model: M = ℝ^d, I = modelWithCornersSelf ℝ (ℝ^d).
  Coordinates are `Fin d → ℝ`.
-/

/-- The standard quadratic form with `pos` positive squares, `neg` negative squares,
    and `zer` zero (absent) coordinates, on `ℝ^(pos+neg+zer)`. -/
noncomputable def stdQuadForm (pos neg zer : ℕ) : (Fin (pos + neg + zer) → ℝ) → ℝ :=
  fun x =>
    (∑ i : Fin pos,  x (Fin.castAdd zer (Fin.castAdd neg i)) ^ 2) -
    (∑ i : Fin neg,  x (Fin.castAdd zer (Fin.natAdd pos i)) ^ 2)

/-! NODE
  \name: QuadFormCriticalPoint
  \inputs: ["IsCriticalPoint"]
  \type: proposition
  \natural: The origin is a critical point of the standard quadratic form $q$ on
  $\mathbb{R}^{p+n+z}$ for all $p, n, z \ge 0$ with $p+n+z > 0$.
  \NL_proof: The differential of $q$ at $0$ is the linear map $v \mapsto 2\sum_{i<p} v_i e_i^*
  - 2\sum_{p \le i < p+n} v_i e_i^*$, which vanishes at $0$ because it is linear.
-/
theorem stdQuadForm_isCriticalPoint (pos neg zer : ℕ) (h : 0 < pos + neg + zer) :
    IsCriticalPoint (modelWithCornersSelf ℝ (Fin (pos + neg + zer) → ℝ))
      (stdQuadForm pos neg zer) 0 := by
  sorry

/-! NODE
  \name: QuadFormDegenerate
  \inputs: ["NonDegenerateCriticalPoint", "QuadFormCriticalPoint"]
  \type: proposition
  \natural: If $z > 0$, the critical point $0$ of the standard quadratic form on
  $\mathbb{R}^{p+n+z}$ is degenerate: for any index $\mathtt{idx}$, the point $0$ is
  \emph{not} a non-degenerate critical point of index $\mathtt{idx}$.
  \NL_proof: The last $z$ coordinates do not appear in $q$, so any tangent vector supported
  on those coordinates lies in the kernel of the Hessian, making it degenerate.
-/
theorem stdQuadForm_degenerate (pos neg zer : ℕ) (h : 0 < zer) (idx : ℕ) :
    ¬ NonDegenerateCriticalPoint (modelWithCornersSelf ℝ (Fin (pos + neg + zer) → ℝ))
        (stdQuadForm pos neg zer) 0 idx := by
  sorry

/-! NODE
  \name: QuadFormNonDegenerate
  \inputs: ["NonDegenerateCriticalPoint", "QuadFormCriticalPoint"]
  \type: proposition
  \natural: If $z = 0$, the critical point $0$ of the standard quadratic form on
  $\mathbb{R}^{p+n}$ is non-degenerate with index $n$.
  \NL_proof: The Hessian of $q$ at $0$ is the diagonal matrix
  $\mathrm{diag}(2,\dots,2,-2,\dots,-2)$ (block of $+2$ for the first $p$ coordinates,
  $-2$ for the next $n$), which is non-singular.  The negative-definite subspace is exactly
  the span of the last $n$ coordinate vectors, which has dimension $n$ and is maximal.
-/
theorem stdQuadForm_nonDegenerate (pos neg : ℕ) (h : 0 < pos + neg) :
    NonDegenerateCriticalPoint (modelWithCornersSelf ℝ (Fin (pos + neg) → ℝ))
      (stdQuadForm pos neg 0) 0 neg := by
  sorry

end QuadraticFormUnitTest
