-- This document is a lean benchmark file for the "Homotopy types in terms of critical values" theorem.
-- Written by Ziyang Qin, with edits by Daniel Halpern-Leistner

import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homotopy.Equiv

/-!
  We work with smooth real manifolds modelled on a normed space.
  Throughout, `M` is a smooth manifold with corners modelled on `H` via `I`,
  where `H` is modelled on a real normed space `E`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
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
  $H_p f : T_p M \times T_p M \to \mathbb{R}$ defined as the second derivative of the chart
  representative $f \circ (\mathrm{extChartAt}\, I\, p)^{-1}$ at the image of $p$, read through
  the canonical identification $T_p M \cong E$ given by the preferred chart.  At a critical
  point this bilinear form is independent of the choice of chart (see
  `IntrinsicHessian_chart_indep`), which is what makes it intrinsic.
  \NL_proof:
-/
noncomputable def IntrinsicHessian (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M] (f : M → ℝ) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp
    (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I p).symm)) (extChartAt I p p)).toLinearMap

/-! NODE
  \name: IntrinsicHessian_chart_indep
  \inputs: ["IsCriticalPoint", "IntrinsicHessian"]
  \type: proposition
  \natural: At a critical point $p$ of a smooth function $f$, the Hessian computed in the
  preferred chart agrees with the Hessian computed in any other smooth chart around $p$,
  after identifying tangent vectors via the derivative of the transition map.  Concretely:
  for any partial diffeomorphism $\psi$ from $M$ to the model space whose source contains $p$,
  the second derivative of $f \circ \psi^{-1}$ at $\psi(p)$, pulled back along
  $d\psi_p$, equals `IntrinsicHessian I f p`.
  \NL_proof: Write $g = f \circ \psi^{-1}$ and $\tau$ for the transition map between the two
  charts.  By the chain rule, the second derivative of $g \circ \tau$ is the pullback of the
  second derivative of $g$ along $d\tau$ plus a term involving the first derivative of $g$
  composed with the second derivative of $\tau$; the latter vanishes because $p$ is a
  critical point.
-/
theorem IntrinsicHessian_chart_indep [IsManifold I ⊤ M] [I.Boundaryless] (f : M → ℝ) (p : M)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f)
    (hp : IsCriticalPoint I f p)
    (ψ : PartialDiffeomorph I (modelWithCornersSelf ℝ E) M E ⊤)
    (hpψ : p ∈ ψ.source) (v w : TangentSpace I p) :
    fderiv ℝ (fderiv ℝ (f ∘ ψ.symm)) (ψ p)
        (mfderiv I (modelWithCornersSelf ℝ E) ψ p v)
        (mfderiv I (modelWithCornersSelf ℝ E) ψ p w)
      = IntrinsicHessian I f p v w := by
  sorry

/-! NODE
  \name: IntrinsicHessian_symm
  \inputs: ["IsCriticalPoint", "IntrinsicHessian"]
  \type: proposition
  \natural: At a critical point of a smooth function, the intrinsic Hessian is a symmetric
  bilinear form: $H_p f(v, w) = H_p f(w, v)$.
  \NL_proof: The Hessian is defined as a second Fréchet derivative of the chart representative,
  and second derivatives of $C^2$ functions are symmetric (Schwarz/Clairaut, available in
  Mathlib as the symmetry of the second derivative).
-/
theorem IntrinsicHessian_symm [IsManifold I ⊤ M] [I.Boundaryless] (f : M → ℝ) (p : M)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f)
    (hp : IsCriticalPoint I f p) (v w : TangentSpace I p) :
    IntrinsicHessian I f p v w = IntrinsicHessian I f p w v := by
  sorry

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
  \name: SublevelSet_isClosed
  \inputs: ["SublevelSet"]
  \type: proposition
  \natural: If $f$ is continuous then every sublevel set $M^c$ is closed in $M$.
  \NL_proof: $M^c = f^{-1}((-\infty, c])$ is the preimage of a closed set under a continuous map.
-/
theorem SublevelSet_isClosed (f : M → ℝ) (c : ℝ) (hf : Continuous f) :
    IsClosed (SublevelSet f c) :=
  isClosed_le hf continuous_const

/-! NODE
  \name: IsMorseChartAt
  \inputs: ["IsCriticalPoint"]
  \type: definition
  \natural: A chart $\varphi$ (a partial diffeomorphism from $M$ to $\mathbb{R}^n$,
  $n = \dim M$) is a Morse chart for $f$ at $p$ of index $\mathtt{idx}$ if $p$ lies in its
  source, $\varphi(p) = 0$, and on the source
  $f = f(p) - x_1^2 - \dots - x_{\mathtt{idx}}^2 + x_{\mathtt{idx}+1}^2 + \dots + x_n^2$
  in the coordinates $x = \varphi$.
  \NL_proof:
-/
def IsMorseChartAt (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M] (f : M → ℝ) (p : M) (idx : ℕ)
    (φ : PartialDiffeomorph I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ))
          M (Fin (Module.finrank ℝ E) → ℝ) ⊤) : Prop :=
  p ∈ φ.source ∧
  φ p = 0 ∧
  ∀ x ∈ φ.source,
    f x = f p + ∑ i : Fin (Module.finrank ℝ E),
      (if (i : ℕ) < idx then (-1 : ℝ) else 1) * (φ x i) ^ 2

/-! NODE
  \name: MorseLemma
  \inputs: ["NonDegenerateCriticalPoint", "IsMorseChartAt"]
  \type: theorem
  \natural: (Morse Lemma) Let $p$ be a non-degenerate critical point of $f$ of index $\mathtt{idx}$.
  Then there exists a Morse chart for $f$ at $p$ of index $\mathtt{idx}$, i.e. a chart $(U, x)$
  around $p$ with $x(p) = 0$ and
  $f = f(p) - x_1^2 - \dots - x_{\mathtt{idx}}^2 + x_{\mathtt{idx}+1}^2 + \dots + x_n^2$ on $U$.
  \NL_proof: By Taylor expansion and induction using the non-degeneracy of the Hessian.
-/
theorem MorseLemma [IsManifold I ⊤ M] [I.Boundaryless] (f : M → ℝ) (p : M) (idx : ℕ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f)
    (h : NonDegenerateCriticalPoint I f p idx)
    (hidx : idx ≤ Module.finrank ℝ E) :
    ∃ φ : PartialDiffeomorph I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ))
            M (Fin (Module.finrank ℝ E) → ℝ) ⊤,
      IsMorseChartAt I f p idx φ := by
  sorry

/-! NODE
  \name: GradientLikeVectorField
  \inputs: ["IsCriticalPoint", "NonDegenerateCriticalPoint", "IsMorseChartAt"]
  \type: definition
  \natural: A vector field $X$ on $M$ is gradient-like for $f$ if $X(f) > 0$ away from critical
  points, and around every non-degenerate critical point of index $\mathtt{idx}$ there is a
  Morse chart in which $X$ equals the gradient of the standard quadratic form
  $f(p) - x_1^2 - \dots - x_{\mathtt{idx}}^2 + x_{\mathtt{idx}+1}^2 + \dots + x_n^2$, i.e.
  $d\varphi(X) = (-2x_1, \dots, -2x_{\mathtt{idx}}, 2x_{\mathtt{idx}+1}, \dots, 2x_n)$
  at the point with coordinates $x = \varphi$ (so $X(f) = 4\|x\|^2 \ge 0$ there, consistent
  with the first condition; the descending flow used in Morse theory is the flow of $-X$).
  \NL_proof:
-/
def GradientLikeVectorField (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M]
    (f : M → ℝ) (X : (p : M) → TangentSpace I p) : Prop :=
  (∀ p : M, ¬ IsCriticalPoint I f p →
    (0 : ℝ) < show ℝ from mfderiv I (modelWithCornersSelf ℝ ℝ) f p (X p)) ∧
  (∀ (p : M) (idx : ℕ), NonDegenerateCriticalPoint I f p idx →
    ∃ φ : PartialDiffeomorph I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ))
            M (Fin (Module.finrank ℝ E) → ℝ) ⊤,
      IsMorseChartAt I f p idx φ ∧
      ∀ x ∈ φ.source,
        mfderiv I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ)) φ x (X x) =
          fun i : Fin (Module.finrank ℝ E) =>
            (if (i : ℕ) < idx then (-2 : ℝ) else 2) * φ x i)

/-! NODE
  \name: GradientLikeVectorField_exists
  \inputs: ["IsCriticalPoint", "NonDegenerateCriticalPoint", "GradientLikeVectorField"]
  \type: proposition
  \natural: If every critical point of a smooth function $f$ is non-degenerate (a Morse
  function), then there exists a gradient-like vector field for $f$.
  \NL_proof: Choose a Morse chart around each critical point and place the gradient
  of the standard quadratic form there; away from the critical points choose, in local charts,
  vector fields with $X(f) > 0$ (e.g. local Euclidean gradients).  Patch these together with a
  smooth partition of unity; the positivity condition is convex, so it survives the patching.
-/
theorem GradientLikeVectorField_exists [IsManifold I ⊤ M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f)
    (hmorse : ∀ p : M, IsCriticalPoint I f p → ∃ idx, NonDegenerateCriticalPoint I f p idx) :
    ∃ X : (p : M) → TangentSpace I p, GradientLikeVectorField I f X := by
  sorry

/-! NODE
  \name: DeformationRetract
  \inputs: []
  \type: definition
  \natural: A subset $A$ is a (strong) deformation retract of $B$ if $A \subseteq B$ and there
  is a continuous map $H : B \times [0, 1] \to B$ with $H(\cdot, 0) = \mathrm{id}$, with
  $H(\cdot, 1)$ taking values in $A$, and with $H(a, t) = a$ for all $a \in A$ and all $t$.
  In Morse theory, such retractions are constructed via the flow of a gradient-like vector field.
  \NL_proof:
-/
def DeformationRetract (A : Set M) (B : Set M) : Prop :=
  A ⊆ B ∧
  ∃ Ht : C(↥B × unitInterval, ↥B),
    (∀ b : ↥B, Ht (b, 0) = b) ∧
    (∀ b : ↥B, (Ht (b, 1) : M) ∈ A) ∧
    (∀ (b : ↥B) (t : unitInterval), (b : M) ∈ A → Ht (b, t) = b)

/-! NODE
  \name: DeformationRetract_homotopyEquiv
  \inputs: ["DeformationRetract"]
  \type: proposition
  \natural: If $A$ is a deformation retract of $B$, then the inclusion $A \hookrightarrow B$
  is a homotopy equivalence.
  \NL_proof: The retraction $r = H(\cdot, 1) : B \to A$ satisfies $r \circ \iota = \mathrm{id}_A$
  on the nose (since $H$ fixes $A$ pointwise), and $\iota \circ r \simeq \mathrm{id}_B$ via the
  homotopy $H$ itself.
-/
theorem DeformationRetract_homotopyEquiv (A B : Set M) (h : DeformationRetract A B) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥A ↥B) := by
  sorry

/-! NODE
  \name: NoCriticalPoints_deformationRetract
  \inputs: ["IsCriticalPoint", "SublevelSet", "GradientLikeVectorField", "DeformationRetract"]
  \type: theorem
  \natural: (Milnor, Theorem 3.1) Let $a < b$ and suppose $f^{-1}[a, b]$ is compact and contains
  no critical points of $f$.  Then $M^a$ is a deformation retract of $M^b$.
  \NL_proof: Flow along (the negative of) a gradient-like vector field, rescaled by
  $1 / X(f)$ inside $f^{-1}[a,b]$ so that $f$ decreases at unit speed; compactness guarantees
  the flow exists for the required time and pushes $M^b$ down into $M^a$ while fixing $M^a$.
-/
theorem NoCriticalPoints_deformationRetract [IsManifold I ⊤ M] [I.Boundaryless] [T2Space M]
    (f : M → ℝ) (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f)
    (a b : ℝ) (hab : a < b)
    (h_compact : IsCompact (f ⁻¹' (Set.Icc a b)))
    (h_no_crit : ∀ q ∈ f ⁻¹' (Set.Icc a b), ¬ IsCriticalPoint I f q) :
    DeformationRetract (SublevelSet f a) (SublevelSet f b) := by
  sorry

/-! NODE
  \name: HandleAttachment
  \inputs: ["DeformationRetract"]
  \type: definition
  \natural: $Y$ has the homotopy type of $X$ with an $\mathtt{idx}$-cell attached (inside the
  ambient space $M$) if $X \subseteq Y$ and there is a continuous map
  $e : D^{\mathtt{idx}} \to M$ from the closed unit disk such that: the image of $e$ lies in
  $Y$; the boundary sphere is sent into $X$; the open disk is sent injectively into the
  complement of $X$; and $X \cup e(D^{\mathtt{idx}})$ is a deformation retract of $Y$.
  (When $M$ is Hausdorff, $e$ restricted to the compact disk is a closed map, so
  $X \cup e(D^{\mathtt{idx}})$ automatically carries the adjunction-space topology of
  $X \cup_{e|_{\partial}} D^{\mathtt{idx}}$; thus this captures cell attachment up to
  homotopy equivalence.)
  \NL_proof:
-/
def HandleAttachment (X : Set M) (Y : Set M) (idx : ℕ) : Prop :=
  X ⊆ Y ∧
  ∃ e : C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin idx)) 1), M),
    (∀ v, e v ∈ Y) ∧
    (∀ v : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin idx)) 1),
        ‖(v : EuclideanSpace ℝ (Fin idx))‖ = 1 → e v ∈ X) ∧
    (∀ v : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin idx)) 1),
        ‖(v : EuclideanSpace ℝ (Fin idx))‖ < 1 → e v ∉ X) ∧
    (∀ v w : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin idx)) 1),
        ‖(v : EuclideanSpace ℝ (Fin idx))‖ < 1 → ‖(w : EuclideanSpace ℝ (Fin idx))‖ < 1 →
        e v = e w → v = w) ∧
    DeformationRetract (X ∪ Set.range e) Y

/-! NODE
  \name: HomotopyTypesCriticalValues
  \inputs: ["IsCriticalPoint", "NonDegenerateCriticalPoint", "SublevelSet", "IsMorseChartAt",
            "MorseLemma", "GradientLikeVectorField", "NoCriticalPoints_deformationRetract",
            "DeformationRetract", "HandleAttachment"]
  \type: theorem
  \natural: Let $f: M \to \mathbb{R}$ be a smooth function, and let $p$ be a non-degenerate
  critical point with index $\mathtt{idx}$.  Setting $f(p) = c$, suppose that
  $f^{-1}[c-\epsilon,c+\epsilon]$ is compact and contains no critical point of $f$ other than $p$,
  for some $\epsilon > 0$.  Then, for all sufficiently small $\epsilon$, the set $M^{c+\epsilon}$
  has the homotopy type of $M^{c-\epsilon}$ with a $\mathtt{idx}$-cell attached.
  \NL_proof: We first use `MorseLemma` around $p$ to find a chart where $f$ is exactly quadratic.
  Then we construct a `GradientLikeVectorField` $X$ matching the quadratic-form gradient inside
  the chart and with $X(f) > 0$ outside.  We construct a thickened handle region
  $H \cong D^{\mathtt{idx}} \times D^{n-\mathtt{idx}}$ around $p$.  Using the flow of $-X$ we prove
  a `DeformationRetract` from $M^{c+\epsilon} \setminus H$ into $M^{c-\epsilon}$ (away from the
  critical level this is `NoCriticalPoints_deformationRetract`).  Since $H$ is attached to
  $M^{c-\epsilon}$ via its boundary and retracts onto its core $\mathtt{idx}$-cell, this is a
  `HandleAttachment`, showing $M^{c+\epsilon}$ is homotopy equivalent to $M^{c-\epsilon}$ with
  an $\mathtt{idx}$-cell attached.
-/
theorem HomotopyTypesCriticalValues
    [IsManifold I ⊤ M] [I.Boundaryless] [T2Space M] (f : M → ℝ) (p : M) (idx : ℕ) (c : ℝ) (ε : ℝ)
    (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f)
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
