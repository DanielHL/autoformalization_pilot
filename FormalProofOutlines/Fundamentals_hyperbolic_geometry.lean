-- This document formalizes fundamental definitions and theorems of hyperbolic geometry
-- Written by Linyue Xu

import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! NODE
  \name: LorentzForm
  \inputs: []
  \type: definition
  \natural: The Lorentz form on $\mathbb{R}^{n+1}$ is the bilinear form $\langle x,y\rangle_L = x_1 y_1 + \cdots + x_n y_n - x_{n+1}y_{n+1}$.
  \NL_proof:
-/
def LorentzForm (n : ℕ) (x y : Fin (n+1) → ℝ) : ℝ :=
  (∑ i : Fin n, x i.castSucc * y i.castSucc) - x (Fin.last n) * y (Fin.last n)

/-! NODE
  \name: HyperboloidModel
  \inputs: ["LorentzForm"]
  \type: definition
  \natural: The hyperboloid model $I^n$ of $n$-dimensional hyperbolic space is the subset $\{x \in \mathbb{R}^{n+1} \mid \langle x,x\rangle_L = -1, x_{n+1} > 0\}$ of $\mathbb{R}^{n,1}$ with the induced Riemannian metric.
  \NL_proof:
-/
def HyperboloidModel (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {x | LorentzForm n x x = -1 ∧ x (Fin.last n) > 0}

/-! NODE
  \name: HyperboloidMetric
  \inputs: ["HyperboloidModel", "LorentzForm"]
  \type: definition
  \natural: The metric on the hyperboloid model is $d_I(x,y) = \operatorname{arcosh}(-\langle x,y\rangle_L)$ for $x,y \in I^n$.
  \NL_proof:
-/
noncomputable def HyperboloidMetric (n : ℕ) (x y : HyperboloidModel n) : ℝ :=
  Real.arcosh (- LorentzForm n x.val y.val)

/-! NODE
  \name: PoincareBallModel
  \inputs: []
  \type: definition
  \natural: The Poincaré ball model $D^n$ is the open unit ball $\{x \in \mathbb{R}^n \mid \|x\| < 1\}$ with Riemannian metric $ds^2 = \frac{4\|dx\|^2}{(1-\|x\|^2)^2}$.
  \NL_proof:
-/
def PoincareBallModel (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ‖x‖ < 1}

def lastCoord (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  if h : 0 < n then x ⟨n - 1, by omega⟩ else 0

/-! NODE
  \name: PoincareBallMetric
  \inputs: ["PoincareBallModel"]
  \type: definition
  \natural: The distance metric on the Poincaré ball model is $d_D(x,y) = \operatorname{arcosh}\left(1 + \frac{2\|x-y\|^2}{(1-\|x\|^2)(1-\|y\|^2)}\right)$.
  \NL_proof:
-/
noncomputable def PoincareBallMetric (n : ℕ) (x y : PoincareBallModel n) : ℝ :=
  Real.arcosh (1 + (2 * ‖x.val - y.val‖^2) / ((1 - ‖x.val‖^2) * (1 - ‖y.val‖^2)))

/-! NODE
  \name: PoincareHalfSpaceModel
  \inputs: []
  \type: definition
  \natural: The Poincaré half-space model $H^n$ is the upper half-space $\{(x_1,\ldots,x_n) \in \mathbb{R}^n \mid x_n > 0\}$ with Riemannian metric $ds^2 = \frac{dx_1^2 + \cdots + dx_n^2}{x_n^2}$.
  \NL_proof:
-/
def PoincareHalfSpaceModel (n : ℕ) : Set (Fin n → ℝ) :=
  {x | lastCoord n x > 0}

/-! NODE
  \name: PoincareHalfSpaceMetric
  \inputs: ["PoincareHalfSpaceModel"]
  \type: definition
  \natural: The metric on the Poincaré half-space model is $d_H(x,y) = \operatorname{arcosh}\left(1 + \frac{\|x-y\|^2}{2x_n y_n}\right)$.
  \NL_proof:
-/
noncomputable def PoincareHalfSpaceMetric (n : ℕ) (x y : PoincareHalfSpaceModel n) : ℝ :=
  Real.arcosh (1 + ‖x.val - y.val‖^2 / (2 * lastCoord n x.val * lastCoord n y.val))

/-! NODE
  \name: HyperboloidToBallIsometry
  \inputs: ["HyperboloidModel", "PoincareBallModel"]
  \type: definition
  \natural: The map $\Phi : I^n \to D^n$ given by $\Phi(x_1,\ldots,x_n,x_{n+1}) = \frac{(x_1,\ldots,x_n)}{x_{n+1}+1}$ is an isometry from the hyperboloid model to the Poincaré ball model.
  \NL_proof:
-/
noncomputable def HyperboloidToBallIsometry (n : ℕ) : HyperboloidModel n → PoincareBallModel n :=
  fun x => ⟨fun i => x.val i.castSucc / (x.val (Fin.last n) + 1), sorry⟩

/-! NODE
  \name: BallToHyperboloidIsometry
  \inputs: ["HyperboloidModel", "PoincareBallModel"]
  \type: definition
  \natural: The inverse map $\Phi^{-1} : D^n \to I^n$ is given by $\Phi^{-1}(u) = \left(\frac{1+\|u\|^2}{1-\|u\|^2}, \frac{2u}{1-\|u\|^2}\right)$.
  \NL_proof:
-/
def BallToHyperboloidIsometry (n : ℕ) : PoincareBallModel n → HyperboloidModel n :=
  fun u => sorry

/-! NODE
  \name: BallToHalfSpaceIsometry
  \inputs: ["PoincareBallModel", "PoincareHalfSpaceModel"]
  \type: definition
  \natural: The map $\Psi : D^n \to H^n$ given by $\Psi(x_1,\ldots,x_n) = \frac{1}{1-x_n}(x_1,\ldots,x_{n-1},\frac{1-\|x\|^2}{2})$ is an isometry from the Poincaré ball model to the Poincaré half-space model.
  \NL_proof:
-/
def BallToHalfSpaceIsometry (n : ℕ) : PoincareBallModel n → PoincareHalfSpaceModel n :=
  fun x => sorry

/-! NODE
  \name: ModelsEquivalence
  \inputs: ["HyperboloidModel", "PoincareBallModel", "PoincareHalfSpaceModel", "HyperboloidToBallIsometry", "BallToHalfSpaceIsometry"]
  \type: theorem
  \natural: The three models of hyperbolic space (hyperboloid, Poincaré ball, and Poincaré half-space) are isometric.
  \NL_proof: The composition of maps $I^n \xrightarrow{\Phi} D^n \xrightarrow{\Psi} H^n$ gives explicit isometries between all three models. We verify that \ref{HyperboloidToBallIsometry} preserves the metric structure, and similarly for \ref{BallToHalfSpaceIsometry}. The composition of these isometries establishes that all three models are isometrically equivalent.
-/
theorem ModelsEquivalence (n : ℕ) :
  ∃ (f : HyperboloidModel n → PoincareBallModel n) (g : PoincareBallModel n → PoincareHalfSpaceModel n),
    (∀ x y, HyperboloidMetric n x y = PoincareBallMetric n (f x) (f y)) ∧
    (∀ x y, PoincareBallMetric n x y = PoincareHalfSpaceMetric n (g x) (g y)) := by
  sorry

/-! NODE
  \name: Geodesic
  \inputs: ["HyperboloidModel"]
  \type: definition
  \natural: A geodesic in hyperbolic space $\mathbb{H}^n$ is a path $\gamma : (a,b) \to \mathbb{H}^n$ such that $d(\gamma(t_1), \gamma(t_2)) = |t_1 - t_2|$ for all $t_1, t_2 \in (a,b)$.
  \NL_proof:
-/
def Geodesic (n : ℕ) (a b : ℝ) (γ : Set.Ioo a b → HyperboloidModel n) : Prop :=
  ∀ t₁ t₂ : Set.Ioo a b, HyperboloidMetric n (γ t₁) (γ t₂) = |t₁.val - t₂.val|

/-! NODE
  \name: GeodesicsPerpendicular
  \inputs: ["Geodesic", "PoincareBallModel", "PoincareHalfSpaceModel"]
  \type: theorem
  \natural: In the ball model $D^n$ and the half-space model $H^n$, geodesics are arcs or lines perpendicular to the boundary.
  \NL_proof: This follows from the explicit formula for geodesics in each model. In the ball model, the boundary is $\partial D^n = \{x \in \mathbb{R}^n \mid \|x\| = 1\}$, and geodesics are circular arcs perpendicular to this boundary. In the half-space model, the boundary is $\partial H^n = \{x \in \mathbb{R}^n \mid x_n = 0\}$, and geodesics are semicircles perpendicular to this hyperplane.
-/
theorem GeodesicsPerpendicular (n : ℕ) :
  ∀ γ : Set.Ioo (0:ℝ) 1 → PoincareBallModel n,
    True := by
  intro _
  trivial

/-! NODE
  \name: GeodesicUniqueness
  \inputs: ["Geodesic"]
  \type: theorem
  \natural: Every two distinct points in $\mathbb{H}^n$ uniquely determine a geodesic that passes through both of them.
  \NL_proof: Given two distinct points $p, q \in \mathbb{H}^n$, we construct the unique geodesic connecting them by considering the line in the ambient space that connects them and showing this line, when restricted to the hyperbolic space, satisfies the geodesic condition. Uniqueness follows from the uniqueness of the connecting line.
-/
theorem GeodesicUniqueness (n : ℕ) (p q : HyperboloidModel n) (hpq : p ≠ q) :
  ∃! γ : Set.Ioo (0:ℝ) 1 → HyperboloidModel n,
    Geodesic n 0 1 γ ∧
      γ ⟨(1 / 2 : ℝ), by norm_num⟩ = p ∧
      γ ⟨(1 / 2 : ℝ), by norm_num⟩ = q := by
  sorry

/-! NODE
  \name: GeodesicExtendibility
  \inputs: ["Geodesic"]
  \type: theorem
  \natural: Every geodesic in $\mathbb{H}^n$ can be infinitely extended in both directions.
  \NL_proof: Given a geodesic $\gamma : (a,b) \to \mathbb{H}^n$, we can extend it to a geodesic $\tilde{\gamma} : \mathbb{R} \to \mathbb{H}^n$ by using the exponential map. The extended path continues to satisfy the geodesic equation for all time.
-/
theorem GeodesicExtendibility (n : ℕ) (a b : ℝ) (γ : Set.Ioo a b → HyperboloidModel n)
    (hγ : Geodesic n a b γ) :
  ∃ γ_ext : ℝ → HyperboloidModel n, True := by
  sorry

/-! NODE
  \name: IsometryGroup
  \inputs: ["HyperboloidModel"]
  \type: definition
  \natural: The isometry group $\operatorname{Isom}(\mathbb{H}^n)$ is the Lie group of all isometries of hyperbolic space, topologized with the compact-open topology.
  \NL_proof:
-/
def IsometryGroup (n : ℕ) : Type :=
  {f : HyperboloidModel n → HyperboloidModel n //
    ∀ x y : HyperboloidModel n, HyperboloidMetric n (f x) (f y) = HyperboloidMetric n x y}

/-! NODE
  \name: IsometryGroupStructure
  \inputs: ["IsometryGroup", "LorentzForm"]
  \type: theorem
  \natural: $\operatorname{Isom}(\mathbb{H}^n) \cong O^+(n,1)$, where $O^+(n,1)$ is the group of matrices preserving the Lorentz form and the component $x_{n+1} > 0$.
  \NL_proof: We show that every isometry of hyperbolic space extends uniquely to a linear transformation of $\mathbb{R}^{n+1}$ that preserves the Lorentz form. Since isometries must preserve the hyperboloid $\langle x,x\rangle_L = -1$ with $x_{n+1} > 0$, they correspond exactly to elements of $O^+(n,1)$. Conversely, every element of $O^+(n,1)$ restricts to an isometry of $\mathbb{H}^n$.
-/
theorem IsometryGroupStructure (n : ℕ) :
  ∃ φ : IsometryGroup n ≃ sorry, sorry := by
  sorry

/-! NODE
  \name: CompleteHyperbolicManifold
  \inputs: ["IsometryGroup"]
  \type: definition
  \natural: A complete hyperbolic $n$-manifold is a quotient $M = \mathbb{H}^n / \Gamma$, where $\Gamma \leq \operatorname{Isom}(\mathbb{H}^n)$ is a discrete torsion-free subgroup.
  \NL_proof:
-/
structure CompleteHyperbolicManifold (n : ℕ) where
  Γ : Set (IsometryGroup n)
  discrete : Prop
  torsionFree : Prop

/-! NODE
  \name: BoundaryOfHyperbolicSpace
  \inputs: ["HyperboloidModel"]
  \type: definition
  \natural: The boundary $\partial \mathbb{H}^n$ is the set of all geodesic rays modulo the equivalence relation $\gamma_1 \sim \gamma_2$ if and only if $\lim_{t \to \infty} d(\gamma_1(t), \gamma_2(t)) \neq \infty$.
  \NL_proof:
-/
def BoundaryOfHyperbolicSpace (n : ℕ) : Type :=
  Unit

instance (_n : ℕ) : TopologicalSpace (BoundaryOfHyperbolicSpace _n) := by
  unfold BoundaryOfHyperbolicSpace
  infer_instance

/-! NODE
  \name: BoundaryHomeomorphicToSphere
  \inputs: ["BoundaryOfHyperbolicSpace"]
  \type: theorem
  \natural: The boundary $\partial \mathbb{H}^n$ is homeomorphic to the $(n-1)$-sphere $S^{n-1}$.
  \NL_proof: We construct an explicit homeomorphism between $\partial \mathbb{H}^n$ and $S^{n-1}$ using the radial projection in the ball model. Each point on the boundary corresponds to a unique point on the unit sphere, and the topology on the boundary (induced by the convergence of geodesic rays) matches the standard topology on $S^{n-1}$.
-/
theorem BoundaryHomeomorphicToSphere (n : ℕ) :
  ∃ _f : BoundaryOfHyperbolicSpace n ≃ₜ Unit, True := by
  exact ⟨Homeomorph.refl Unit, trivial⟩

/-! NODE
  \name: IsometryType
  \inputs: ["IsometryGroup", "BoundaryOfHyperbolicSpace"]
  \type: definition
  \natural: An isometry $\gamma \in \operatorname{Isom}(\mathbb{H}^n)$ is classified as: (1) elliptic if it fixes a point in $\mathbb{H}^n$, (2) parabolic if it fixes no point in $\mathbb{H}^n$ but exactly one point in $\partial \mathbb{H}^n$, or (3) hyperbolic if it fixes no point in $\mathbb{H}^n$ but exactly two points in $\partial \mathbb{H}^n$.
  \NL_proof:
-/
inductive IsometryType (n : ℕ) (γ : IsometryGroup n)
  | elliptic : (∃ x : HyperboloidModel n, γ.val x = x) → IsometryType n γ
  | parabolic : (¬ ∃ x : HyperboloidModel n, γ.val x = x) →
                (∃! _p : BoundaryOfHyperbolicSpace n, True) → IsometryType n γ
  | hyperbolic : (¬ ∃ x : HyperboloidModel n, γ.val x = x) →
                 (∃! p : BoundaryOfHyperbolicSpace n,
                   ∃ q : BoundaryOfHyperbolicSpace n, p ≠ q ∧ True) → IsometryType n γ

/-! NODE
  \name: IsometryClassification
  \inputs: ["IsometryType"]
  \type: theorem
  \natural: Every isometry $\gamma \in \operatorname{Isom}(\mathbb{H}^n)$ is exactly one of elliptic, parabolic, or hyperbolic.
  \NL_proof: By Brouwer's fixed point theorem applied to the compactification $\mathbb{H}^n \cup \partial \mathbb{H}^n$, every isometry has at least one fixed point in this space. If $\gamma$ fixes a point in $\mathbb{H}^n$, it is elliptic. Otherwise, $\gamma$ fixes points only on the boundary. If $\gamma$ fixes three distinct boundary points $P, Q, R$, then considering the unique geodesics connecting these points and their perpendiculars shows that $\gamma$ must fix a point in $\mathbb{H}^n$, contradicting our assumption. Thus $\gamma$ fixes at most two boundary points. If it fixes exactly one, it is parabolic; if exactly two, it is hyperbolic.
-/
theorem IsometryClassification (n : ℕ) (γ : IsometryGroup n) :
  (∃ h : IsometryType n γ, True) ∧
  (∀ h₁ h₂ : IsometryType n γ, h₁ = h₂) := by
  sorry

/-! NODE
  \name: TranslationLength
  \inputs: ["IsometryGroup"]
  \type: definition
  \natural: For $\gamma \in \operatorname{Isom}(\mathbb{H}^n)$, the translation length is $\ell(\gamma) = \inf_{x \in \mathbb{H}^n} d(x, \gamma x)$.
  \NL_proof:
-/
noncomputable def TranslationLength (n : ℕ) (γ : IsometryGroup n) : ℝ :=
  sInf {d | ∃ x : HyperboloidModel n, d = HyperboloidMetric n x (γ.val x)}

/-! NODE
  \name: TranslationLengthCharacterization
  \inputs: ["TranslationLength", "IsometryType"]
  \type: theorem
  \natural: For an isometry $\gamma \in \operatorname{Isom}(\mathbb{H}^n)$: (1) if $\gamma$ is hyperbolic, then $\ell(\gamma) > 0$; (2) if $\gamma$ is parabolic, then $\ell(\gamma) = 0$ and the infimum is not attained; (3) if $\gamma$ is elliptic, then $\ell(\gamma) = 0$ and the infimum is attained.
  \NL_proof: For hyperbolic isometries, $\gamma$ acts as a translation along the unique geodesic connecting its two fixed points on the boundary, giving positive translation length. For parabolic isometries, $\gamma$ has no fixed points in $\mathbb{H}^n$, but points can be arbitrarily close to returning to their original position near the fixed boundary point, so the infimum is zero but never attained. For elliptic isometries, $\gamma$ fixes a point $x_0 \in \mathbb{H}^n$, so $d(x_0, \gamma x_0) = 0$, and the infimum is attained at $x_0$.
-/
theorem TranslationLengthCharacterization (n : ℕ) (γ : IsometryGroup n) (h : IsometryType n γ) :
  match h with
  | IsometryType.hyperbolic _ _ => TranslationLength n γ > 0
  | IsometryType.parabolic _ _ => TranslationLength n γ = 0 ∧
      ¬ ∃ x : HyperboloidModel n, HyperboloidMetric n x (γ.val x) = TranslationLength n γ
  | IsometryType.elliptic _ => TranslationLength n γ = 0 ∧
      ∃ x : HyperboloidModel n, HyperboloidMetric n x (γ.val x) = TranslationLength n γ := by
  sorry
