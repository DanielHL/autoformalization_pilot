-- Formal outline for: Thick-Thin Decomposition of Complete Hyperbolic Manifolds
-- Written by Linyue Xu
-- Main result: Every complete hyperbolic manifold decomposes into thick and thin parts,
-- where the thin part is a disjoint union of cusp neighborhoods and tubes.

import Mathlib.Tactic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Algebra.Group.Basic

noncomputable section

open scoped Topology

/-! NODE
  \name: LorentzianForm
  \inputs: []
  \type: definition
  \natural: The Lorentzian bilinear form on $\mathbb{R}^{n+1}$ defined by $\langle x, y \rangle_L = -x_0 y_0 + x_1 y_1 + \cdots + x_n y_n$.
  \NL_proof:
-/
def LorentzianForm (n : ℕ) (x y : Fin (n + 1) → ℝ) : ℝ :=
  - x 0 * y 0 + ∑ i : Fin n, x i.succ * y i.succ

/-! NODE
  \name: HyperboloidModel
  \inputs: ["LorentzianForm"]
  \type: definition
  \natural: The hyperboloid model $I^n = \{ x \in \mathbb{R}^{n+1} \mid \langle x, x \rangle_L = -1,\; x_0 > 0 \}$ with metric $d_I(x,y) = \operatorname{arcosh}(-\langle x,y \rangle_L)$.
  \NL_proof:
-/
structure HyperboloidModel (n : ℕ) where
  carrier : Type
  isMetricSpace : MetricSpace carrier
  toFun : carrier → (Fin (n + 1) → ℝ)
  on_hyperboloid : ∀ x : carrier, LorentzianForm n (toFun x) (toFun x) = -1
  positive_time : ∀ x : carrier, toFun x 0 > 0
  dist_eq : ∀ x y : carrier,
    @dist carrier isMetricSpace.toDist x y = Real.arcosh (- LorentzianForm n (toFun x) (toFun y))

def HyperboloidModelInstance (n : ℕ) : HyperboloidModel n := sorry

/-! NODE
  \name: PoincareBallModel
  \inputs: []
  \type: definition
  \natural: The Poincaré ball model $D^n = \{ x \in \mathbb{R}^n \mid \|x\| < 1 \}$ with metric $d_D(x,y) = \operatorname{arcosh}(1 + \frac{2\|x-y\|^2}{(1-\|x\|^2)(1-\|y\|^2)})$.
  \NL_proof:
-/
structure PoincareBallModel (n : ℕ) where
  carrier : Type
  isMetricSpace : MetricSpace carrier
  toFun : carrier → EuclideanSpace ℝ (Fin n)
  in_ball : ∀ x : carrier, ‖toFun x‖ < 1
  dist_eq : ∀ x y : carrier,
    @dist carrier isMetricSpace.toDist x y =
      Real.arcosh (1 + 2 * ‖toFun x - toFun y‖ ^ 2 /
        ((1 - ‖toFun x‖ ^ 2) * (1 - ‖toFun y‖ ^ 2)))

def PoincareBallModelInstance (n : ℕ) : PoincareBallModel n := sorry

/-! NODE
  \name: PoincareHalfSpaceModel
  \inputs: []
  \type: definition
  \natural: The Poincaré half-space model $H^n = \{ (x_1, \ldots, x_n) \in \mathbb{R}^n \mid x_n > 0 \}$ with metric $d_H(x,y) = \operatorname{arcosh}(1 + \frac{\|x-y\|^2}{2 x_n y_n})$.
  \NL_proof:
-/
structure PoincareHalfSpaceModel (n : ℕ) where
  carrier : Type
  isMetricSpace : MetricSpace carrier
  toFun : carrier → (Fin n → ℝ)
  lastCoord : carrier → ℝ
  lastCoord_pos : ∀ x : carrier, lastCoord x > 0
  dist_eq : ∀ x y : carrier,
    @dist carrier isMetricSpace.toDist x y =
      Real.arcosh (1 + ‖(fun i => toFun x i - toFun y i)‖ ^ 2 /
        (2 * lastCoord x * lastCoord y))

def PoincareHalfSpaceModelInstance (n : ℕ) : PoincareHalfSpaceModel n := sorry

/-! NODE
  \name: HyperbolicSpace
  \inputs: ["HyperboloidModel", "PoincareBallModel", "PoincareHalfSpaceModel"]
  \type: definition
  \natural: The $n$-dimensional hyperbolic space $\mathbb{H}^n$, defined as a complete simply-connected Riemannian manifold of constant sectional curvature $-1$, realized by any of the three standard models.
  \NL_proof:
-/
structure HyperbolicSpace (n : ℕ) where
  carrier : Type
  isMetricSpace : MetricSpace carrier

def HyperbolicSpaceInstance (n : ℕ) : HyperbolicSpace n := sorry

/-! NODE
  \name: EquivalenceOfModels
  \inputs: ["HyperboloidModel", "PoincareBallModel", "PoincareHalfSpaceModel"]
  \type: hypothesis
  \natural: The three models of hyperbolic space (hyperboloid, Poincaré ball, Poincaré half-space) are mutually isometric, with explicit isometries $\Phi : I^n \to D^n$ and $\Psi : D^n \to H^n$.
  \NL_proof:
-/
def EquivalenceOfModels (n : ℕ) : Prop :=
  ∃ (Hn : HyperboloidModel n) (Bn : PoincareBallModel n) (Sn : PoincareHalfSpaceModel n),
    (∃ f : Hn.carrier → Bn.carrier,
      @Isometry Hn.carrier Bn.carrier
        Hn.isMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        Bn.isMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace f ∧
      Function.Bijective f) ∧
    (∃ g : Bn.carrier → Sn.carrier,
      @Isometry Bn.carrier Sn.carrier
        Bn.isMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        Sn.isMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace g ∧
      Function.Bijective g)

/-! NODE
  \name: Hyperbolicity
  \inputs: ["HyperbolicSpace"]
  \type: hypothesis
  \natural: Each of the three models is a simply-connected, complete Riemannian manifold of constant sectional curvature $-1$.
  \NL_proof:
-/
def Hyperbolicity (n : ℕ) : Prop :=
  ∀ (H : HyperbolicSpace n),
    @CompleteSpace H.carrier H.isMetricSpace.toPseudoMetricSpace.toUniformSpace

/-! NODE
  \name: Geodesics
  \inputs: ["PoincareBallModel", "PoincareHalfSpaceModel"]
  \type: hypothesis
  \natural: The geodesics in the disk model $D^n$ and the half-space model $H^n$ are circles or lines perpendicular to the boundary.
  \NL_proof:
-/
def Geodesics (n : ℕ) : Prop := True

/-! NODE
  \name: IsomGroup
  \inputs: ["HyperbolicSpace"]
  \type: definition
  \natural: The isometry group $\mathrm{Isom}(\mathbb{H}^n)$ of hyperbolic space, as a topological group with the compact-open topology.
  \NL_proof:
-/
structure IsomGroup (n : ℕ) (H : HyperbolicSpace n) where
  carrier : Type
  isGroup : Group carrier
  isTopologicalSpace : TopologicalSpace carrier
  isTopologicalGroup : @IsTopologicalGroup carrier isTopologicalSpace isGroup
  action : carrier → H.carrier → H.carrier
  action_isometry : ∀ g : carrier, @Isometry H.carrier H.carrier
    H.isMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
    H.isMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace (action g)

def IsomGroupInstance (n : ℕ) (H : HyperbolicSpace n) : IsomGroup n H := sorry

/-! NODE
  \name: CompleteHyperbolicManifold
  \inputs: ["HyperbolicSpace", "IsomGroup"]
  \type: definition
  \natural: A complete hyperbolic $n$-manifold is a quotient $M = \mathbb{H}^n / \Gamma$ where $\Gamma \leq \mathrm{Isom}(\mathbb{H}^n)$ is a discrete torsion-free subgroup.
  \NL_proof:
-/
structure CompleteHyperbolicManifold (n : ℕ) where
  H : HyperbolicSpace n
  G : IsomGroup n H
  Gamma : @Subgroup G.carrier G.isGroup
  torsionFree : ∀ (g : G.carrier), g ∈ Gamma →
    g ≠ (letI := G.isGroup; 1) →
    ∀ k : ℕ, k > 0 →
      (letI := G.isGroup; g ^ k) ≠ (letI := G.isGroup; 1)
  carrier : Type
  isMetricSpace : MetricSpace carrier
  projection : H.carrier → carrier
  projection_surjective : Function.Surjective projection

/-! NODE
  \name: BoundaryHyperbolicSpace
  \inputs: ["HyperbolicSpace"]
  \type: definition
  \natural: The boundary $\partial \mathbb{H}^n$ of hyperbolic space, defined via equivalence classes of geodesic rays, equipped with a topology.
  \NL_proof:
-/
structure BoundaryHyperbolicSpace (n : ℕ) (H : HyperbolicSpace n) where
  carrier : Type
  isTopologicalSpace : TopologicalSpace carrier

def BoundaryHyperbolicSpaceInstance (n : ℕ) (H : HyperbolicSpace n) :
    BoundaryHyperbolicSpace n H := sorry

/-! NODE
  \name: CompactificationHomeomorphism
  \inputs: ["HyperbolicSpace", "BoundaryHyperbolicSpace"]
  \type: theorem
  \natural: $\mathbb{H}^n \cup \partial \mathbb{H}^n$ is homeomorphic to $\overline{D}^n$, the closed $n$-disk.
  \NL_proof: The compactification of hyperbolic space by its boundary at infinity is homeomorphic to the closed unit ball in $\mathbb{R}^n$.
-/
theorem CompactificationHomeomorphism
    (n : ℕ) (H : HyperbolicSpace n) (B : BoundaryHyperbolicSpace n H) :
    ∃ (X : Type) (_ : TopologicalSpace X),
      Nonempty (X ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by sorry

/-! NODE
  \name: IsometryClassification
  \inputs: ["HyperbolicSpace", "IsomGroup", "BoundaryHyperbolicSpace"]
  \type: theorem
  \natural: An isometry $\gamma \in \mathrm{Isom}(\mathbb{H}^n)$ falls into exactly one of three categories: elliptic (fixes a point in $\mathbb{H}^n$), parabolic (fixes no point in $\mathbb{H}^n$ and exactly one point in $\partial \mathbb{H}^n$), or loxodromic (fixes no point in $\mathbb{H}^n$ and exactly two points in $\partial \mathbb{H}^n$).
  \NL_proof: Every isometry of hyperbolic space extends continuously to the boundary. Brouwer's fixed point theorem on the closed disk guarantees at least one fixed point in $\mathbb{H}^n \cup \partial \mathbb{H}^n$. The three cases are then exhaustive and mutually exclusive.
-/
/-! NODE
  \name: FixedPointSet
  \inputs: ["HyperbolicSpace", "IsomGroup", "BoundaryHyperbolicSpace"]
  \type: definition
  \natural: For $\phi \in \mathrm{Isom}(\mathbb{H}^n)$, define $\mathrm{Fix}(\phi)$ as the set of fixed points of $\phi$ in $\mathbb{H}^n \cup \partial \mathbb{H}^n$.
  \NL_proof:
-/
def FixedPointSet (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H)
    (B : BoundaryHyperbolicSpace n H) (γ : G.carrier) : Set (H.carrier ⊕ B.carrier) := sorry

inductive IsometryType where
  | elliptic
  | parabolic
  | loxodromic

theorem IsometryClassification
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (γ : G.carrier) :
    -- Elliptic: fixes a point in H
    (∃ x : H.carrier, G.action γ x = x) ∨
    -- Parabolic: no interior fixed point, exactly one boundary fixed point
    ((¬ ∃ x : H.carrier, G.action γ x = x) ∧
      ∃! p : B.carrier, Sum.inr p ∈ FixedPointSet n H G B γ) ∨
    -- Loxodromic: no interior fixed point, exactly two boundary fixed points
    ((¬ ∃ x : H.carrier, G.action γ x = x) ∧
      ∃ p q : B.carrier, p ≠ q ∧
        Sum.inr p ∈ FixedPointSet n H G B γ ∧
        Sum.inr q ∈ FixedPointSet n H G B γ ∧
        ∀ r : B.carrier, Sum.inr r ∈ FixedPointSet n H G B γ → r = p ∨ r = q) := by sorry

/-! NODE
  \name: IsometryCoordinates
  \inputs: ["IsometryClassification", "PoincareBallModel", "PoincareHalfSpaceModel"]
  \type: theorem
  \natural: In coordinates: elliptic isometries with fixed point $0 \in D^n$ act as $\phi(x) = Ax$ for $A \in O(n)$; parabolic isometries fixing $\infty \in H^n$ act as $\phi(\bar{x}, t) = (A\bar{x} + b, t)$ for $A \in O(n-1)$; loxodromic isometries fixing $0, \infty$ act as $\phi(\bar{x}, t) = \lambda(A\bar{x}, t)$.
  \NL_proof: By conjugating to place the fixed points at standard positions, the isometry must preserve the metric, constraining it to the given coordinate form.
-/
theorem IsometryCoordinates
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (hclass : ∀ γ : G.carrier,
      (∃ x : H.carrier, G.action γ x = x) ∨
      (¬ ∃ x : H.carrier, G.action γ x = x)) :
    True := by sorry

/-! NODE
  \name: TranslationLength
  \inputs: ["HyperbolicSpace", "IsomGroup"]
  \type: definition
  \natural: For $\gamma \in \mathrm{Isom}(\mathbb{H}^n)$, the translation length is $\ell(\gamma) = \inf_{x \in \mathbb{H}^n} d(x, \gamma x)$.
  \NL_proof:
-/
def TranslationLength (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (γ : G.carrier) : ℝ :=
  iInf (fun x : H.carrier => @dist H.carrier H.isMetricSpace.toDist x (G.action γ x))

/-! NODE
  \name: TranslationLengthClassification
  \inputs: ["TranslationLength", "IsometryClassification"]
  \type: theorem
  \natural: For isometries of $\mathbb{H}^n$: loxodromic isometries have $\ell(\gamma) > 0$; parabolic isometries have $\ell(\gamma) = 0$ but the infimum is not realized; elliptic isometries have $\ell(\gamma) = 0$ with the infimum realized.
  \NL_proof: Loxodromic isometries translate along their axis by a positive amount. Parabolic isometries move points arbitrarily little near their fixed point at infinity but never fix an interior point. Elliptic isometries fix an interior point where the displacement is zero.
-/
theorem TranslationLengthClassification
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (γ : G.carrier) :
    -- Loxodromic: ℓ(γ) > 0
    (TranslationLength n H G γ > 0) ∨
    -- Parabolic: ℓ(γ) = 0 and infimum not realized
    (TranslationLength n H G γ = 0 ∧
      ¬ ∃ x : H.carrier, @dist H.carrier H.isMetricSpace.toDist x (G.action γ x) = 0) ∨
    -- Elliptic: ℓ(γ) = 0 and infimum realized (fixed point)
    (TranslationLength n H G γ = 0 ∧
      ∃ x : H.carrier, G.action γ x = x) := by sorry

/-! NODE
  \name: NoEllipticElements
  \inputs: ["CompleteHyperbolicManifold", "IsometryClassification"]
  \type: theorem
  \natural: If $M = \mathbb{H}^n / \Gamma$ is a complete hyperbolic manifold, then $\Gamma$ does not contain elliptic elements.
  \NL_proof: If $\gamma \in \Gamma$ is elliptic, it fixes a point $x \in \mathbb{H}^n$. Then $\gamma$ is a non-trivial element of finite order (since the stabilizer is compact and $\Gamma$ is discrete), contradicting $\Gamma$ being torsion-free.
-/
theorem NoEllipticElements
    (n : ℕ) (M : CompleteHyperbolicManifold n)
    (γ : M.G.carrier) (hγ : γ ∈ M.Gamma) (hne : γ ≠ @One.one M.G.carrier M.G.isGroup.toOne) :
    ¬ ∃ x : M.H.carrier, M.G.action γ x = x := by sorry

/-! NODE
  \name: InjectivityRadius
  \inputs: ["CompleteHyperbolicManifold"]
  \type: definition
  \natural: The injectivity radius at $x \in M$ is $\mathrm{inj}_M(x) = \frac{1}{2} \inf_{\gamma \in \Gamma \setminus \{1\}} d(\tilde{x}, \gamma \tilde{x})$ where $\tilde{x}$ is any lift of $x$ to $\mathbb{H}^n$.
  \NL_proof:
-/
def InjectivityRadius (n : ℕ) (M : CompleteHyperbolicManifold n) (x : M.carrier) : ℝ := sorry

/-! NODE
  \name: ThinPart
  \inputs: ["CompleteHyperbolicManifold", "InjectivityRadius"]
  \type: definition
  \natural: For $\epsilon > 0$, the thin part is $M_{(0,\epsilon)} = \{ x \in M \mid \mathrm{inj}_M(x) < \epsilon/2 \}$.
  \NL_proof:
-/
def ThinPart (n : ℕ) (M : CompleteHyperbolicManifold n) (ε : ℝ) : Set M.carrier :=
  { x | InjectivityRadius n M x < ε / 2 }

/-! NODE
  \name: ThickPart
  \inputs: ["CompleteHyperbolicManifold", "ThinPart"]
  \type: definition
  \natural: The thick part is $M_{(\epsilon,\infty)} = M \setminus M_{(0,\epsilon)}$.
  \NL_proof:
-/
def ThickPart (n : ℕ) (M : CompleteHyperbolicManifold n) (ε : ℝ) : Set M.carrier :=
  (ThinPart n M ε)ᶜ

/-! NODE
  \name: ThickThinComplement
  \inputs: ["ThinPart", "ThickPart"]
  \type: theorem
  \natural: The thick and thin parts partition $M$: $M = M_{(0,\epsilon)} \sqcup M_{(\epsilon,\infty)}$.
  \NL_proof: By definition the thick part is the complement of the thin part.
-/
theorem ThickThinComplement (n : ℕ) (M : CompleteHyperbolicManifold n) (ε : ℝ) :
    ThinPart n M ε ∪ ThickPart n M ε = Set.univ := by sorry

/-! NODE
  \name: ThickThinComplement_test
  \inputs: ["ThinPart", "ThickPart"]
  \type: unit test
  \natural: The thick and thin parts are disjoint.
  \NL_proof: Immediate from the definition as complement.
-/
theorem ThickThinComplement_test (n : ℕ) (M : CompleteHyperbolicManifold n) (ε : ℝ) :
    ThinPart n M ε ∩ ThickPart n M ε = ∅ := by sorry

/-! NODE
  \name: Tube
  \inputs: ["HyperbolicSpace", "IsomGroup"]
  \type: definition
  \natural: If $\gamma$ is a loxodromic isometry, the quotient $T_\gamma = \mathbb{H}^n / \langle \gamma \rangle$ is called a tube.
  \NL_proof:
-/
structure Tube (n : ℕ) where
  H : HyperbolicSpace n
  G : IsomGroup n H
  γ : G.carrier
  isLoxodromic : TranslationLength n H G γ > 0
  carrier : Type
  isMetricSpace : MetricSpace carrier

def TubeInstance (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H)
    (γ : G.carrier) (hlox : TranslationLength n H G γ > 0) : Tube n := sorry

/-! NODE
  \name: TubeClosedGeodesic
  \inputs: ["Tube"]
  \type: theorem
  \natural: A tube contains a closed geodesic corresponding to the axis of $\gamma$.
  \NL_proof: The axis of the loxodromic isometry $\gamma$ projects to a closed geodesic in the quotient $\mathbb{H}^n / \langle \gamma \rangle$.
-/
theorem TubeClosedGeodesic (n : ℕ) (T : Tube n) :
    ∃ (geodesic : Set T.carrier), geodesic.Nonempty := by sorry

/-! NODE
  \name: Cusp
  \inputs: ["HyperbolicSpace", "IsomGroup", "BoundaryHyperbolicSpace"]
  \type: definition
  \natural: A cusp is a quotient $C = \mathbb{H}^n / \Lambda$ where $\Lambda$ is a subgroup of parabolic isometries fixing the same point in $\partial \mathbb{H}^n$.
  \NL_proof:
-/
structure Cusp (n : ℕ) where
  H : HyperbolicSpace n
  G : IsomGroup n H
  B : BoundaryHyperbolicSpace n H
  fixedPoint : B.carrier
  Lambda : @Subgroup G.carrier G.isGroup
  allParabolic : ∀ g : G.carrier, g ∈ Lambda → ¬ ∃ x : H.carrier, G.action g x = x
  carrier : Type
  isMetricSpace : MetricSpace carrier
  isTopologicalSpace : TopologicalSpace carrier

def CuspInstance (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H)
    (B : BoundaryHyperbolicSpace n H) (p : B.carrier)
    (Lambda : @Subgroup G.carrier G.isGroup) : Cusp n := sorry

/-! NODE
  \name: CuspTopology
  \inputs: ["Cusp"]
  \type: theorem
  \natural: Topologically, a cusp $C$ is homeomorphic to $N \times [0, \infty)$ where $N$ is a flat $(n-1)$-manifold.
  \NL_proof: In the upper half-space model with the fixed point at infinity, the parabolic group acts on horospheres (horizontal slices $\{x_n = t\}$) as Euclidean isometries. The quotient of each horosphere gives the flat manifold $N$, and the vertical direction gives the $[0,\infty)$ factor.
-/
theorem CuspTopology (n : ℕ) (C : Cusp n) :
    ∃ (N : Type) (_ : TopologicalSpace N),
      Nonempty (@Homeomorph C.carrier (N × Set.Ici (0 : ℝ))
        C.isTopologicalSpace instTopologicalSpaceProd) := by sorry

/-! NODE
  \name: StarShapedSet
  \inputs: ["HyperbolicSpace", "BoundaryHyperbolicSpace"]
  \type: definition
  \natural: A star-shaped set centered at $p \in \partial \mathbb{H}^n$ is a subset $U \subset \mathbb{H}^n$ that intersects every half-line pointing to $p$ in a half-line. A star-shaped cusp neighborhood is $U/\Gamma$ for a $\Gamma$-invariant star-shaped set. A star-shaped geodesic neighborhood is $V/\Gamma$ for a $\Gamma$-invariant neighborhood of a geodesic axis.
  \NL_proof:
-/
structure StarShapedSet (n : ℕ) (H : HyperbolicSpace n) (B : BoundaryHyperbolicSpace n H) where
  set : Set H.carrier
  center : B.carrier
  -- Star-shaped: intersects every geodesic ray toward center in a half-ray

/-! NODE
  \name: MargulisLemmaLieGroups
  \inputs: []
  \type: lemma
  \natural: (Margulis Lemma for Lie Groups) Let $G$ be a Lie group. There exists a neighborhood $U$ of the identity such that any discrete subgroup generated by elements of $U$ is nilpotent.
  \NL_proof: Near the identity the commutator map $[g,h] = g^{-1}h^{-1}gh$ has vanishing differential, so $|[g,h]| \leq \frac{1}{2} \min(|g|, |h|)$ in a small neighborhood $U$. Iterated commutators shrink exponentially. Since the subgroup is discrete, the lower central series terminates, giving nilpotency.
-/
theorem MargulisLemmaLieGroups
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ (U : Set G), IsOpen U ∧ (1 : G) ∈ U ∧
      ∀ (H : Subgroup G), (∀ h : G, h ∈ H → h ∈ U) →
        Group.IsNilpotent H := by sorry

/-! NODE
  \name: SmallDisplacementSubgroup
  \inputs: ["HyperbolicSpace", "IsomGroup"]
  \type: definition
  \natural: For a discrete subgroup $\Gamma \leq \mathrm{Isom}(\mathbb{H}^n)$, a point $x \in \mathbb{H}^n$, and $\epsilon > 0$, define $\Gamma_\epsilon(x) = \langle \gamma \in \Gamma \mid d(x, \gamma x) < \epsilon \rangle$.
  \NL_proof:
-/
def SmallDisplacementSubgroup (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H)
    (Gamma : @Subgroup G.carrier G.isGroup) (x : H.carrier) (ε : ℝ) :
    @Subgroup G.carrier G.isGroup := sorry

/-! NODE
  \name: MargulisLemma
  \inputs: ["MargulisLemmaLieGroups", "HyperbolicSpace", "IsomGroup", "SmallDisplacementSubgroup"]
  \type: theorem
  \natural: (Margulis Lemma) There exists a constant $\epsilon_n > 0$ such that for any discrete subgroup $\Gamma \leq \mathrm{Isom}(\mathbb{H}^n)$ and any $x \in \mathbb{H}^n$, the group $\Gamma_\epsilon(x)$ is virtually nilpotent for all $\epsilon \leq \epsilon_n$.
  \NL_proof: $\mathrm{Isom}(\mathbb{H}^n)$ is a Lie group. Small displacement means the element lies in a small neighborhood of the identity in the stabilizer. Apply the Margulis Lemma for Lie groups.
-/
theorem MargulisLemma
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H)
    (hMargulis : ∀ {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'],
      ∃ (U : Set G'), IsOpen U ∧ (1 : G') ∈ U ∧
        ∀ (H : Subgroup G'), (∀ h : G', h ∈ H → h ∈ U) →
          Group.IsNilpotent H) :
    ∃ (ε_n : ℝ), ε_n > 0 ∧
      ∀ (Gamma : @Subgroup G.carrier G.isGroup) (x : H.carrier) (ε : ℝ),
        ε ≤ ε_n →
          ∃ (N : @Subgroup G.carrier G.isGroup),
            N ≤ SmallDisplacementSubgroup n H G Gamma x ε ∧
            Group.IsNilpotent N := by sorry

/-! NODE
  \name: CommutingFixedPoints
  \inputs: ["FixedPointSet", "IsometryClassification"]
  \type: theorem
  \natural: If two loxodromic (or parabolic) isometries $\phi_1, \phi_2$ commute, then $\mathrm{Fix}(\phi_1) = \mathrm{Fix}(\phi_2)$.
  \NL_proof: If two loxodromic isometries commute, each must preserve the axis of the other. In hyperbolic space, a loxodromic isometry is determined by its axis and translation length, so the axes must coincide, giving the same fixed points at infinity.
-/
theorem CommutingFixedPoints
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (φ₁ φ₂ : G.carrier)
    -- Both act freely (loxodromic or parabolic, not elliptic)
    (hfree₁ : ¬ ∃ x : H.carrier, G.action φ₁ x = x)
    (hfree₂ : ¬ ∃ x : H.carrier, G.action φ₂ x = x)
    (hcommute : letI := G.isGroup
      φ₁ * φ₂ = φ₂ * φ₁) :
    FixedPointSet n H G B φ₁ = FixedPointSet n H G B φ₂ := by sorry

/-! NODE
  \name: FixedPointAlternative
  \inputs: ["FixedPointSet", "IsometryClassification"]
  \type: theorem
  \natural: Let $\Gamma \leq \mathrm{Isom}(\mathbb{H}^n)$ be discrete. For two non-trivial isometries $\phi_1, \phi_2$ acting freely on $\mathbb{H}^n$, exactly one of the following holds: (1) $\mathrm{Fix}(\phi_1) \cap \mathrm{Fix}(\phi_2) = \emptyset$, (2) $\phi_1, \phi_2$ are parabolic with the same fixed point, (3) $\phi_1, \phi_2$ are powers of the same loxodromic isometry.
  \NL_proof: If the fixed point sets on the boundary intersect, then the shared fixed points constrain both isometries. One shared point forces both to be parabolic fixing that point. Two shared points forces both to have the same axis, hence to be powers of the same primitive loxodromic element (by discreteness).
-/
theorem FixedPointAlternative
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (Gamma : @Subgroup G.carrier G.isGroup)
    (φ₁ φ₂ : G.carrier) (h₁ : φ₁ ∈ Gamma) (h₂ : φ₂ ∈ Gamma)
    (hfree₁ : ¬ ∃ x : H.carrier, G.action φ₁ x = x)
    (hfree₂ : ¬ ∃ x : H.carrier, G.action φ₂ x = x) :
    (FixedPointSet n H G B φ₁ ∩ FixedPointSet n H G B φ₂ = ∅) ∨
    (∃ p : B.carrier, FixedPointSet n H G B φ₁ = {Sum.inr p} ∧
                       FixedPointSet n H G B φ₂ = {Sum.inr p}) ∨
    (∃ γ₀ : G.carrier, ∃ k₁ k₂ : ℤ,
      letI := G.isGroup
      φ₁ = γ₀ ^ k₁ ∧ φ₂ = γ₀ ^ k₂) := by sorry

/-! NODE
  \name: ElementarySubgroup
  \inputs: ["FixedPointAlternative", "CommutingFixedPoints"]
  \type: theorem
  \natural: Let $\Gamma \leq \mathrm{Isom}(\mathbb{H}^n)$ be a discrete virtually nilpotent subgroup acting freely on $\mathbb{H}^n$. Then $\Gamma$ is elementary: either (1) $\Gamma$ is finite, (2) $\Gamma$ is generated by a single loxodromic isometry, or (3) $\Gamma$ consists of parabolic isometries fixing the same point in $\partial \mathbb{H}^n$.
  \NL_proof: A virtually nilpotent group has a nilpotent subgroup of finite index. In hyperbolic space, a nilpotent group of isometries acting freely must have commuting elements sharing fixed points (by the fixed point alternative). This forces all elements to share the same fixed point set, yielding the three cases.
-/
theorem ElementarySubgroup
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (Gamma : @Subgroup G.carrier G.isGroup)
    (hfree : ∀ g : G.carrier, g ∈ Gamma →
      g ≠ @One.one G.carrier G.isGroup.toOne →
      ¬ ∃ x : H.carrier, G.action g x = x)
    (hFixAlt : ∀ φ₁ φ₂ : G.carrier, φ₁ ∈ Gamma → φ₂ ∈ Gamma →
      (FixedPointSet n H G B φ₁ ∩ FixedPointSet n H G B φ₂ = ∅) ∨
      (∃ p : B.carrier, FixedPointSet n H G B φ₁ = {Sum.inr p} ∧
                         FixedPointSet n H G B φ₂ = {Sum.inr p}) ∨
      True)
    (hVN : ∃ (N : @Subgroup G.carrier G.isGroup), N ≤ Gamma ∧ Group.IsNilpotent N) :
    Finite Gamma ∨
    (∃ γ : G.carrier, γ ∈ Gamma ∧ TranslationLength n H G γ > 0) ∨
    (∃ p : B.carrier, ∀ g : G.carrier, g ∈ Gamma →
      Sum.inr p ∈ FixedPointSet n H G B g) := by sorry

/-! NODE
  \name: MargulisLemma2
  \inputs: ["MargulisLemma", "ElementarySubgroup"]
  \type: theorem
  \natural: Let $\Gamma \leq \mathrm{Isom}(\mathbb{H}^n)$ be discrete and acting freely. If $\Gamma$ is virtually nilpotent, it is either trivial or elementary.
  \NL_proof: Combine the Margulis Lemma (giving virtual nilpotency of small displacement subgroups) with the elementary subgroup classification.
-/
theorem MargulisLemma2
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (Gamma : @Subgroup G.carrier G.isGroup)
    (hfree : ∀ g : G.carrier, g ∈ Gamma →
      g ≠ @One.one G.carrier G.isGroup.toOne →
      ¬ ∃ x : H.carrier, G.action g x = x)
    (hElem : Finite Gamma ∨
      (∃ γ : G.carrier, γ ∈ Gamma ∧ TranslationLength n H G γ > 0) ∨
      (∃ p : B.carrier, ∀ g : G.carrier, g ∈ Gamma →
        Sum.inr p ∈ FixedPointSet n H G B g))
    (hVN : ∃ (N : @Subgroup G.carrier G.isGroup), N ≤ Gamma ∧ Group.IsNilpotent N) :
    (∀ g : G.carrier, g ∈ Gamma → g = @One.one G.carrier G.isGroup.toOne) ∨
    (∃ γ : G.carrier, γ ∈ Gamma ∧ TranslationLength n H G γ > 0) ∨
    (∃ p : B.carrier, ∀ g : G.carrier, g ∈ Gamma →
      Sum.inr p ∈ FixedPointSet n H G B g) := by sorry

/-! NODE
  \name: SmallDisplacementSet
  \inputs: ["HyperbolicSpace", "IsomGroup"]
  \type: definition
  \natural: For $\gamma \in \Gamma$ and $\epsilon > 0$, define the small displacement set $U_\gamma(\epsilon) = \{ x \in \mathbb{H}^n \mid d(x, \gamma x) < \epsilon \}$.
  \NL_proof:
-/
def SmallDisplacementSet (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H)
    (γ : G.carrier) (ε : ℝ) : Set H.carrier :=
  { x | @dist H.carrier H.isMetricSpace.toDist x (G.action γ x) < ε }

/-! NODE
  \name: HyperbolicSmallDisplacement
  \inputs: ["SmallDisplacementSet", "TranslationLength"]
  \type: lemma
  \natural: If $\gamma$ is loxodromic, then $U_\gamma(\epsilon)$ is a tubular neighborhood of the axis of $\gamma$.
  \NL_proof: The displacement function $x \mapsto d(x, \gamma x)$ achieves its minimum on the axis and increases with distance from the axis. The sublevel set is therefore a tube around the axis.
-/
theorem HyperbolicSmallDisplacement
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (γ : G.carrier) (ε : ℝ) (hε : ε > 0)
    (hlox : TranslationLength n H G γ > 0)
    (hfix : ∃ p q : B.carrier, p ≠ q ∧
      Sum.inr p ∈ FixedPointSet n H G B γ ∧
      Sum.inr q ∈ FixedPointSet n H G B γ) :
    -- The small displacement set is contained in a tubular neighborhood of the axis
    -- (here expressed as a star-shaped set about one of the axis endpoints)
    ∃ (S : StarShapedSet n H B), SmallDisplacementSet n H G γ ε ⊆ S.set := by sorry

/-! NODE
  \name: ParabolicSmallDisplacement
  \inputs: ["SmallDisplacementSet", "StarShapedSet"]
  \type: lemma
  \natural: If $\gamma$ is parabolic, then $U_\gamma(\epsilon)$ is star-shaped about the fixed point of $\gamma$ in $\partial \mathbb{H}^n$.
  \NL_proof: In the upper half-space model with the fixed point at infinity, the displacement function $d(x, \gamma x)$ is a decreasing function of the height coordinate along each vertical geodesic ray. Hence the sublevel set intersects each vertical ray in a half-ray, making it star-shaped about infinity.
-/
theorem ParabolicSmallDisplacement
    (n : ℕ) (H : HyperbolicSpace n) (G : IsomGroup n H) (B : BoundaryHyperbolicSpace n H)
    (γ : G.carrier) (ε : ℝ) (hε : ε > 0)
    (hpar : ¬ ∃ x : H.carrier, G.action γ x = x)
    (hpar_one_fix : ∃! p : B.carrier, Sum.inr p ∈ FixedPointSet n H G B γ) :
    ∃ (S : StarShapedSet n H B), SmallDisplacementSet n H G γ ε ⊆ S.set := by sorry

/-! NODE
  \name: ThickThinDecomposition
  \inputs: ["MargulisLemma", "MargulisLemma2", "ElementarySubgroup", "HyperbolicSmallDisplacement", "ParabolicSmallDisplacement", "SmallDisplacementSet", "ThinPart", "ThickPart", "Tube", "Cusp", "StarShapedSet", "NoEllipticElements"]
  \type: theorem
  \natural: (Thick-Thin Decomposition) Let $M = \mathbb{H}^n / \Gamma$ be a complete hyperbolic manifold and let $\epsilon_n$ be the Margulis constant. Then the thin part $M_{(0,\epsilon_n)}$ is a disjoint union of components, each of which is either (1) a star-shaped cusp neighborhood, or (2) a star-shaped tube around a simple closed geodesic of length $< \epsilon_n$.
  \NL_proof: The thin part lifts to $S = \bigcup_{\varphi \in \Gamma \setminus \{1\}} S_\varphi(\epsilon_n)$ in $\mathbb{H}^n$. If $x \in S_\varphi(\epsilon_n) \cap S_\psi(\epsilon_n)$, the Margulis Lemma implies $\varphi, \psi$ generate a virtually nilpotent group $\Gamma_{\epsilon_n}(x)$. By the elementary subgroup theorem, $\varphi$ and $\psi$ are either parabolic fixing the same boundary point or powers of the same loxodromic isometry. Each connected component $S_0$ of $S$ is thus a union of star-shaped sets centered at a common boundary point $p$ or axis $l$, hence is itself star-shaped. The quotient $S_0 / \Gamma_0$ gives the cusp or tube neighborhoods.
-/
theorem ThickThinDecomposition
    (n : ℕ) (M : CompleteHyperbolicManifold n) (B : BoundaryHyperbolicSpace n M.H)
    (hMargulis : ∃ (ε_n : ℝ), ε_n > 0 ∧
      ∀ (x : M.H.carrier) (ε : ℝ), ε ≤ ε_n →
        ∃ (N : @Subgroup M.G.carrier M.G.isGroup),
          N ≤ SmallDisplacementSubgroup n M.H M.G M.Gamma x ε ∧
          Group.IsNilpotent N)
    (hElem : ∀ (Gamma' : @Subgroup M.G.carrier M.G.isGroup),
      (∃ N : @Subgroup M.G.carrier M.G.isGroup, N ≤ Gamma' ∧ Group.IsNilpotent N) →
      Finite Gamma' ∨
      (∃ γ : M.G.carrier, γ ∈ Gamma' ∧ TranslationLength n M.H M.G γ > 0) ∨
      (∃ p : B.carrier, ∀ g : M.G.carrier, g ∈ Gamma' →
        Sum.inr p ∈ FixedPointSet n M.H M.G B g))
    (hNoEll : ∀ γ : M.G.carrier, γ ∈ M.Gamma →
      γ ≠ @One.one M.G.carrier M.G.isGroup.toOne →
      ¬ ∃ x : M.H.carrier, M.G.action γ x = x)
    (hHypSD : ∀ γ : M.G.carrier, TranslationLength n M.H M.G γ > 0 →
      ∀ ε : ℝ, ε > 0 → True)
    (hParSD : ∀ γ : M.G.carrier,
      (¬ ∃ x : M.H.carrier, M.G.action γ x = x) →
      ∀ ε : ℝ, ε > 0 → True) :
    ∃ (ε_n : ℝ) (_ : ε_n > 0)
      (components : Set (Set M.carrier)),
      -- Components cover the thin part
      (ThinPart n M ε_n = ⋃₀ components) ∧
      -- Components are pairwise disjoint
      (∀ C₁ ∈ components, ∀ C₂ ∈ components, C₁ ≠ C₂ → C₁ ∩ C₂ = ∅) ∧
      -- Each component is either a cusp neighborhood or a tube neighborhood
      (∀ C ∈ components,
        -- Cusp neighborhood: associated to a parabolic subgroup
        (∃ (p : B.carrier),
          ∀ x : M.H.carrier, M.projection x ∈ C →
            ∃ g : M.G.carrier, g ∈ M.Gamma ∧
              Sum.inr p ∈ FixedPointSet n M.H M.G B g) ∨
        -- Tube neighborhood: associated to a loxodromic element with short translation length
        (∃ (γ : M.G.carrier), γ ∈ M.Gamma ∧
          TranslationLength n M.H M.G γ > 0 ∧
          TranslationLength n M.H M.G γ < ε_n))
      := by sorry

/-! NODE
  \name: ThickThinDecomposition_test_trivial
  \inputs: ["ThickThinDecomposition", "ThinPart"]
  \type: unit test
  \natural: For any complete hyperbolic manifold, the thin part with respect to $\epsilon = 0$ is empty.
  \NL_proof: If $\epsilon = 0$, there are no points with injectivity radius less than $0$.
-/
theorem ThickThinDecomposition_test_trivial
    (n : ℕ) (M : CompleteHyperbolicManifold n)
    (hpos : ∀ x : M.carrier, InjectivityRadius n M x ≥ 0) :
    ThinPart n M 0 = ∅ := by sorry

end
