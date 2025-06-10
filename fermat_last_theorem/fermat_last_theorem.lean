-- This file was generated from a JSON blueprint.
import Mathlib.Tactic
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

-- Global variable for the algebraic closure of ℚ
-- variable (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]

/-! NODE
  \name: OddPrimesOnly
  \inputs: []
  \type: theorem
  \informal: If there is a counterexample to Fermat's Last Theorem, then there is a counterexample $a^p+b^p=c^p$ with $p$ an odd prime.
  \informal_proof: Say $a^n + b^n = c^n$ is a counterexample to Fermat's Last Theorem. Every positive integer is either a power of 2 or has an odd prime factor. If $n=kp$ has an odd prime factor $p$ then $(a^k)^p+(b^k)^p=(c^k)^p$ is the counterexample we seek. It remains to deal with the case where $n$ is a power of 2, so let's assume this. We have $3\leq n$ by assumption, so $n=4k$ must be a multiple of~4, and thus $(a^k)^4=(b^k)^4=(c^k)^4$, giving us a counterexample to Fermat's Last Theorem for $n=4$. However theorem \ref{FermatLastTheoremFour} says that $x^4+y^4=z^4$ has no solutions in positive integers.
-/
theorem OddPrimesOnly (hprimes : ∀ p : ℕ, Nat.Prime p → Odd p → FermatLastTheoremFor p) : FermatLastTheorem := by sorry

/-! NODE
  \name: FLT3
  \inputs: []
  \type: hypothesis
  \informal: There are no solutions in positive integers to $a^3+b^3=c^3$.
  \informal_proof:
-/
def FLT3 : Prop := FermatLastTheoremFor 3

/-! NODE
  \name: FLT4
  \inputs: []
  \type: hypothesis
  \informal: There are no solutions in positive integers to $a^4+b^4=c^4$.
  \informal_proof:
-/
def FLT4 : Prop := FermatLastTheoremFor 4

/-! NODE
  \name: FreyPackage
  \inputs: []
  \type: definition
  \informal: A Frey package is a triple of pairwise coprime nonzero integers $a$, $b$, $c$ with $a\equiv3\pmod4$, $b\equiv0\pmod2$, and a prime $p\geq5$ such that $a^p+b^p=c^p$.
  \informal_proof:
-/
structure FreyPackage where
  a : ℤ
  b : ℤ
  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0
  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1 -- same as saying a,b,c pairwise coprime
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0

/-! NODE
  \name: NotFLTGivesFreyPackage
  \inputs: ["FreyPackage"]
  \type: theorem
  \informal: If there is a counterexample to Fermat's Last Theorem with $p\geq5$, then there is a Frey package.
  \informal_proof: Suppose we have a counterexample $a^p+b^p=c^p$ for the given $p$; we now build a Frey package from this data.
 If the greatest common divisor of $a,b,c$ is $d$ then $a^p+b^p=c^p$ implies $(a/d)^p+(b/d)^p=(c/d)^p$. Dividing through, we can thus assume that no prime divides all of $a,b,c$. Under this assumption we must have that $a,b,c$ are pairwise coprime, as if some prime divides two of the integers $a,b,c$ then by $a^p+b^p=c^p$ and unique factorization it must divide all three of them. In particular we may assume that not all of $a,b,c$ are even, and now reducing modulo~2 shows that precisely one of them must be even.
 Next we show that we can find a counterexample with $b$ even. If $a$ is the even one then we can just switch $a$ and $b$. If $c$ is the even one then we can replace $c$ by $-b$ and $b$ by $-c$ (using that $p$ is odd).
 The last thing to ensure is that $a$ is 3 mod~4. Because $b$ is even, we know that $a$ is odd, so it is either~1 or~3 mod~4. If $a$ is 3 mod~4 then we are home; if however $a$ is 1 mod~4 we replace $a,b,c$ by their negatives and this is the Frey package we seek.
-/
lemma NotFLTGivesFreyPackage {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) {p : ℕ} (pp : p.Prime) (hp5 : 5 ≤ p) (H : a^p + b^p = c^p) : Nonempty FreyPackage := by sorry

/-! NODE
  \name: FreyCurve
  \inputs: ["FreyPackage"]
  \type: definition
  \informal: The Frey curve associated to a Frey package $(a,b,c,p)$ is the Weierstrass curve defined by the equation $Y^2=X(X-a^p)(X+b^p).$
  \informal_proof:
-/
def FreyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - P.a ^ P.p)
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p)
  a₆ := 0

/-! NODE
  \name: GaloisModule
  \inputs: []
  \type: definition
  \informal: The Galois module associated to a Weierstrass curve $E$ over $\mathbb{Q}$ and a prime $p$ is the module of $p$-torsion points of $E$ over an algebraic closure $K$ of $\mathbb{Q}$, equipped with the canonical action of the absolute Galois group $Gal(K/\mathbb{Q})$.
  \informal_proof:
-/
structure PTorsionRepresentation (K : Type) [Field K] [Algebra ℚ K] (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] where
  carrier : Type
  isAddCommGroup : AddCommGroup carrier
  isZModPModule : Module (ZMod p) carrier
  isGaloisAction : MulAction (K ≃ₐ[ℚ] K) carrier
  -- The explicit group homomorphism from carrier to E(K)
  φ : letI := isAddCommGroup
      carrier →+ (E.baseChange K).toAffine.Point
  -- 1) φ is injective
  φ_injective : Function.Injective φ
  -- 2) The image of φ is exactly the p-torsion subgroup
  φ_image : ∀ (P : (E.baseChange K).toAffine.Point),
    P ∈ Set.range φ ↔ p • P = 0
  -- 3) φ intertwines the Galois actions
  φ_equivariant : ∀ (g : K ≃ₐ[ℚ] K) (m : carrier),
    letI := isAddCommGroup
    letI := isGaloisAction
    φ (g • m) = WeierstrassCurve.Affine.Point.map g.toAlgHom (φ m)

def GaloisModule (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
    (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] :
    PTorsionRepresentation K E p := sorry

/-! NODE
  \name: FreyCurveGaloisModule
  \inputs: ["FreyCurve", "GaloisModule"]
  \type: definition
  \informal: The torsion Galois representation of the Frey curve associated to a Frey package is the Galois module associated to the Frey curve and the prime $p$ of the Frey package.
  \informal_proof:
-/
def FreyCurveGaloisModule (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K]
    (P : FreyPackage) [h : Fact P.p.Prime] :
    PTorsionRepresentation K (FreyCurve P) P.p :=
  GaloisModule K (FreyCurve P) P.p

/-! NODE
  \name: Wiles_Frey
  \inputs: ["FreyPackage","FreyCurve","FreyCurveGaloisModule"]
  \type: hypothesis
  \informal: The torsion Galois representation of the Frey curve associated to a Frey package is not simple as a module over $\mathbb{Z}/p\mathbb{Z}$.
  \informal_proof:
-/
def Wiles_Frey : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K] (P : FreyPackage) [h : Fact P.p.Prime],
    letI := (FreyCurveGaloisModule K P).isZModPModule
    letI := (FreyCurveGaloisModule K P).isAddCommGroup
    ¬ IsSimpleModule (ZMod P.p) (FreyCurveGaloisModule K P).carrier

/-! NODE
  \name: Mazur_Frey
  \inputs: ["FreyPackage","FreyCurve","FreyCurveGaloisModule"]
  \type: hypothesis
  \informal: The torsion Galois representation of the Frey curve associated to a Frey package is simple as a module over $\mathbb{Z}/p\mathbb{Z}$.
  \informal_proof:
-/
def Mazur_Frey : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] [IsAlgClosure ℚ K] (P : FreyPackage) [h : Fact P.p.Prime],
    letI := (FreyCurveGaloisModule K P).isZModPModule
    letI := (FreyCurveGaloisModule K P).isAddCommGroup
    IsSimpleModule (ZMod P.p) (FreyCurveGaloisModule K P).carrier

/-! NODE
  \name: MainTheorem
  \inputs: ["OddPrimesOnly", "FLT3", "FLT4", "NotFLTGivesFreyPackage", "Wiles_Frey", "Mazur_Frey"]
  \type: theorem
  \informal: Fermat's Last Theorem holds: there are no positive integer solutions to $a^n+b^n=c^n$ for $n>2$.
  \informal_proof: We first show that if there is a counterexample to Fermat's Last Theorem, then there is a counterexample with $n$ an odd prime. This is the content of the theorem \ref{OddPrimesOnly}. We then show that if there is a counterexample with $n\geq5$, then there is a Frey package, which is a triple of pairwise coprime nonzero integers $a$, $b$, $c$ with $a\equiv3\pmod4$, $b\equiv0\pmod2$, and a prime $p\geq5$ such that $a^p+b^p=c^p$. This is the content of the lemma \ref{NotFLTGivesFreyPackage}. We then associate to this Frey package a Weierstrass curve, the Frey curve, and its torsion Galois representation. The key point is that Wiles' theorem says that this torsion Galois representation cannot be simple as a module over $\mathbb{Z}/p\mathbb{Z}$, while Mazur's theorem says that it must be simple as a module over $\mathbb{Z}/p\mathbb{Z}$. This contradiction shows that there can be no counterexamples to Fermat's Last Theorem.
-/
theorem MainTheorem
    (hwiles : Wiles_Frey)
    (hmazur : Mazur_Frey) :
    ∀ n : ℕ, n > 2 → ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ n + b ^ n ≠ c ^ n := by sorry
