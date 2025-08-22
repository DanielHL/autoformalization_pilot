# autoformalization_pilot
A repository holding template examples for an autoformalization dataset. Each problem will be a lean file. A problem is solved when all sorry's have been filled in and the whole file typechecks.

`parser.py` parses the lean files into a directed graph. Example usage: `python parser.py fermat_last_theorem/fermat_last_theorem.lean`

# Organization

This project developed out of the workshop "Autoformalization for the working mathematician" at ICERM in April, 2025. The benchmark was conceived and designed by a groupd of researches from industry and mathematics:

Jarod Alper (University of Washington)
Daniel Halpern-Leistner (Cornell University)
Albert Q. Jiang (Mistral)
Alex Meiburg (Perimiter Institute and Harmonic)
Kim Morrison (Lean FRO)
Jason Rute (Mistral)
Adam Topaz (University of Alberta)
Sean Welleck (Carnegie Melon University)
Zeyu Zheng (Carnegie Melon University)

# How to contribute
At the moment, we are collecting problems privately. If you are interested in contributing, please contact me: daniel.hl@cornell.edu

If you are a mathematician with little to no Lean experience, or a Lean enthusiast with minimal research-level mathematical training, you can still contribute! We hope to pair people with complementary expertise to create problems.

# Guidlines for contributions

- The problem should be *HARD*, requiring substantial mathematical reasoning to solve.

- The problem should *NOT* be open. For any statement that requires the solver to provide a formal proof, the problem should provide a correct and precise natural language proof.

- The problem should be unlikely to appear online in a human formalization project any time soon.

- It is OK to omit some minor intermediate lemmas. This just makes the problem harder by essentially requiring the solver to discover and add those on its own!

- The ultimate contribution should be a single Lean 4 file that may import from MATHLIB but no other libraries. It should generate no compilation errors. It should contain up to 20 `sorry` statements such that, once filled in, the file will type check and constitute a proof of an interesting mathematical result. It is OK to include some supporting code above the first node.

- You may include as many formalized background statements as you would like, and add them as hypotheses to the statement of the main theorem. These will be identified as `hypothesis` nodes (see below).

# Formatting the data
A datapoint is a lean file with specific formatting requirements. The template is `fermat_last_theorem/fermat_last_theorem.lean.` This will NOT be a problem in the final dataset, as it is based on an active human formalization effort (https://github.com/ImperialCollegeLondon/FLT). It is also somewhat easier than the problems we hope to receive, because it black-boxes the most important parts of the proof.

The nodes should consist of a comment block containing specific metadate, followed by a piece of lean code. For example:

```Lean
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
```

The inputs field indicates the logical dependencies. They are hints to the solver.

The node above is a complete definition. On the other hand, it is possible to give a definition that does require a `sorry` to be filled in. In the template, we do this by defining a structure containing lemmas that guarantee that any implementation corresponds to the intended mathematical object. Then the solver must find a constructor for this structure, which amounts to formalizing a definition of the object. (In this case, the Galois representation associated to the p-torsion points of an Elliptic curve.)

```Lean
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
```

Other nodes can be "hypotheses," which are propositions that are defined by not instantiated. The idea is that the main theorem is allows to be contingent on these hypotheses, for example:

```Lean
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
```

Finally, nodes can also be theorems or lemmas, which are propositions whose proof is `sorry`:

```Lean
/-! NODE
  \name: OddPrimesOnly
  \inputs: []
  \type: theorem
  \informal: If there is a counterexample to Fermat's Last Theorem, then there is a counterexample $a^p+b^p=c^p$ with $p$ an odd prime.
  \informal_proof: Say $a^n + b^n = c^n$ is a counterexample to Fermat's Last Theorem. Every positive integer is either a power of 2 or has an odd prime factor. If $n=kp$ has an odd prime factor $p$ then $(a^k)^p+(b^k)^p=(c^k)^p$ is the counterexample we seek. It remains to deal with the case where $n$ is a power of 2, so let's assume this. We have $3\leq n$ by assumption, so $n=4k$ must be a multiple of~4, and thus $(a^k)^4=(b^k)^4=(c^k)^4$, giving us a counterexample to Fermat's Last Theorem for $n=4$. However theorem \ref{FermatLastTheoremFour} says that $x^4+y^4=z^4$ has no solutions in positive integers.
-/
theorem OddPrimesOnly (hprimes : ∀ p : ℕ, Nat.Prime p → Odd p → FermatLastTheoremFor p) : FermatLastTheorem := by sorry
```
