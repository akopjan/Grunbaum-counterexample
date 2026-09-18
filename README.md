# A convex-body four-hyperplane counterexample in R^4

Lean 4 formalization of a strengthening of Pablo Soberón's counterexample to the Grünbaum conjecture.

The project proves a geometric strengthening/variant of Pablo Soberón's 2026 four-hyperplane mass-partition counterexample: There exists a convex body
`K ⊂ R^4` with nonempty interior such that no four affine hyperplanes divide
`K` into sixteen sign cells of equal four-dimensional volume.

Equivalently, the obstructed mass can be chosen to be **uniform Lebesgue volume
on a convex body**, rather than a general mass. Soberón's paper constructs a
smooth strictly positive density; this project does **not** claim to preserve
that smooth-positive-density property. The strengthening lies in the geometric
specialization of the mass to uniform volume on a convex body.

The proof is based on Soberón's explicit cubic/quartic tensor obstruction and
his Walsh/Fourier perturbation architecture. The density perturbation is
replaced by a small Wulff-body perturbation of the Euclidean ball.

## Attribution

The formalization was prepared by **Arseniy Akopyan**, with substantial
assistance from **ChatGPT (OpenAI)**. The underlying obstruction and explicit
tensor construction are due to **Pablo Soberón**:

> Pablo Soberón, *Four hyperplanes do not always equipartition a mass in R^4*,
> arXiv:2608.23312v2 (2026).

## Main statement

`Challenge.lean` contains only the human-auditable advertised statement. It
quantifies over arbitrary vectors `u_i` and offsets `t_i`; no unit-normal or
nonzero-normal hypothesis is exposed. If `u_i = 0`, one sign side is empty; if
all normals are nonzero, they can be positively rescaled to unit length without
changing the cells.

`Solution.lean` proves exactly the same declaration via
`SoberonConvexBody.ComparatorBridge` and the internal theorem
`SoberonConvexBody.exists_convex_body_counterexample`.

The main declaration is:

```lean
theorem SoberonConvexBody.grunbaum_counterexample :
    ∃ K : ConvexBody (EuclideanSpace ℝ (Fin 4)),
      (interior (K : Set (EuclideanSpace ℝ (Fin 4)))).Nonempty ∧
      ¬ ∃ (u : Fin 4 → EuclideanSpace ℝ (Fin 4)) (t : Fin 4 → ℝ),
          ∀ s : Fin 4 → Bool,
            volume.real
                ((K : Set (EuclideanSpace ℝ (Fin 4))) ∩
                  {x : EuclideanSpace ℝ (Fin 4) |
                    ∀ i,
                      if s i then
                        t i ≤ inner ℝ x (u i)
                      else
                        inner ℝ x (u i) < t i}) =
              volume.real (K : Set (EuclideanSpace ℝ (Fin 4))) / 16
```

## Repository map

- `Challenge.lean` — pure statement surface.
- `Solution.lean` — corresponding proved declaration.
- `comparator.json` — verification configuration.
- `formalization.yaml` — provenance, authorship, AI-use, and fidelity metadata.
- `SoberonConvexBody/Main.lean` — internal final theorem with unit-normal
  hyperplanes.
- `SoberonConvexBody/ComparatorBridge.lean` — normalization/degenerate-normal
  bridge to the literal statement.
- `SoberonConvexBody/Tensors.lean` — Soberón's tensor obstruction.
- `SoberonConvexBody/Geometry*.lean`, `Ball*.lean`, `Shell*.lean`,
  `Wulff*.lean`, `Radial*.lean` — geometric and measure-theoretic estimates.

## Verification status

The proof-development source contains no explicit `sorry`, `axiom`, or `admit`;
`Challenge.lean` intentionally contains the single statement placeholder.

To verify:

```sh
lake exe cache get
lake build
./scripts/verify.sh
```

## Pinned environment

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `141f6b6455959bfeb0b2a6b04118031191d62683`
- License: Apache-2.0

## Source relationship

Soberón's source theorem gives a smooth strictly positive density in `R^4`
with no four-hyperplane equipartition. This development adapts the same
explicit tensor obstruction but produces uniform volume on a convex body with
nonempty interior. See `formalization.yaml` for the precise provenance and
fidelity declaration.
