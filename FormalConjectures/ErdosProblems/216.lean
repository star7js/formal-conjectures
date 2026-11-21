/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 216

*References:*
- [erdosproblems.com/216](https://www.erdosproblems.com/216)
- [Ha78] Harborth, H., *Konvexe Fünfecke in ebenen Punktmengen*. Elem. Math. (1978), 116-118.
- [Ho83] Horton, J. D., *Sets with no empty convex $7$-gons*. Canad. Math. Bull. (1983), 482-484.
- [Ni07] Nicolás, C. M., *The empty hexagon theorem*. Discrete Comput. Geom. (2007), 389-397.
- [Ge08] Gerken, T., *Empty convex hexagons in planar point sets*. Discrete Comput. Geom. (2008),
  239-272.
- [HeSc24] Heule, M. J. H. and Scheucher, M., *Happy ending: an empty hexagon in every set of
  $30$ points*. (2024).
-/

@[expose] public section

open EuclideanGeometry

namespace Erdos216

/-- The set `P` contains an empty convex `n`-gon: `n` points of `P` in convex position whose
convex hull contains no other point of `P`. -/
def HasEmptyConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S ∧
    ∀ p ∈ P \ S, p ∉ convexHull ℝ (S : Set ℝ²)

/-- The set of $N$ such that any $N$ points in the plane, no three on a line, contain an empty
convex $k$-gon. Then $g(k)$ exists if and only if this set is nonempty, and $g(k)$ is its least
element. -/
def cardSet (k : ℕ) : Set ℕ :=
  {N | ∀ pts : Finset ℝ², pts.card = N → NonTrilinear (pts : Set ℝ²) →
    HasEmptyConvexNGon k pts}

/--
Let $g(k)$ be the smallest integer (if any such exists) such that any $g(k)$ points in
$\mathbb{R}^2$, no three on a line, contain an empty convex $k$-gon (i.e. with no point in the
interior). Does $g(k)$ exist?

The answer is no: Horton [Ho83] showed that $g(k)$ does not exist for $k\geq 7$.
-/
@[category research solved, question, AMS 52]
theorem erdos_216 : ¬ ∀ k : ℕ, (cardSet k).Nonempty := by
  sorry

/--
Horton [Ho83] constructed, for every $n$, a set of $n$ points with no three on a line and no
empty convex $7$-gon. Hence $g(k)$ does not exist for any $k\geq 7$.
-/
@[category research solved, AMS 52]
theorem erdos_216.variants.horton : ∀ k ≥ 7, cardSet k = ∅ := by
  sorry

/-- Harborth [Ha78] proved that $g(5)=10$. -/
@[category research solved, AMS 52]
theorem erdos_216.variants.harborth : IsLeast (cardSet 5) 10 := by
  sorry

/--
Nicolás [Ni07] and Gerken [Ge08] independently proved that $g(6)$ exists. Heule and Scheucher
[HeSc24] proved that $g(6)=30$.
-/
@[category research solved, AMS 52]
theorem erdos_216.variants.heule_scheucher : IsLeast (cardSet 6) 30 := by
  sorry

end Erdos216
