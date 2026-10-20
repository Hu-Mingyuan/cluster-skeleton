#!/usr/bin/env bash
set -euo pipefail
export MATHLIB_NO_CACHE_ON_UPDATE=1
cd "$(dirname "$0")/.."
lake exe cache get \
  Mathlib.Analysis.Complex.Basic \
  Mathlib.LinearAlgebra.Matrix.Determinant.Basic \
  Mathlib.Order.WellFoundedSet \
  Mathlib.Analysis.Normed.Module.FiniteDimension \
  Mathlib.Analysis.Normed.Group.Constructions \
  Mathlib.Topology.MetricSpace.ProperSpace \
  Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset \
  Mathlib.Algebra.BigOperators.GroupWithZero.Finset \
  Mathlib.Tactic.FunProp Mathlib.Tactic.Linarith \
  Mathlib.LinearAlgebra.Matrix.Notation Mathlib.Tactic.NormNum Mathlib.Tactic.FinCases \
  Mathlib.Dynamics.Flow \
  Mathlib.Topology.Instances.Real.Lemmas \
  Mathlib.Topology.Separation.Hausdorff \
  Mathlib.Geometry.Manifold.Diffeomorph \
  Mathlib.Geometry.Manifold.MFDeriv.Basic \
  Mathlib.Geometry.Manifold.VectorBundle.Tangent \
  Mathlib.Analysis.Calculus.DifferentialForm.Basic \
  Mathlib.Analysis.InnerProductSpace.PiL2 \
  Mathlib.GroupTheory.Perm.Sign
