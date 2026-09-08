/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT.lean
-/
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.ParametersBase
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SqrtBounds
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.AxisParallelLine
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DiagonalLine
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LinePolynomials
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LowDegreePolynomial
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.QuantumState
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.OperatorExpectations
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.Distribution
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.PMFAverages
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.PMFUniformAverages
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionUniformSums
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionAvg
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionPMF
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionProduct
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionMapAverages
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DistributionUniform
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementCore
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.OpFamily
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.Defs
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.StrategyPolynomialFamilies
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.Classical
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.SurfaceVsPoint
import MIPRE.Background.LIDT.MIPStarRE.LDT.Test.MainTheorem.MainFormal
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.FiniteFields
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Defs
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.DistanceBounds
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ConsistencyBridges
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.ApproxDelta
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Completion
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Left
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SwitchSandwichGapBounds.Middle
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.Completeness
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Completion
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Triangles.SimEq
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.ProjectorApprox
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.Conversion
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Line169Repair
import MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output
import MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Families
import MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems
import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Defs
import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Saturated
import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.StrongDuality.Separation
import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.AddInUFullStatement
import MIPRE.Background.LIDT.MIPStarRE.LDT.SelfImprovement.Theorems.Results.SelfImprovementTop.Core
import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Defs
import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.SharedHelpers.SharedLine
import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.BridgeTheorems.DropBridges
import MIPRE.Background.LIDT.MIPStarRE.LDT.CommutativityPoints.AnswerTheorems
import MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Defs.Normalization
import MIPRE.Background.LIDT.MIPStarRE.LDT.Commutativity.Main.Results
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Families
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Context
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Statements
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Core.LdGbcon
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Core.CompletePart
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.SwitcherooCompletion
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.CommutingWithG.Incomplete
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.GHatFacts
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.Final
import MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ContextWrappers
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Polynomials
import MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.PolynomialAgreement

-- Mathlib 4.31 header checks require this for this aggregate module.
set_option linter.style.header false

/-!
# Low individual degree test

This root module provides the Lean development for the low individual degree test,
including the test definition, preliminary analytic estimates, the
projectivization theorem, the main-induction interface, global variance,
self-improvement, commutativity, and pasting.
-/
