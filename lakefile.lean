import Lake
open Lake DSL

package «lean957» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "067a2c89ad91a79c38006b1d0e8137533fadb81b"

lean_lib Foundations where

lean_lib Algebra where

lean_lib Geometry where

lean_lib Reduction where

lean_lib AngularPacking where

lean_lib PlanarDirections where

lean_lib NearestGraph where

lean_lib CirclePacking where

lean_lib NearestBound where

lean_lib DiameterSupport where

lean_lib DiameterGraph where

lean_lib DiameterExtreme where

lean_lib DiameterHull where

lean_lib DiameterCrossing where

lean_lib ExtremeSubsets where

lean_lib PlanarRadon where

lean_lib DiameterIntersectionMetric where

lean_lib DiameterIntersection where

lean_lib PlanarOrientation where

lean_lib DiameterSelector where

lean_lib GraphSelectorBound where

lean_lib DiameterBound where

lean_lib ChargingReduction where

lean_lib HalfplanePacking where

lean_lib BoundaryDegree where

lean_lib NearestMetric where

lean_lib SixAngleRigidity where

lean_lib CircularGap where

lean_lib SixtyDegreeChord where

lean_lib SixCircleRigidity where

lean_lib SixNeighborStructure where

lean_lib Antipodal where

lean_lib EquilateralRhombus where

lean_lib HexagonCompletion where

lean_lib BoundarySixNeighbors where

lean_lib BoundaryNeighborOrder where

lean_lib InteriorTransfer where

lean_lib InteriorExclusion where

lean_lib ChargingAccounting where

lean_lib ChargingCertificates where

lean_lib FlatExceptionalCount where

lean_lib GridPacking where

lean_lib LargeScaleReduction where

lean_lib HullSupport where

lean_lib HullInterior where

lean_lib HullRadialOrder where

lean_lib HullGeneration where

lean_lib CollinearBound where

lean_lib HullDegree where

lean_lib RadialSupport where

lean_lib RadialAngles where

lean_lib HullAngularGaps where

lean_lib WrappedSector where

lean_lib HullEdgeOrder where

lean_lib HullStrictTurn where

lean_lib HullCardinality where

lean_lib HullCycle where

lean_lib CyclicAngleSum where

lean_lib EdgeAngleLift where

lean_lib DirectionSine where

lean_lib HullEdgeLifts where

lean_lib PolygonTurning where

lean_lib HullExteriorAngles where

lean_lib HullFlatVertices where

lean_lib HullInteriorAngle where

lean_lib MiddleAngleBounds where

lean_lib TriangleInterior where

lean_lib RotatedCoordinates where

lean_lib CircleTriangle where

lean_lib MiddleTriangle where

lean_lib MiddleNeighborInterior where

lean_lib CentralProjection where

lean_lib CentralCommonNeighbors where

lean_lib LocalCharge where

lean_lib LocalChargeAssembly where

lean_lib CentralLocalCharge where

lean_lib ShortArcPacking where

lean_lib TwoCircleSeparation where

lean_lib NormalizedEdge where

lean_lib FiveMiddleCommon where

lean_lib FiveCentralCharge where

lean_lib NormalizedEdgeGeometry where

lean_lib HullEdgeBeyond where

lean_lib HexagonExtension where

lean_lib TruncatedCirclePacking where

lean_lib SharedReceiverDegree where

lean_lib SharedHexagonBound where

lean_lib SharedOuterDegree where

lean_lib SharedHexagonCoordinates where

lean_lib ShortEdgeChain where

lean_lib TightHullDirections where

@[default_target]
lean_lib Lean957 where

lean_lib NormalizedHullEdges where

lean_lib HullSpanFromDirections where

lean_lib TightFlatHullSpan where

lean_lib TightFlatSharedCharge where

lean_lib NormalizedTriangle where

lean_lib NormalizedReceiverInterior where

lean_lib SharedHexagonCharge where

lean_lib RectangleInterior where

lean_lib HullSpanInterpolation where

lean_lib NormalizedDiameterCone where

lean_lib SmallAngleProjection where

lean_lib TightFlatVertices where

lean_lib TightFlatOffsets where

lean_lib HullChordAdjacency where

lean_lib DonorCases where

lean_lib WeightedChargeAssembly where

lean_lib SupportedSharedCharge where

lean_lib ShortHullChord where

lean_lib TightFlatChord where

lean_lib SixCentralNeighbor where

lean_lib DonorNearestShared where

lean_lib CentralAntipodes where

lean_lib SixNeighborDistances where

lean_lib FlatDonorReduction where

lean_lib SixDiameterGeometry where

lean_lib DiameterAxisSeparation where

lean_lib HullChordSeparation where

lean_lib SharedFiveGeometry where

lean_lib ShortDiameterChordAlgebra where

lean_lib ShortDiameterChord where

lean_lib AdjacentDonorReduction where

lean_lib ConfigurationCongruence where

lean_lib PlaneReflection where

lean_lib ReflectedHull where

lean_lib BackwardSharedSix where

lean_lib BoundaryTriangleSix where

lean_lib SharedFiveReceiver where

lean_lib SharedFiveCharge where

lean_lib BackwardSharedFive where

lean_lib AllLocalPackets where

lean_lib PacketMetricLocality where

lean_lib SourceAxisLocality where

lean_lib DeepestSharedFiveGeometry where

lean_lib SharedFiveReceiverRegion where

lean_lib DeepestNeighborHeight where

lean_lib SharedFivePairSelection where

lean_lib CertifiedCentralPackets where

lean_lib CertifiedSharedSix where

lean_lib SharedFivePairReflection where

lean_lib SharedFiveCenterFamily where

lean_lib CertifiedLowCentral where

lean_lib SupportedCentralNeighbor where

lean_lib FlatDiameterLocality where

lean_lib TightFlatDiameterLocality where

lean_lib FlatCentralProjection where

lean_lib FlatSharedClassification where

lean_lib CertifiedSharedSixReflection where

lean_lib CertifiedDonorRules where

lean_lib AllCertifiedDonors where

lean_lib SupportingPacketFrames where

lean_lib ExtendedFlatDirections where

lean_lib FourDeltaDiameterLocality where

lean_lib ChargeNeighborhood where

lean_lib CertifiedSourceLocality where

lean_lib DeepReceiverExclusion where

lean_lib FlatUnitCircleSources where

lean_lib DirectChargeAccounting where

lean_lib DirectChargeCapacity where

lean_lib DeepSharedReceivers where

lean_lib FiveHighestSelection where

lean_lib SupportingHeightFamily where

lean_lib SharedCenterUniqueness where

lean_lib DeepCenterPacking where

lean_lib SharedSixLowerExclusion where

lean_lib CenterChargeGroups where

lean_lib ActualSharedFiveGroups where

lean_lib IndirectChargeUnitBound where

lean_lib DeepReceiverCapacity where

lean_lib DeepExactRadiusPacking where

lean_lib DeepOverloadSaturation where

lean_lib SharedSixPairCompatibility where

lean_lib SharedFivePairedReceivers where

lean_lib DeepFiveRuleCases where

lean_lib DeepFiveObstruction where

lean_lib SharedSixLowerCapacity where

lean_lib ReflectedSharedSixLowerExclusion where

lean_lib ReflectedSharedSixLowerCapacity where

lean_lib SharedFiveSixExtensionExclusion where

lean_lib SharedSixSecondExtensionCapacity where

lean_lib ReflectedSharedSixSecondExtensionCapacity where

lean_lib SharedSixRightCapacity where

lean_lib DeepFiveDegreeSixSourceCapacity where

lean_lib DeepFiveCenterReduction where


lean_lib DeepFiveCapacityComplete where
  roots := #[`DeepFiveCapacityComplete]

lean_lib MixedReceiverCenterCapacity where

lean_lib DegreeFiveMixedReduction where

lean_lib ShallowDegreeFiveStructure where

lean_lib ShallowDegreeFiveOverload where

lean_lib ShallowCaseFourObstruction where

lean_lib ShallowSourceTypes where

lean_lib ShallowTripleNormalForm where

lean_lib ShallowPaperCaseTypes where

lean_lib ShallowCaseFourOrientation where

lean_lib SupportingFamilyShallowNormalForm where

lean_lib ShallowCase4CenterExclusion where

lean_lib ShallowCase4ForeignCenterGeometry where

lean_lib ShallowCase4ReceiverSide where

lean_lib ShallowCase4SideNormalForm where

lean_lib ShallowCase4PartnerFreeNormalForm where

lean_lib ShallowDegreeFiveCardinality where

lean_lib ShallowCase4ThreeStepExclusion where

lean_lib ShallowCase4ActiveGeometry where
lean_lib ShallowCase4TwoStepReduction where

lean_lib LocalScalarBridgeCompatibility where

lean_lib ShallowCase4OppositeSideExclusion where

lean_lib ShallowMixedDirectOffsets where

lean_lib TwoSixBottomRigidity where

lean_lib FourEndpointPacking where

lean_lib FourEndpointExclusion where

lean_lib NeighborRoutingCapacity where

lean_lib SixBottomLowDegreeCapacity where

lean_lib BlockedNeighborRouting where

lean_lib FarDeepReceiverExclusion where

lean_lib SharedSixLowDegreeReduction where

lean_lib SharedSixTerminalGeometry where

lean_lib ReflectedSharedSixTerminalGeometry where

lean_lib SharedSixLowDegreeCapacity where

lean_lib LowDegreeCapacity where

lean_lib SharedFiveBottomCapacity where

lean_lib DegreeFiveNoDiameterCapacity where

lean_lib SupportingFamilyCapacity where

lean_lib Erdos957Complete where
