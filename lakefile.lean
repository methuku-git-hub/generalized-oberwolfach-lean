import Lake
open Lake DSL
package oberwolfachVerification where
  moreLeanArgs := #["-j1"]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"
@[default_target]
lean_lib Oberwolfach

lean_lib FixedPointTheorems

lean_lib HadwigerLean

lean_lib Challenge

lean_lib Solution

-- Build-only ordering of large modules to limit concurrent memory use.
lean_lib MemoryGuard001 where
  roots := #[`Oberwolfach.LongSmallerParentStructuralBeforeMatching]
lean_lib MemoryGuard002 where
  roots := #[`Oberwolfach.LongSmallerParentAllBeforeSpacing]
  needs := #[`@/MemoryGuard001]
lean_lib MemoryGuard003 where
  roots := #[`Oberwolfach.LongSmallerParentExpandedProbability]
  needs := #[`@/MemoryGuard002]
lean_lib MemoryGuard004 where
  roots := #[`Oberwolfach.LongSmallerParentMatchingReservedOccupancy]
  needs := #[`@/MemoryGuard003]
lean_lib MemoryGuard005 where
  roots := #[`Oberwolfach.LongFullParentMatchingSmallerReferenceEarly]
  needs := #[`@/MemoryGuard004]
lean_lib MemoryGuard006 where
  roots := #[`Oberwolfach.LongSmallerParentProbabilityAllMargins]
  needs := #[`@/MemoryGuard005]
lean_lib MemoryGuard007 where
  roots := #[`Oberwolfach.LongSmallerParentMatchingReservedAllMargins]
  needs := #[`@/MemoryGuard006]
lean_lib MemoryGuard008 where
  roots := #[`Oberwolfach.LongFullParentMatchingSmallerReferenceAllMargins]
  needs := #[`@/MemoryGuard007]
lean_lib MemoryGuard009 where
  roots := #[`Oberwolfach.LongSmallerParentChainStructuralBeforeMatching]
  needs := #[`@/MemoryGuard008]
lean_lib MemoryGuard010 where
  roots := #[`Oberwolfach.LongSmallerParentChainAllBeforeSpacing]
  needs := #[`@/MemoryGuard009]
lean_lib MemoryGuard011 where
  roots := #[`Oberwolfach.LongSmallerParentProbabilityChain]
  needs := #[`@/MemoryGuard010]
lean_lib MemoryGuard012 where
  roots := #[`Oberwolfach.LongSmallerParentMatchingReservedChain]
  needs := #[`@/MemoryGuard011]
lean_lib MemoryGuard013 where
  roots := #[`Oberwolfach.LongFullParentMatchingSmallerReferenceChain]
  needs := #[`@/MemoryGuard012]
lean_lib MemoryGuard014 where
  roots := #[`Oberwolfach.LongNamedReservedCorrectionUniformLists]
  needs := #[`@/MemoryGuard013]
lean_lib MemoryGuard015 where
  roots := #[`Oberwolfach.LongNamedInitialCorrectionHighProbabilityCap]
  needs := #[`@/MemoryGuard014]
lean_lib MemoryGuard016 where
  roots := #[`Oberwolfach.LongNamedEarlyMatchingCorrectionLists]
  needs := #[`@/MemoryGuard015]
lean_lib MemoryGuard017 where
  roots := #[`Oberwolfach.LongNamedParentTestsStructuralBeforeMatching]
  needs := #[`@/MemoryGuard016]
lean_lib MemoryGuard018 where
  roots := #[`Oberwolfach.LongNamedParentTestsAuxCapBeforeSpacing]
  needs := #[`@/MemoryGuard017]
lean_lib MemoryGuard019 where
  roots := #[`Oberwolfach.FirstVortexConcreteCommonBalancedActualChainInnerSum]
  needs := #[`@/MemoryGuard018]
lean_lib MemoryGuard020 where
  roots := #[`Oberwolfach.FirstVortexConcreteFixedClassCommonBalancedActualChainInnerSum]
  needs := #[`@/MemoryGuard019]
lean_lib MemoryGuard021 where
  roots := #[`Oberwolfach.FirstVortexConcreteCommonBalancedActualChainGeometry]
  needs := #[`@/MemoryGuard020]
lean_lib MemoryGuard022 where
  roots := #[`Oberwolfach.FirstVortexConcreteCommonBalancedActualChainInnerSumExplicitLevel]
  needs := #[`@/MemoryGuard021]
lean_lib MemoryGuard023 where
  roots := #[`Oberwolfach.FirstVortexConcreteFixedClassActualChainInnerSumExplicitLevel]
  needs := #[`@/MemoryGuard022]
lean_lib MemoryGuard024 where
  roots := #[`Oberwolfach.FirstVortexFixedTerminalChainCommonBalancedActualChainInnerSum]
  needs := #[`@/MemoryGuard023]
lean_lib MemoryGuard025 where
  roots := #[`Oberwolfach.FirstVortexFixedTerminalChainActualChainInnerSumExplicitLevel]
  needs := #[`@/MemoryGuard024]
lean_lib MemoryGuard026 where
  roots := #[`Oberwolfach.LongNamedParentCorrectionOrderedTests]
  needs := #[`@/MemoryGuard025]
lean_lib MemoryGuard027 where
  roots := #[`Oberwolfach.LongAllStructuralSelectorProbabilityRelativeBoundaryEvent]
  needs := #[`@/MemoryGuard026]
lean_lib MemoryGuard028 where
  roots := #[`Oberwolfach.LongAllStructuralSelectorProbabilitySeparateLevelLosses]
  needs := #[`@/MemoryGuard027]
lean_lib MemoryGuard029 where
  roots := #[`Oberwolfach.LongAllStructuralSelectorPositiveRelativeBoundaryEvent]
  needs := #[`@/MemoryGuard028]
lean_lib MemoryGuard030 where
  roots := #[`Oberwolfach.LongAllStructuralSelectorSeparateLevelLosses]
  needs := #[`@/MemoryGuard029]
lean_lib MemoryGuard031 where
  roots := #[`Oberwolfach.FirstVortexSelectorHostGeometryTail]
  needs := #[`@/MemoryGuard030]
lean_lib MemoryGuard032 where
  roots := #[`Oberwolfach.FirstVortexSelectorSizedHostTail]
  needs := #[`@/MemoryGuard031]
lean_lib MemoryGuard033 where
  roots := #[`Oberwolfach.FirstVortexSelectorSameThresholdTail]
  needs := #[`@/MemoryGuard032]
lean_lib MemoryGuard034 where
  roots := #[`Oberwolfach.FirstVortexSelectorActualHostFixedTail]
  needs := #[`@/MemoryGuard033]
lean_lib MemoryGuard035 where
  roots := #[`Oberwolfach.FirstVortexSelectorActualHostCoreLateThresholdTail]
  needs := #[`@/MemoryGuard034]
lean_lib MemoryGuard036 where
  roots := #[`Oberwolfach.LongAllStructuralCoreAllReservesLateHostRetentionHighProbability]
  needs := #[`@/MemoryGuard035]
lean_lib MemoryGuard037 where
  roots := #[`Oberwolfach.LongAllStructuralCoreAllReservesHighProbability]
  needs := #[`@/MemoryGuard036]
lean_lib MemoryGuard038 where
  roots := #[`Oberwolfach.LongNoCompletionCombinedSameSampleHighProbability]
  needs := #[`@/MemoryGuard037]
lean_lib MemoryGuard039 where
  roots := #[`Oberwolfach.FirstVortexSameSampleChainRatesReady]
  needs := #[`@/MemoryGuard038]
lean_lib MemoryGuard040 where
  roots := #[`Oberwolfach.FirstVortexSameSampleFixedClassChainRatesReady]
  needs := #[`@/MemoryGuard039]
lean_lib MemoryGuard041 where
  roots := #[`Oberwolfach.FirstVortexSelectorSameSampleFactorSeedReadyProof]
  needs := #[`@/MemoryGuard040]
lean_lib MemoryGuard042 where
  roots := #[`Oberwolfach.FirstVortexFixedTerminalChainRatesReady]
  needs := #[`@/MemoryGuard041]
lean_lib MemoryGuard043 where
  roots := #[`Oberwolfach.FirstVortexSelectorActualHostCoreEfficientTail]
  needs := #[`@/MemoryGuard042]
