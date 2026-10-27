import ThresholdHC.ResearchRouteA.Sanity

namespace ThresholdHC.ResearchRouteA.Audit

example : ThresholdHC.ResearchRouteA.SeparateMomentBoundsStatement :=
  ThresholdHC.ResearchRouteA.separate_moment_bounds

example : ThresholdHC.ResearchRouteA.UniformFamilyBoundsStatement :=
  ThresholdHC.ResearchRouteA.uniform_family_bounds

#check ThresholdHC.ResearchRouteA.SeparateMomentBoundsStatement
#check ThresholdHC.ResearchRouteA.UniformFamilyBoundsStatement
#print axioms ThresholdHC.ResearchRouteA.separate_moment_bounds
#print axioms ThresholdHC.ResearchRouteA.uniform_family_bounds
#print axioms ThresholdHC.ResearchRouteA.independent_constant_observations
#print axioms ThresholdHC.ResearchRouteA.deterministic_gap_model
#print axioms ThresholdHC.ResearchRouteA.deterministic_gap_separate_bounds

end ThresholdHC.ResearchRouteA.Audit
