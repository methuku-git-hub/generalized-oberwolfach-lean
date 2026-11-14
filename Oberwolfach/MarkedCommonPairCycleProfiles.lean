module

public import Oberwolfach.MarkedDiagramCompletion

@[expose] public section

/-! Original common-cycle profiles for every pair of distinct hubs.
The coefficient functions are fixed on the original ambient cycle family;
all row-root loads omit the root indicator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V]

structure MarkedCommonPairCycleProfiles (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b l:ℕ) (q₀ β blo bhi ε:ℝ) where
  A:U→U→Finset V
  B:U→U→Finset V
  q:U→U→ℝ
  w:U→U→MarkedCycleTuple tail head ktail khead (l+4) π b→ℝ
  q_lower:∀ u u',u≠u'→q₀≤q u u'
  marked_class:∀ u u',u≠u'→∀ v,v∈A u u'↔HK v u∧HK v u'
  ordinary_class:∀ u u',u≠u'→∀ v∈B u u',H₀ v u∧H₀ v u'
  marked_size:∀ u u',u≠u'→|((A u u').card:ℝ)-q u u'*Fintype.card V|≤ε*Fintype.card V
  ordinary_size:∀ u u',u≠u'→|((B u u').card:ℝ)-(l+4)*q u u'*Fintype.card V|≤ε*Fintype.card V
  overlap:∀ u u',u≠u'→((B u u'∩(A u u').image π).card:ℝ)≤ε*Fintype.card V
  cycles:∀ u u',u≠u'→β*(Fintype.card V:ℝ)^(l+5)≤
    Fintype.card (ClassMarkedCycle tail head ktail khead (l+4) π b (A u u') (B u u'))
  paths:∀ u u',u≠u'→∀ j:Bool,∀ v v':V,v≠v'→β*(Fintype.card V:ℝ)^(l+4)≤
    Fintype.card (RootFirstCommonMarkedPath tail head ktail khead (l+4) π b
      (fun x (_:Unit)=>x∈B u u') (fun x (_:Unit)=>x∈A u u') j v v' () ())
  weight_bounds:∀ u u',u≠u'→∀ C,blo/(Fintype.card V:ℝ)^(l+4)≤w u u' C∧
    w u u' C≤bhi/(Fintype.card V:ℝ)^(l+4)
  root_loads:∀ u u',u≠u'→∀ j:Bool,∀ v:V,|1-resourceRootOmittedLoad typedMarkedCycleVertices (w u u')
    (fun x=>x∈typedClassSet (A u u') (B u u')) (j,v)|≤ε

end Oberwolfach
