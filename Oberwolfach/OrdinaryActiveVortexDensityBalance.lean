module

public import Oberwolfach.OrdinaryTrimmedVortexDensityBalance
public import Oberwolfach.OrdinaryInducedSubsetCounts

@[expose] public section
/-! The parent density and sampling balance hold on the actual trimmed
    active vertex and hub types at every nonterminal vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_active_vortex_density_balance
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (P:SimpleGraph V) (D m:ℕ) (β ε θ α ρ pH:ℝ)
    (Q:Vortex U P D β ε m) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:ρ=initialIndexDensity U D) (hρpos:0<ρ) (hβ:0≤β) (hε:0≤ε) (hεsmall:ε≤1/4) (hpH:0≤pH)
    (hdegree:(θ+α)*Fintype.card V≤D) (i:ℕ):
    let C:=Q.extendedVertices i\Q.extendedVertices (i+2);
    let W:=Q.extendedIndices i\Q.extendedIndices (i+2);
    let A:=Q.extendedVertices (i+1)\Q.extendedVertices (i+2);
    let B:=Q.extendedIndices (i+1)\Q.extendedIndices (i+2);
    let Ain:=A.subtype (fun v=>v∈C);
    let Bin:=B.subtype (fun u=>u∈W);
    let Pactive:=P.induce (C:Set V);
    (∀x:{v:V // v∈C},(θ+α-(10/3:ℝ)*β)*Ain.card≤((Ain∩Pactive.neighborFinset x).card:ℝ)) ∧
    (∀x:{v:V // v∈C},|(ρ*pH)*(Ain∩Pactive.neighborFinset x).card-2*pH*Bin.card|≤
      (ρ*pH)*(5/3:ℝ)*β*Ain.card):=by
  intro C W A B Ain Bin Pactive
  have hAC:A⊆C:=by
    intro x hx
    have hx':x∈Q.extendedVertices (i+1) ∧ x∉Q.extendedVertices (i+2):=Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Q.extendedVertices_subset (by omega) hx'.1,hx'.2⟩
  have hBW:B⊆W:=by
    intro u hu
    have hu':u∈Q.extendedIndices (i+1) ∧ u∉Q.extendedIndices (i+2):=Finset.mem_sdiff.mp hu
    exact Finset.mem_sdiff.mpr ⟨Q.extendedIndices_subset (by omega) hu'.1,hu'.2⟩
  have hcounts:=ordinary_induced_subset_counts P C A hAC
  have hBcounts:=ordinary_induced_subset_counts (⊥:SimpleGraph U) W B hBW
  have htrim:=ordinary_trimmed_vortex_density_balance P D m β ε θ α ρ pH Q hn hreg hρ hρpos hβ hε hεsmall hpH hdegree (i+1) (i+2) (by omega)
  constructor
  · intro x
    have hx:x.val∈Q.extendedVertices ((i+2)-2):=by
      have hh: x.val∈Q.extendedVertices i:=(Finset.mem_sdiff.mp x.property).1
      simpa using hh
    have hh:=htrim.1 x.val hx
    rw [hcounts.1,hcounts.2 x]
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro x
    have hx:x.val∈Q.extendedVertices ((i+2)-2):=by
      have hh: x.val∈Q.extendedVertices i:=(Finset.mem_sdiff.mp x.property).1
      simpa using hh
    have hh:=htrim.2 x.val hx
    rw [hcounts.1,hBcounts.1,hcounts.2 x]
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
