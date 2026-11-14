module

public import Oberwolfach.LongEligibleMarkedIncomingChange
public import Oberwolfach.BalancedOrientationArcDegrees

@[expose] public section
/-! Removing the physical edges of an oriented packing removes exactly those
directions from the original zero-one class orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_residual_orientation_arc_identity
    (S Small:SimpleGraph V) (M:V→V→ℕ) (A:Finset (V×V))
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hA:∀a∈A,M a.1 a.2=1)
    (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2))):
    ∀x y,longEligibleResidualArc M Small ⊥ (x,y)↔(x,y)∈orientationMatrixArcs M\A:=by
  intro x y
  have hmem:M x y=1→(Small.Adj x y↔(x,y)∈A):=by
    intro hm
    constructor
    · intro hs
      have he:s(x,y)∈A.image (fun a=>s(a.1,a.2)):=by rw [←hSmall];exact SimpleGraph.mem_edgeFinset.mpr hs
      obtain ⟨⟨u,v⟩,ha,heq⟩:=Finset.mem_image.mp he
      have hor:=hA (u,v) ha
      rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩|⟨hu,hv⟩
      · exact ha
      · have hrev:M y x=1:=by
          change u=y at hu
          change v=x at hv
          simpa only [hu,hv] using hor
        have hh:=hphysical x y
        split_ifs at hh <;> omega
    · intro ha
      have he:s(x,y)∈Small.edgeFinset:=by
        rw [hSmall]
        exact Finset.mem_image.mpr ⟨(x,y),ha,rfl⟩
      exact SimpleGraph.mem_edgeFinset.mp he
  simp only [longEligibleResidualArc,SimpleGraph.bot_adj,not_false_eq_true,and_true,Finset.mem_sdiff,
    orientationMatrixArcs,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hm,hs⟩
    exact ⟨hm,fun ha=>hs ((hmem hm).mpr ha)⟩
  · rintro ⟨hm,ha⟩
    exact ⟨hm,fun hs=>ha ((hmem hm).mp hs)⟩
end Oberwolfach
