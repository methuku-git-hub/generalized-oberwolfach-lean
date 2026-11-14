module

public import Oberwolfach.LongDualResidualReconstructionGeometry
public import Oberwolfach.MarkedSampleArcs

@[expose] public section
/-! The corrected sample's actual arc types inherit the host and avoidance
properties of the encoded oriented residual, without reindexing the wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_encoded_residual_sample_reconstruction_geometry
    {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (G S Small:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (π:Equiv.Perm V) (d:ℕ) (σ:Sym2 V→Option (Bool×Bool))
    (T:Finset {a:V×V // longEligibleResidualArc M Small ⊥ a})
    (hcode:∀mark x y,markedPhysicalRim G π (3*d) σ mark x y=1 ↔
      if mark then ∃e:residualMarkedArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc (longEligibleResidualArc M Small ⊥) T,e.val.val.1=x∧e.val.val.2=y):
    let E:=MarkedSampleArc G π (3*d) σ false
    let K:=MarkedSampleArc G π (3*d) σ true
    letI : Fintype E:=Fintype.ofFinite _
    letI : Fintype K:=Fintype.ofFinite _
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let Rrim:=markedPhysicalRimSet tail head ktail khead π;
    (∀e:E,tail e≠head e) ∧ (∀e:K,ktail e≠π (khead e)) ∧
    Function.Injective (markedPhysicalEdge tail head ktail khead π) ∧
    physicalEdgeGraph Rrim≤S ∧
    (∀x y,Small.Adj x y→({x,y}:Finset V)∉Rrim) :=by
  intro E K tail head ktail khead Rrim
  have hgraph:∀e:{a:V×V // longEligibleResidualArc M Small ⊥ a},(S\Small).Adj e.val.1 e.val.2:=by
    intro e
    have hp:=hphysical e.val.1 e.val.2
    have hm:=e.property.1
    have hs:S.Adj e.val.1 e.val.2:=by split_ifs at hp with hh;exact hh;omega
    exact ⟨hs,e.property.2.1⟩
  have hE:∀e:E,(S\Small).Adj (tail e) (head e):=by
    intro e
    obtain ⟨a,ha,hb⟩:=(hcode false e.val.1 e.val.2).mp e.property
    simpa only [tail,head,ha,hb] using hgraph a.val
  have hK:∀e:K,(S\Small).Adj (ktail e) (π (khead e)):=by
    intro e
    obtain ⟨a,ha,hb⟩:=(hcode true e.val.1 e.val.2).mp e.property
    have hh:=hgraph a.val
    rw [ha] at hh
    have heq:π e.val.2=a.val.val.2:=by rw [←hb,Equiv.apply_symm_apply]
    simpa only [ktail,khead,heq] using hh
  have hRim:physicalEdgeGraph Rrim≤S\Small:=marked_physical_host_graph_le (S\Small) tail head ktail khead π hE hK
  refine ⟨(fun e=>(hE e).ne),(fun e=>(hK e).ne),markedSampleArc_physical_injective G π (3*d) σ,?_,?_⟩
  · intro x y hxy;exact (hRim hxy).1
  · intro x y hxy hrim;exact (hRim ⟨hxy.ne,hrim⟩).2 hxy
end Oberwolfach
