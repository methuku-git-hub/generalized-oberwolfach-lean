module

public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
/-! Physical edges recorded by the oriented class lie in that class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

theorem long_prescribed_union_in_oriented_class
    (S Small:SimpleGraph V) (M:V→V→ℕ) (A:Finset (V×V)) (E:U→Finset (Sym2 V))
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hA:∀a∈A,M a.1 a.2=1)
    (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (hE:prescribedPhysicalUnion E≤Small):prescribedPhysicalUnion E≤S :=by
  intro x y hxy
  have hSmallAdj:=hE hxy
  have hedge:s(x,y)∈Small.edgeFinset:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hSmallAdj
  rw [hSmall] at hedge
  obtain ⟨a,ha,haeq⟩:=Finset.mem_image.mp hedge
  have hSa:S.Adj a.1 a.2:=by
    by_contra hn
    have hh:=hphysical a.1 a.2
    rw [if_neg hn] at hh
    have hh':=hA a ha
    omega
  have hs:s(a.1,a.2)∈S.edgeFinset:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hSa
  rw [haeq] at hs
  simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hs
end Oberwolfach
