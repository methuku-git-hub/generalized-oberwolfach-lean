module

public import Oberwolfach.MarkedInitialDiagramSupport

@[expose] public section

/-! Separation and exclusion for the whole newly constructed diagram,
including vertices of fixed-endpoint paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {src dst:A→V} {row:S→V} {φ:V→V} {u u':S→U} {jr:A→Bool} {js:S→Bool}
    {W Z:Finset V} {B:Finset U}

def markedDiagramFreeRows (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):Finset V:=
  markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s)∪
    Finset.univ.biUnion (fun z=>Finset.univ.image (D.pv z))

theorem marked_diagram_rows_eq
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    markedDiagramRows D=Z∪markedDiagramFreeRows D:=Finset.union_assoc _ _ _

theorem marked_diagram_endpoints_in_paths
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (z:Σ v,DirectedIncidence src dst v):
    D.pv z 0∈markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s)∧
    D.pv z (Fin.last (l+3))∈markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s):=by
  rw [(D.vertexEnds z).1,(D.vertexEnds z).2]
  rcases z with ⟨v,e|e⟩
  · exact ⟨markedPathUnion_rim _ _ _ _ e.val 0,markedPathUnion_spoke _ _ _ _ (D.a v e).val _⟩
  · exact ⟨markedPathUnion_spoke _ _ _ _ (D.d v e).val 0,markedPathUnion_rim _ _ _ _ e.val _⟩

theorem marked_diagram_free_rows_avoid
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    Disjoint (markedDiagramFreeRows D) (W∪Z):=by
  have hPW:=markedPathUnion_avoid (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s) W
    (fun e k=>(D.rimAvoid e k).1) (fun s k=>(D.spokeAvoid s k).1)
  have hPZ:=markedPathUnion_avoid (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s) Z
    (fun e k=>(D.rimAvoid e k).2.1) (fun s k=>(D.spokeAvoid s k).2.1)
  have hvW:∀ z k,D.pv z k∉W:=by
    intro z k hk
    have he:=D.vertexNewAvoid z k (Finset.mem_union_left _ hk)
    have hend:=marked_diagram_endpoints_in_paths D z
    rcases Finset.mem_insert.mp he with he|he
    · exact Finset.disjoint_left.mp hPW (he.symm ▸ hend.1) hk
    · have he':D.pv z k=D.pv z (Fin.last (l+3)):=Finset.mem_singleton.mp he
      exact Finset.disjoint_left.mp hPW (he'.symm ▸ hend.2) hk
  apply Finset.disjoint_left.mpr
  intro v hv hz
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Finset.disjoint_left.mp (Finset.disjoint_union_right.mpr ⟨hPW,hPZ⟩) hv hz
  · obtain ⟨z,_,hv⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hz with hz|hz
    · exact hvW z k hz
    · exact (D.vertexAvoid z k).1 hz

theorem marked_diagram_free_rows_separated
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    (∀ x∈markedDiagramFreeRows D,∀ y∈Z,¬PermutationClose π b x y)∧
    (∀ x∈markedDiagramFreeRows D,∀ y∈markedDiagramFreeRows D,x≠y→¬PermutationClose π b x y):=by
  have hPZ:=markedPathUnion_root_separated (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s) π b Z
    (fun e k=>(D.rimAvoid e k).2.2) (fun s k=>(D.spokeAvoid s k).2.2)
  constructor
  · intro x hx y hy
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hPZ x hx y hy
    · obtain ⟨z,_,hx⟩:=Finset.mem_biUnion.mp hx
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
      exact (D.vertexAvoid z k).2 y hy
  · intro x hx y hy hne
    rcases Finset.mem_union.mp hx with hx|hx <;> rcases Finset.mem_union.mp hy with hy|hy
    · exact D.pathSeparated x hx y hy hne
    · obtain ⟨z,_,hy⟩:=Finset.mem_biUnion.mp hy
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hy
      exact fun hc=>D.vertexPathSeparated z k x hx hne.symm ((permutationClose_symm π b _ _).mp hc)
    · obtain ⟨z,_,hx⟩:=Finset.mem_biUnion.mp hx
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
      exact D.vertexPathSeparated z k y hy hne
    · obtain ⟨z,_,hx⟩:=Finset.mem_biUnion.mp hx
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨z',_,hy⟩:=Finset.mem_biUnion.mp hy
      obtain ⟨k',_,rfl⟩:=Finset.mem_image.mp hy
      exact D.vertexSeparated z z' k k' hne

end Oberwolfach
