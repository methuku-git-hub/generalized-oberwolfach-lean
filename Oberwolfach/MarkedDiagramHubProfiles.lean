module

public import Oberwolfach.MarkedInitialDiagramSupport
public import Oberwolfach.MarkedSpokeProfilesFromWheels
public import Oberwolfach.MarkedActiveHubLoads

@[expose] public section

/-! The old hubs determine the switch index set and its root classes. Their
sizes, types, separation and disjointness follow from the constructed paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {src dst:A→V} {row:S→V} {φ:V→V} {u u':S→U} {jr:A→Bool} {js:S→Bool}
    {W Z:Finset V} {B:Finset U}

theorem marked_diagram_hub_profiles
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B)
    (ψ:U→U) (hu':∀ s,u' s=ψ (u s)) (htypes:∀ v u,HK v u→¬H₀ v u)
    (hbal:∀ z,(Finset.univ.filter (fun s:{s:S // u s=z}=>js s.val=false)).card=
      (l+4)*(Finset.univ.filter (fun s:{s:S // u s=z}=>js s.val=true)).card):
    ∃ ZK ZO:U→Finset V,
      (∀ z,ZK z∪ZO z=spokePathHubVertices (l+4) D.ps u z∧
        Disjoint (ZK z) (ZO z)∧(ZO z).card=(l+4)*(ZK z).card∧(ZK z).card≤Fintype.card S∧
        (∀ x∈ZK z,HK x z∧HK x (ψ z))∧(∀ x∈ZO z,H₀ x z∧H₀ x (ψ z)))∧
      (∀ z,ZK z∪ZO z⊆markedDiagramRows D)∧
      (∀ z z',z≠z'→Disjoint (ZK z∪ZO z) (ZK z'∪ZO z'))∧
      (∀ z,∀ x∈ZK z∪ZO z,∀ y∈ZK z∪ZO z,x≠y→¬PermutationClose π b x y):=by
  obtain ⟨ZK,ZO,hZ⟩:=marked_spoke_profiles_from_wheels (l+4) (by omega) D.ps js row (fun s=>φ (row s)) u ψ
    D.SC D.SD D.spokeCoordinates D.imageSpokeCoordinates (fun s=>(D.spokeHubs s).1)
    (fun s=>(D.spokeHubs s).2.trans (hu' s)) D.spokeDisjoint hbal htypes
  have hsub:∀ z,spokePathHubVertices (l+4) D.ps u z⊆
      markedPathUnion (l+3) (l+4) (fun e=>D.pr e) (fun s=>D.ps s):=by
    intro z v hv
    obtain ⟨s,_,hv⟩:=Finset.mem_biUnion.mp hv
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
    exact markedPathUnion_spoke _ _ _ _ s.val k
  refine ⟨ZK,ZO,?_,?_,?_,?_⟩
  · intro z
    exact ⟨(hZ z).1,(hZ z).2.1,(hZ z).2.2.1,(hZ z).2.2.2.1,(hZ z).2.2.2.2.2⟩
  · intro z;rw [(hZ z).1]
    exact (hsub z).trans (marked_diagram_rows_path D)
  · intro z z' hne;rw [(hZ z).1,(hZ z').1]
    exact spokePathHubVertices_disjoint (l+4) D.ps u D.spokeDisjoint z z' hne
  · intro z x hx y hy hne
    rw [(hZ z).1] at hx hy
    exact D.pathSeparated x (hsub z hx) y (hsub z hy) hne

end Oberwolfach
