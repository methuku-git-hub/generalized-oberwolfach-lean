module

public import Oberwolfach.MarkedSpokePathRootProfile
public import Oberwolfach.MarkedSpokeLoadGrouping

@[expose] public section

/-! Supply the root classes for each actual hub-switch caller from the
spoke-path family and the original typed hub degree identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U S:Type} [Fintype S] [Fintype U] [DecidableEq S] [DecidableEq V] [DecidableEq U]

 theorem marked_spoke_hub_root_profiles (m:ℕ) (hm:3≤m)
    (p:S→(Fin m↪V)) (j:S→Bool) (hub:S→U) (ψ:U→U)
    (hdis:∀ s t,s≠t→Disjoint (Finset.univ.image (p s)) (Finset.univ.image (p t)))
    (hbalance:∀ u,(Finset.univ.filter (fun s:{s:S // hub s=u}=>j s.val=false)).card=
      m*(Finset.univ.filter (fun s:{s:S // hub s=u}=>j s.val=true)).card)
    (H₀ HK:V→U→Prop) (htypes:∀ v u,HK v u→¬H₀ v u)
    (hsp:∀ s k,if rootFirstSpokeType m (j s) k.succ then
      HK (p s k) (hub s)∧HK (p s k) (ψ (hub s)) else
      H₀ (p s k) (hub s)∧H₀ (p s k) (ψ (hub s))):
    ∃ ZK ZO:U→Finset V,∀ u,
      ZK u∪ZO u=spokePathHubVertices m p hub u∧Disjoint (ZK u) (ZO u)∧
      (ZO u).card=m*(ZK u).card∧
      (ZK u).card=(Finset.univ.filter (fun s:{s:S // hub s=u}=>j s.val=false)).card∧
      (spokePathHubVertices m p hub u).card=m*Fintype.card {s:S // hub s=u}∧
      (∀ v∈spokePathHubVertices m p hub u,v∈ZK u↔HK v u∧HK v (ψ u))∧
      (∀ v∈spokePathHubVertices m p hub u,v∈ZO u↔H₀ v u∧H₀ v (ψ u)):=by
  have hex:∀ u,∃ ZK ZO:Finset V,
      ZK∪ZO=spokePathHubVertices m p hub u∧Disjoint ZK ZO∧
      ZO.card=m*ZK.card∧
      ZK.card=(Finset.univ.filter (fun s:{s:S // hub s=u}=>j s.val=false)).card∧
      (spokePathHubVertices m p hub u).card=m*Fintype.card {s:S // hub s=u}∧
      (∀ v∈spokePathHubVertices m p hub u,v∈ZK↔HK v u∧HK v (ψ u))∧
      (∀ v∈spokePathHubVertices m p hub u,v∈ZO↔H₀ v u∧H₀ v (ψ u)):=by
    intro u
    have hd:∀ s t:{s:S // hub s=u},s≠t→Disjoint (Finset.univ.image (p s.val)) (Finset.univ.image (p t.val)):=
      fun s t hn=>hdis s.val t.val (fun h=>hn (Subtype.ext h))
    have hh:=marked_spoke_path_root_profile m hm (fun s:{s:S // hub s=u}=>p s.val)
      (fun s=>j s.val) hd (hbalance u) H₀ HK u (ψ u) (fun v=>htypes v u) (by
        intro s k
        have hs:=hsp s.val k
        rw [s.property] at hs
        exact hs)
    exact hh
  choose ZK ZO h using hex
  exact ⟨ZK,ZO,h⟩

end Oberwolfach
