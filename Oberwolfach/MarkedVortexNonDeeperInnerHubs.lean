module

public import Oberwolfach.MarkedVortexNonDeeperHubEmbedding

@[expose] public section
/-! Identify the next active hubs inside the parent with its deeper hubs
removed, as required by the level-record hub image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexNonDeeperHubToParent (i:ℕ):markedVortexNonDeeperHubType Q i ↪ markedVortexHubType Q i:=
  ⟨Subtype.val,Subtype.val_injective⟩

def markedVortexInnerNonDeeperHubs (i:ℕ):Finset (markedVortexNonDeeperHubType Q i):=
  Finset.univ.filter (fun u=>u.val∈markedVortexInnerHubs Q i)

theorem marked_vortex_inner_nondeeper_hubs_image (i:ℕ):
    (markedVortexInnerNonDeeperHubs Q i).image (markedVortexNonDeeperHubToParent Q i)=
      markedVortexInnerHubs Q i\markedVortexDeeperHubs Q i:=by
  ext u
  simp only [Finset.mem_image,markedVortexInnerNonDeeperHubs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,hxu⟩
    have hnot:x.val∉markedVortexDeeperHubs Q i:=(Finset.mem_sdiff.mp x.property).2
    change x.val=u at hxu
    subst u
    exact ⟨hx,hnot⟩
  · rintro ⟨hi,hd⟩
    let x:markedVortexNonDeeperHubType Q i:=⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hd⟩⟩
    exact ⟨x,hi,rfl⟩
end Oberwolfach
