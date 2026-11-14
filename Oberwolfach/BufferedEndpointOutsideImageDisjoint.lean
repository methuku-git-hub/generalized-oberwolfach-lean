module

public import Oberwolfach.BufferedComplementImage
public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! Complement images outside all reserved paths avoid images of their
source endpoints under the same injective complement embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_outside_image_disjoint_endpoints
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (e:I→X) (heA:∀i,e i∈bufferedPathFullDomain n inner)
    (heD:∀i,e i∉bufferedPathStrictInterior n inner)
    (b:I→V) (hb:∀i,fC ⟨e i,heD i⟩=b i):
    Disjoint (outsideBufferedPathImage n inner fC) (Finset.univ.image b):=by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvz hvb
  obtain ⟨z,hz,hzv⟩:=Finset.mem_image.mp hvz
  obtain ⟨i,_,hbv⟩:=Finset.mem_image.mp hvb
  have heq:fC z=fC ⟨e i,heD i⟩:=hzv.trans (hbv.symm.trans (hb i).symm)
  have heq':z.val=e i:=congrArg Subtype.val (fC.injective heq)
  have hzA:z.val∉bufferedPathFullDomain n inner:=(Finset.mem_filter.mp hz).2
  exact hzA (heq' ▸ heA i)
end Oberwolfach
