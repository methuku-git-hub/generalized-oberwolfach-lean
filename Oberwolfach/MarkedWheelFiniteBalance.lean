module

public import Oberwolfach.MarkedFiniteRemainder
public import Oberwolfach.MarkedBoundaryArcIndices

@[expose] public section

/-! The four integer divisibility identities for the actual finite arc and
spoke sets of a marked wheel. The marked spoke is recovered from the two
disjoint host spoke relations, not from an untyped incidence count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

def markedWheelArcs (W:MarkedWheel tail head ktail khead m π b H₀ HK):Finset (E⊕T):=
  Finset.univ.image (markedCycleTypedEdge tail head ktail khead m π b W.1)

def markedWheelSpokePairs (W:MarkedWheel tail head ktail khead m π b H₀ HK):Finset (V×U):=
  Finset.univ.image (fun i=>(W.1.val i,W.2.val))

theorem finite_injective_image_filter_card {A B:Type} [Fintype A] [DecidableEq B]
    (f:A→B) (hf:Function.Injective f) (p:B→Prop) [DecidablePred p]:
    ((Finset.univ.image f).filter p).card=(Finset.univ.filter (fun a=>p (f a))).card:=by
  rw [Finset.filter_image,Finset.card_image_of_injective _ hf]

omit [Fintype V] [Fintype U] in
theorem markedWheel_finite_divisible
    (hH:∀ v u,¬(H₀ v u∧HK v u)) (W:MarkedWheel tail head ktail khead m π b H₀ HK):
    MarkedRemainderDivisible tail head ktail khead HK (markedWheelArcs W) (markedWheelSpokePairs W) m:=by
  let C:=W.1.val
  let f:=markedCycleTypedEdge tail head ktail khead m π b W.1
  let g:=fun i:Fin (m+1)=>(C i,W.2.val)
  have hf:Function.Injective f:=markedCycleTypedEdge_injective tail head ktail khead m π b W.1
  have hC:Function.Injective C:=permutationSeparated_injective π b W.1.val W.1.property.1
  have hg:Function.Injective g:=fun i j hij=>hC (congrArg Prod.fst hij)
  have ht (i:Fin (m+1)):Sum.elim tail ktail (f i)=C i:=
    (markedCycleTypedEdge_endpoints tail head ktail khead m π b W.1 i).1
  have hh (i:Fin (m+1)):Sum.elim head khead (f i)=C (finRotate (m+1) i):=
    (markedCycleTypedEdge_endpoints tail head ktail khead m π b W.1 i).2
  have htype (i:Fin (m+1)):markedArcType (f i)=true↔i=Fin.last m:=by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp [f,markedCycleTypedEdge,markedArcType]
    · simp [f,markedCycleTypedEdge,markedArcType]
  have hs (i:Fin (m+1)):HK (C i) W.2.val↔i=0:=by
    refine Fin.cases ?_ (fun j=>?_) i
    · exact iff_of_true W.2.property.1 rfl
    · have hnot:¬HK (C j.succ) W.2.val:=fun hk=>hH _ _ ⟨W.2.property.2 j,hk⟩
      simp [hnot]
  have ha (p:E⊕T→Prop) [DecidablePred p]:((markedWheelArcs W).filter p).card=
      (Finset.univ.filter (fun i=>p (f i))).card:=finite_injective_image_filter_card f hf p
  have hz (p:V×U→Prop) [DecidablePred p]:((markedWheelSpokePairs W).filter p).card=
      (Finset.univ.filter (fun i=>p (g i))).card:=finite_injective_image_filter_card g hg p
  have hrot (v:V):(Finset.univ.filter (fun i:Fin (m+1)=>C (finRotate (m+1) i)=v)).card=
      (Finset.univ.filter (fun i:Fin (m+1)=>C i=v)).card:=by
    convert filter_card_reindex_equiv (finRotate (m+1)) (fun i=>C i=v) using 1 <;> congr!
  constructor
  · intro v
    rw [ha,ha]
    simpa only [ht,hh] using hrot v
  · intro v
    rw [ha,hz]
    simpa only [g,hh] using hrot v
  · intro v
    rw [ha,hz]
    simp only [g,hh,htype,hs]
    have hleft:(Finset.univ.filter (fun i:Fin (m+1)=>C (finRotate (m+1) i)=v∧i=Fin.last m))=
        if C 0=v then {Fin.last m} else ∅:=by
      ext i;simp [and_comm];aesop
    have hright:(Finset.univ.filter (fun i:Fin (m+1)=>C i=v∧i=0))=
        if C 0=v then {0} else ∅:=by
      ext i;simp [and_comm];aesop
    rw [hleft,hright]
    split_ifs <;> simp
  · intro u
    rw [hz,hz]
    simp only [g,hs]
    by_cases hu:W.2.val=u
    · simp only [hu,true_and]
      simp [Finset.filter_ne',Finset.filter_eq']
    · simp [hu]

end Oberwolfach
