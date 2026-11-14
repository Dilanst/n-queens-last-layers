import DerivaFisicaDeLosSoportes
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

private theorem sin_cuota {n} (X : State n) : quota masas X (·⁻¹) 0=0 := by
  unfold quota; change _*0=0; exact mul_zero _

theorem hijo_regular_con_masa {n} {X : State n} {w : ColorWeights ℝ≥0} (A : Region masas X w (·⁻¹))
    (t : ℕ) (ok : X.failed=false) (i : ℝ≥0×State n) (mem : i∈kernel masas w (·⁻¹) t X) (nz : i.1≠0) :
    i.2.failed=false ∧ i.2.reals+i.2.virtuals+1=X.reals+X.virtuals := by
  obtain ⟨_,_,rr,vv⟩:=A.raw_floors (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _))
  have num : X.reals+X.virtuals≠0 := by
    intro eq
    apply A.running
    change ns masas X.reals + ns masas X.virtuals=0
    rw [ns_real,ns_real,←Nat.cast_add,eq,Nat.cast_zero]
  rw [kernel_is_row masas X t w _ ok num,regular_row masas X w (·⁻¹) rr vv] at mem
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp mem
  rcases List.mem_append.mp ha with real | virt
  · obtain ⟨c,_,rfl⟩:=List.mem_map.mp real
    have ap : X.reals≠0 := by
      intro eq; apply nz
      change realAtom masas X w (·⁻¹) c=0
      unfold realAtom; rw [eq,sin_cuota]; exact zero_mul _
    exact ⟨ok,by change (X.reals-1)+X.virtuals+1=_; omega⟩
  · obtain ⟨g,_,rfl⟩:=List.mem_map.mp virt
    have ap : X.virtuals≠0 := by
      intro eq; apply nz
      change virtAtom masas X w (·⁻¹) g=0
      unfold virtAtom; rw [eq,sin_cuota]; exact zero_mul _
    exact ⟨ok,by change X.reals+(X.virtuals-1)+1=_; omega⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.hijo_regular_con_masa
