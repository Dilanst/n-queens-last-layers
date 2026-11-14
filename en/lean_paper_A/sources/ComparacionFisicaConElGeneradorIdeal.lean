import OperadorIdealDelPatronInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

private theorem coe_tasa (P : Prop) [Decidable P] (r : ℝ≥0) :
    (↑(if P then r else (0:ℝ≥0)):ℝ)=filtrarTasa P (r:ℝ) := by
  by_cases h:P <;> simp [h,filtrarTasa]

theorem comparar_deriva_con_ideal {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (e f : Cell n) (o v j l : Bool) (ok : compatible e f) (coh : coherent X) (running : X.failed=false) :
    let row:=choices masas X w (·⁻¹)
    let U:=patronInverso X e f o v j l
    let exceso:=meanN masas row (fun a => indicator U*
      (deathsOn (diez e f) (golpeDelPar e f o v j l a)-1))
    let Q:=operadorInverso X e f o v j l (fun e => (↑(A.birth e/(n:ℝ≥0)^2):ℝ))
      (fun u b => (intensidadIdeal A u b:ℝ))
    let R:=costoLocal X e f o v j l (fun e => (errorDelAtomo A e:ℝ)) (fun u b => (errorDeLinea A u b:ℝ))
    |(↑(meanN masas row (fun a => indicator (patronInverso (next X a) e f o v j l))):ℝ)-
      (indicator U:ℝ)-Q|≤R+(exceso:ℝ) := by
  intro row U exceso Q R
  let a:=fun u b => (tasaDeMarca X w u b:ℝ)
  let r:=fun e => (↑(realAtom masas X w (·⁻¹) e):ℝ)
  obtain ⟨_,_,rr,vv⟩:=A.raw_floors (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _))
  have rem : X.reals+X.virtuals≠0 := by
    intro zero; apply A.running
    change ns masas X.reals+ns masas X.virtuals=0
    rw [ns_real,ns_real,←Nat.cast_add,zero,Nat.cast_zero]
  have tr:=generador_fisico_del_par X w e f o v j l ok coh rr vv running rem
  have sources (e : Cell n) (o : Bool) :
      (bajasFuente X w e U o:ℝ)=sumaFuentes U o e a := by
    unfold bajasFuente sumaFuentes; rw [NNReal.coe_sum]
    exact Finset.sum_congr rfl (fun _ _ => coe_tasa _ _)
  have targets : (bajasDestino X w e f o v j l:ℝ)=sumaMetas X e f o v j l a := by
    unfold bajasDestino sumaMetas; rw [NNReal.coe_add,coe_tasa,coe_tasa]
  have exacto : (↑(meanN masas row (fun a => indicator (patronInverso (next X a) e f o v j l))):ℝ)-
      (indicator U:ℝ)=operadorInverso X e f o v j l r a+(exceso:ℝ) := by
    apply tr.trans
    change _=inserciones X e f o v j l r-sumaFuentes U o e a-sumaFuentes U v f a-sumaMetas X e f o v j l a+(exceso:ℝ)
    unfold inserciones nacimientoCondicionado
    rw [coe_tasa,coe_tasa,sources e o,sources f v,targets]
  have bound : |operadorInverso X e f o v j l r a-Q|≤R := comparar_operadores_inversos X e f o v j l _ _ _ _
  rw [exacto,show operadorInverso X e f o v j l r a+(exceso:ℝ)-Q=(operadorInverso X e f o v j l r a-Q)+exceso by ring]
  exact (abs_add_le _ _).trans (add_le_add bound (le_of_eq (abs_of_nonneg exceso.property)))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparar_deriva_con_ideal
