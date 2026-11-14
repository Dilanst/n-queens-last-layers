import RepresentantesDeLaCajaDual
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem competidor_de_campos_borel {H : ℝ} (f : Fin 4→ℝ→ℝ) (fm : ∀ i,Measurable (f i))
    (fb : ∀ i s,f i s∈Icc 0 H) : ∃ v : CajaDual H,∀ i,campoDual v i=ᵐ[marginalRef i] f i := by
  have lp i : MemLp (f i) 2 (marginalRef i) := MemLp.of_bound (fm i).aestronglyMeasurable H
    (Eventually.of_forall (fun s=>by rw [Real.norm_eq_abs,abs_of_nonneg (fb i s).1]; exact (fb i s).2))
  let a : PotencialesL2:=fun i=>(lp i).toLp (f i)
  have ca : a∈cajaDePotenciales H := by
    intro i; filter_upwards [(lp i).coeFn_toLp] with s eq; rw [show a i s=f i s from eq]; exact fb i s
  exact ⟨⟨a,ca⟩,fun i=>(campo_dual_ae ⟨a,ca⟩ i).trans (lp i).coeFn_toLp⟩

theorem suma_dual_sobre_representantes {H : ℝ} (v : CajaDual H) {f : Fin 4→ℝ→ℝ}
    (fm : ∀ i,Measurable (f i)) (eq : ∀ i,campoDual v i=ᵐ[marginalRef i] f i) :
    sumaDual v=ᵐ[cuadrado] (fun z=>∑ i : Fin 4,f i (coord i z)) := by
  have each i:=etiqueta_cumple_en_el_tablero i (S:={s | campoDual v i s=f i s})
    (measurableSet_eq_fun (campo_dual_medible v i) (fm i)) (eq i)
  filter_upwards [each 0,each 1,each 2,each 3] with z h0 h1 h2 h3
  simp only [sumaDual,Fin.sum_univ_four]
  change campoDual v 0 (coord 0 z)=_ at h0
  change campoDual v 1 (coord 1 z)=_ at h1
  change campoDual v 2 (coord 2 z)=_ at h2
  change campoDual v 3 (coord 3 z)=_ at h3
  rw [h0,h1,h2,h3]

def promedioDeCampos {H : ℝ} (u v : CajaDual H) i s := (campoDual u i s+campoDual v i s)/2
theorem promedio_en_la_caja {H : ℝ} (hp : 0≤H) (u v : CajaDual H) :
    ∃ m : CajaDual H,∀ i,campoDual m i=ᵐ[marginalRef i] promedioDeCampos u v i := by
  apply competidor_de_campos_borel _ (fun i=>((campo_dual_medible u i).add (campo_dual_medible v i)).div_const 2)
  intro i s
  have a:=campo_dual_acotado hp u i s
  have b:=campo_dual_acotado hp v i s
  exact ⟨by linarith [a.1,b.1],by linarith [a.2,b.2]⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.competidor_de_campos_borel
#print axioms ArticuloA.Historias.suma_dual_sobre_representantes
#print axioms ArticuloA.Historias.promedio_en_la_caja
