import CompetidoresBorelDeLaCajaDual
import ControlIntegralDeLaDistanciaDual
import ConvexidadDelLogaritmoDeParticion
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem brecha_por_etiqueta {H : ℝ} (hp : 0≤H) (u v m : CajaDual H)
    (avg : ∀ i,campoDual m i=ᵐ[marginalRef i] promedioDeCampos u v i) (i : Fin 4) :
    exp (-H)*dist (u.val i) (v.val i)^2≤8*((costoDual u i+costoDual v i)/2-costoDual m i) := by
  let μ:=marginalRef i
  let U:=fun s=>potencialDeHolgura (campoDual u i s)
  let V:=fun s=>potencialDeHolgura (campoDual v i s)
  let M:=fun s=>potencialDeHolgura (campoDual m i s)
  have ui:=costo_dual_integrable hp u i; have vi:=costo_dual_integrable hp v i; have mi:=costo_dual_integrable hp m i
  have comp:=integral_mono_ae ((integrable_cuadrado_dual hp u v i).const_mul (exp (-H)))
    ((((ui.add vi).div_const 2).sub mi).const_mul 8) (by
      filter_upwards [avg i] with s eq
      change exp (-H)*(campoDual u i s-campoDual v i s)^2≤8*((U s+V s)/2-M s)
      dsimp only [M]; rw [eq]
      exact punto_medio_del_potencial (campo_dual_acotado hp u i s).2 (campo_dual_acotado hp v i s).2)
  change (∫ s,exp (-H)*(campoDual u i s-campoDual v i s)^2 ∂μ)≤∫ s,8*((U s+V s)/2-M s) ∂μ at comp
  have midI : Integrable (fun s=>(U s+V s)/2) μ := (ui.add vi).div_const 2
  have Uin : Integrable U μ := ui
  have Vin : Integrable V μ := vi
  have Min : Integrable M μ := mi
  rw [integral_const_mul,integral_const_mul,integral_sub midI Min,integral_div,integral_add Uin Vin] at comp
  rw [distancia_L2_por_representantes (u.val i) (v.val i) (campo_dual_ae u i) (campo_dual_ae v i)]; exact comp

theorem particion_dual_en_el_promedio {H : ℝ} (hp : 0≤H) (u v m : CajaDual H)
    (avg : ∀ i,campoDual m i=ᵐ[marginalRef i] promedioDeCampos u v i) :
    log (particionDual m)≤(log (particionDual u)+log (particionDual v))/2 := by
  have ae:=suma_dual_sobre_representantes m (fun i=>((campo_dual_medible u i).add (campo_dual_medible v i)).div_const 2) avg
  have eq : (fun z=>exp (-sumaDual m z))=ᵐ[cuadrado] (fun z=>exp ((-sumaDual u z+-sumaDual v z)/2)) := by
    filter_upwards [ae] with z hz; rw [hz]; congr 1
    simp only [sumaDual,promedioDeCampos,Fin.sum_univ_four]; ring
  have pos (w : CajaDual H) : 0<particionDual w := (exp_pos _).trans_le (particion_dual_acotada hp w).1
  have val : particionDual m=(∫ z,exp ((-sumaDual u z+-sumaDual v z)/2) ∂cuadrado) := integral_congr_ae eq
  rw [val]
  exact convexidad_de_log_particion_por_punto_medio _ _ (densidad_dual_integrable hp u) (densidad_dual_integrable hp v)
    ((densidad_dual_integrable hp m).congr eq) (pos u) (pos v) (val ▸ pos m)

theorem brecha_del_funcional_dual {H d : ℝ} (hp : 0≤H) (dn : 0≤d) (u v m : CajaDual H)
    (avg : ∀ i,campoDual m i=ᵐ[marginalRef i] promedioDeCampos u v i) :
    dist u v^2≤(8/exp (-H))*((funcionalDual d u+funcionalDual d v)/2-funcionalDual d m) := by
  have b:=Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 4)))=>brecha_por_etiqueta hp u v m avg i)
  have pp:=mul_le_mul_of_nonneg_left (particion_dual_en_el_promedio hp u v m avg) dn
  have largest : ∃ i : Fin 4,dist (u.val i) (v.val i)=dist u v := by
    by_cases same : u=v
    · subst v; exact ⟨0,by simp⟩
    · have h : 0<dist u.val v.val := dist_pos.mpr (fun eq=>same (Subtype.ext eq))
      exact ((dist_pi_eq_iff h).mp rfl).1
  obtain ⟨j,eq⟩:=largest
  have singleton:=Finset.single_le_sum (f:=fun i=>exp (-H)*dist (u.val i) (v.val i)^2)
    (fun i _=>mul_nonneg (exp_pos _).le (sq_nonneg _)) (Finset.mem_univ j)
  dsimp only at singleton
  rw [eq] at singleton
  have all:=singleton.trans b
  simp only [Fin.sum_univ_four] at all
  rw [div_mul_eq_mul_div]; apply (le_div_iff₀ (exp_pos (-H))).mpr
  simp only [funcionalDual,Fin.sum_univ_four]; linarith only [all,pp]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.brecha_por_etiqueta
#print axioms ArticuloA.Historias.particion_dual_en_el_promedio
#print axioms ArticuloA.Historias.brecha_del_funcional_dual
