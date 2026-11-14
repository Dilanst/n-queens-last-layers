import BalanceDeLaRamaEnTodasLasRaices
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
open Set MeasureTheory Filter
open scoped Interval NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section

def pesoExtendido (p : FactoresContinuos) (z : ℝ×ℝ) : ℝ :=
  ∏ i : Fin 4,(factorF p i (recorte i (coord i z)):ℝ)

theorem extension_continua_del_peso {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L) :
    Continuous (pesoExtendido p) := by
  apply continuous_finset_prod; intro i _
  have base:=continua_de_cota lp (regular_familia sp i).oscilacion
  have comp : Continuous (coord i) := by
    fin_cases i; exacts [continuous_fst,continuous_snd,continuous_fst.sub continuous_snd,continuous_fst.add continuous_snd]
  exact (base.comp_continuous (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)).comp comp

theorem extension_coincide {p : FactoresContinuos} {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    pesoExtendido p (r,c)=pesoContinuo p r c := by
  unfold pesoExtendido
  have eq (i : Fin 4) := recorte_fijo i (coordenadas_en_dominio (z:=(r,c)) ⟨hr,hc⟩ i)
  simp_rw [eq]
  rw [Fin.prod_univ_four]; rfl

private theorem segmento {s t : ℝ} (hs : s∈Icc (-1:ℝ) 1) (ht : t∈Icc 0 (1-|s|)) :
    max s 0+t∈unidadCerrada ∧ max (-s) 0+t∈unidadCerrada ∧ 1-(max (-s) 0+t)∈unidadCerrada := by
  obtain ⟨low,high⟩:=hs
  obtain ⟨non,len⟩:=ht
  by_cases pos : 0≤s
  · rw [abs_of_nonneg pos] at len
    simp only [max_eq_left pos,max_eq_right (neg_nonpos.mpr pos),zero_add,unidadCerrada,mem_Icc]
    exact ⟨⟨by linarith,by linarith⟩,⟨non,by linarith⟩,⟨by linarith,by linarith⟩⟩
  · have neg := le_of_not_ge pos
    rw [abs_of_nonpos neg] at len
    simp only [max_eq_right neg,max_eq_left (neg_nonneg.mpr neg),zero_add,unidadCerrada,mem_Icc]
    exact ⟨⟨non,by linarith⟩,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

private theorem oblicua_continua {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L) (anti : Bool) :
    ContinuousOn (fun s => integralDesplazada p s anti) (Icc (-1:ℝ) 1) := by
  let xy (s t : ℝ) := (max s 0+t,if anti then 1-(max (-s) 0+t) else max (-s) 0+t)
  let F (s t : ℝ) := pesoExtendido p (xy s t)
  have comp : Continuous (Function.uncurry F) := by
    apply (extension_continua_del_peso sp lp).comp
    cases anti <;> dsimp [xy] <;> fun_prop
  have cg := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ:=volume)
    (a₀:=(0:ℝ)) (s:=fun s : ℝ => 1-|s|) comp (continuous_const.sub continuous_id.abs)
  apply cg.continuousOn.congr
  intro s hs
  apply intervalIntegral.integral_congr; intro t ht
  rw [uIcc_of_le (sub_nonneg.mpr (abs_le.mpr hs))] at ht
  have mem:=segmento hs ht
  exact (extension_coincide mem.1 (by cases anti <;> first | exact mem.2.1 | exact mem.2.2)).symm

theorem integral_fisica_continua {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L) (i : Fin 4) :
    ContinuousOn (integralFisica p i) (rangoF i) := by
  have cont:=extension_continua_del_peso sp lp
  fin_cases i
  · have row:=intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=volume)
      (f:=fun s t => pesoExtendido p (s,t)) cont 0 1
    apply row.continuousOn.congr; intro s hs; apply intervalIntegral.integral_congr; intro t ht
    rw [uIcc_of_le zero_le_one] at ht; exact (extension_coincide hs ht).symm
  · have col:=intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=volume)
      (f:=fun s t => pesoExtendido p (t,s)) (cont.comp continuous_swap) 0 1
    apply col.continuousOn.congr; intro s hs; apply intervalIntegral.integral_congr; intro t ht
    rw [uIcc_of_le zero_le_one] at ht; exact (extension_coincide ht hs).symm
  · exact oblicua_continua sp lp false
  · apply (oblicua_continua sp lp true).comp (continuous_id.sub continuous_const).continuousOn
    intro s hs
    change s∈Icc (0:ℝ) 2 at hs
    change s-1∈Icc (-1:ℝ) 1
    exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem euler_puntual_de_fibras_ae {p κ M L b} (sp : ControlEspacial p κ M L) (lp : 0≤L)
    (x : ℝ≥0) (i : Fin 4)
    (ae : ∀ᵐ t ∂marginalRef i,b*integralFisica p i t=1-holguraLinea p x i t) :
    ∀ t∈rangoF i,b*integralFisica p i t=1-holguraLinea p x i t := by
  have ndeg : extremoIzq i≠extremoDer i := by fin_cases i <;> norm_num [extremoIzq,extremoDer]
  have ref : marginalRef i=volume.restrict (rangoF i) := by
    have eq : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
    rw [eq]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  rw [ref] at ae
  exact fun _ ht => Measure.eqOn_Icc_of_ae_eq (μ:=volume) ndeg ae
    (continuousOn_const.mul (integral_fisica_continua sp lp i))
    (continuousOn_const.sub (continuousOn_const.mul (continua_de_cota lp (regular_familia sp i).oscilacion))) ht
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.euler_puntual_de_fibras_ae
