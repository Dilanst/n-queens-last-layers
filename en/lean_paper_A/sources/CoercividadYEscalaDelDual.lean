import RepresentantesDeLaCajaDual
import IntegralesDeLaProyeccionUniforme
import CompetidoresBorelDeLaCajaDual
import JensenEnLasMedidasFisicas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

local instance : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
local instance : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance
def masaDePotenciales {H : ℝ} (u : CajaDual H) := ∑ i : Fin 4,∫ s,campoDual u i s ∂marginalRef i

theorem log_particion_inferior {H : ℝ} (hp : 0≤H) (u : CajaDual H) :
    -masaDePotenciales u≤log (particionDual u) := by
  have bd i s : |campoDual u i s|≤H := (abs_of_nonneg (campo_dual_acotado hp u i s).1).le.trans (campo_dual_acotado hp u i s).2
  have term i : Integrable (fun z=>campoDual u i (coord i z)) cuadrado :=
    integral_acotada_dual ((campo_dual_medible u i).comp (coord_medible i)) (fun z=>bd i _)
  have si : Integrable (sumaDual u) cuadrado := integrable_finset_sum _ (fun i _=>term i)
  have pos:= (exp_pos _).trans_le (particion_dual_acotada hp u).1
  have j:=jensen_log_en_una_probabilidad (t:=fun z=>exp (-sumaDual u z))
    (Eventually.of_forall (fun z=>exp_pos _)) (densidad_dual_integrable hp u) (by simpa only [log_exp] using si.neg) pos
  simp only [log_exp,integral_neg] at j
  have l:=Real.log_le_log (exp_pos _) j
  rw [log_exp] at l
  have b : (∫ z,sumaDual u z ∂cuadrado)≤masaDePotenciales u := by
    unfold sumaDual masaDePotenciales; rw [integral_finset_sum _ (fun i _=>term i)]
    exact Finset.sum_le_sum (fun i _=>integral_del_levantamiento_acotado i (campo_dual_medible u i) (bd i) (fun s=>(campo_dual_acotado hp u i s).1))
  exact (neg_le_neg b).trans l

theorem cota_inferior_funcional {H : ℝ} (hp : 0≤H) {d : ℝ} (dn : 0≤d) (u : CajaDual H) :
    (1-d)*masaDePotenciales u-6≤funcionalDual d u := by
  have val i : (∫ s,campoDual u i s ∂marginalRef i)-(marginalRef i).real univ≤costoDual u i := by
    have hi : Integrable (campoDual u i) (marginalRef i) := integral_acotada_dual (campo_dual_medible u i)
      (fun s=>(abs_of_nonneg (campo_dual_acotado hp u i s).1).le.trans (campo_dual_acotado hp u i s).2)
    have ord:=integral_mono (hi.sub (integrable_const (1:ℝ))) (costo_dual_integrable hp u i)
      (fun s=>by change campoDual u i s-1≤campoDual u i s+exp (-campoDual u i s)-1; linarith [exp_pos (-campoDual u i s)])
    change (∫ s,campoDual u i s-1 ∂marginalRef i)≤_ at ord
    simpa only [integral_sub hi (integrable_const _),integral_const,smul_eq_mul,mul_one] using ord
  have sum:=Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 4)))=>val i)
  have six : (∑ i : Fin 4,(marginalRef i).real univ)=6 := by norm_num [Fin.sum_univ_four,marginalRef,Measure.real,Real.volume_Ioc]
  rw [Finset.sum_sub_distrib,six] at sum
  have entropy:=mul_le_mul_of_nonneg_left (log_particion_inferior hp u) dn
  change masaDePotenciales u-6≤∑ i,costoDual u i at sum
  unfold funcionalDual; linarith only [sum,entropy]

theorem cota_de_escala_en_el_subnivel {H d : ℝ} (hp : 0≤H) (dp : 0<d) (dt : d<1) (u : CajaDual H)
    (low : funcionalDual d u≤0) : d/particionDual u≤d*exp (6/(1-d)) := by
  have b:=cota_inferior_funcional hp dp.le u
  have mass : masaDePotenciales u≤6/(1-d) := (le_div_iff₀ (sub_pos.mpr dt)).mpr (by linarith only [b,low])
  have l:=log_particion_inferior hp u
  have pos:=(exp_pos _).trans_le (particion_dual_acotada hp u).1
  have ex:=exp_le_exp.mpr (show -log (particionDual u)≤6/(1-d) by linarith)
  rw [exp_neg,exp_log pos] at ex
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left ex dp.le

theorem existe_competidor_de_valor_cero {H : ℝ} (hp : 0≤H) (d : ℝ) : ∃ u : CajaDual H,funcionalDual d u=0 := by
  obtain ⟨v,eq⟩:=competidor_de_campos_borel (H:=H) (fun _ _=>0) (fun _=>measurable_const) (fun _ _=>⟨le_rfl,hp⟩)
  have c i : costoDual v i=0 := by
    unfold costoDual; have t:=integral_congr_ae ((eq i).fun_comp potencialDeHolgura)
    simpa [Function.comp_def,potencialDeHolgura] using t
  have ss:=suma_dual_sobre_representantes v (fun _=>measurable_const) eq
  have Z : particionDual v=1 := by
    unfold particionDual; have t:=integral_congr_ae (ss.fun_comp (fun y=>exp (-y)))
    simpa [Function.comp_def] using t
  exact ⟨v,by simp [funcionalDual,c,Z]⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.log_particion_inferior
#print axioms ArticuloA.Historias.cota_inferior_funcional
#print axioms ArticuloA.Historias.cota_de_escala_en_el_subnivel
#print axioms ArticuloA.Historias.existe_competidor_de_valor_cero
