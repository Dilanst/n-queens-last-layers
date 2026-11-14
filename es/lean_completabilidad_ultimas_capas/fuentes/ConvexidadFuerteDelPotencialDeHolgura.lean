import CotasEscalaresDesdeLasMediasGeometricas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def potencialDeHolgura (h : ℝ) := h+exp (-h)-1

theorem punto_medio_del_potencial {H u v : ℝ} (uh : u≤H) (vh : v≤H) :
    exp (-H)*(u-v)^2 ≤ 8*((potencialDeHolgura u+potencialDeHolgura v)/2-potencialDeHolgura ((u+v)/2)) := by
  let a:=exp (-u/2); let b:=exp (-v/2)
  have law (y z : ℝ) (yz : y≤z) (zh : z≤H) :
      exp (-H/2)*((z-y)/2)≤exp (-y/2)-exp (-z/2) := by
    have k:=mul_le_mul_of_nonneg_right (Real.add_one_le_exp ((z-y)/2)) (exp_pos (-z/2)).le
    rw [←exp_add,show (z-y)/2+-z/2= -y/2 by ring] at k
    have le:=mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith only [zh] : -H/2≤ -z/2))
      (show 0≤(z-y)/2 by linarith only [yz])
    linarith only [k,le]
  have bd : exp (-H/2)*|u-v|≤2*|a-b| := by
    rcases le_total u v with h|h
    · have sub:=law u v h vh
      have ord : b≤a := exp_le_exp.mpr (by linarith only [h] : -v/2≤ -u/2)
      rw [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonneg (sub_nonneg.mpr ord)]
      dsimp [a,b]; linarith only [sub]
    · have sub:=law v u h uh
      have ord : a≤b := exp_le_exp.mpr (by linarith only [h] : -u/2≤ -v/2)
      rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonpos (sub_nonpos.mpr ord)]
      dsimp [a,b]; linarith only [sub]
  have hsquare:=pow_le_pow_left₀ (mul_nonneg (exp_pos _).le (abs_nonneg _)) bd 2
  have ep (t : ℝ) : (exp (-t/2))^2=exp (-t) := by rw [sq,←exp_add]; congr 1; ring
  have ab : a*b=exp (-((u+v)/2)) := by dsimp only [a,b]; rw [←exp_add]; congr 1; ring
  rw [mul_pow,mul_pow,sq_abs,sq_abs,ep] at hsquare
  have ea : a^2=exp (-u) := ep u
  have eb : b^2=exp (-v) := ep v
  unfold potencialDeHolgura
  nlinarith only [hsquare,ea,eb,ab]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.punto_medio_del_potencial
