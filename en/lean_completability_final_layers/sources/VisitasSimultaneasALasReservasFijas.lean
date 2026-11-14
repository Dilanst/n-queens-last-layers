import ColaDeVisitasEnHistoriasRegulares
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open Classical
variable {X : Type}

theorem cola_de_menos_visitas_bajo_seguimiento {S : ℕ→X→Atoms ℝ≥0 X}
    (norm : ∀ t x,total masas (S t x)=1) (V : ℕ→X→Prop) (I : ℕ→X→X→Prop)
    (b : ℝ≥0) (b1 : b≤1) (drift : ∀ t x,V t x → b≤avg masas (S t x) (mark masas (I t x)))
    (q t j : ℕ) (x : X) (threshold : (j:ℝ)≤b*q/3) :
    (avg masas (rutas S t q x) (mark masas (fun l=>prefijoRegular V t x l ∧ visitasDeCamino I t x l≤j))).val
      ≤ exp (-(b:ℝ)*q/6) := by
  let bad (l : List X):=prefijoRegular V t x l ∧ visitasDeCamino I t x l≤j
  let W:=descuentoDeVisitas V I t x
  let law:=rutas S t q x
  have bound (l) : mark masas bad l≤(2:ℝ≥0)^j*W l:=by
    by_cases h : bad l
    · dsimp only [W,descuentoDeVisitas]
      rw [if_pos h.1,mark,if_pos h,one_div,inv_pow,←div_eq_mul_inv]
      exact (one_le_div₀ (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) h.2)
    · simp [mark,h,masas]
  have two:=avg_mono masas law (mark masas bad) (fun l=>masas.mul ((2:ℝ≥0)^j) (W l)) (fun i _=>bound _)
  rw [avg_mul] at two
  have mom:=momento_de_visitas norm V I b b1 drift q t x
  have finite : avg masas law (mark masas bad) ≤ (2:ℝ≥0)^j*(1-b/2)^q :=
    two.trans (mul_le_mul_of_nonneg_left mom (zero_le _))
  have pos : b/2≤1:=(div_le_self (zero_le _) (by norm_num)).trans b1
  have coff:=NNReal.coe_le_coe.mpr finite
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_sub pos,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] at coff
  refine coff.trans ?_
  have ep : 2≤exp 1:=by linarith only [Real.add_one_le_exp (1:ℝ)]
  have infb : (0:ℝ)≤1-b/2:=by
    have hb : (b:ℝ)≤1:=by exact_mod_cast b1
    linarith only [hb]
  have base : 1-(b:ℝ)/2≤exp (-(b:ℝ)/2):=by linarith only [Real.add_one_le_exp (-(b:ℝ)/2)]
  have major:=mul_le_mul (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) ep j)
    (pow_le_pow_left₀ infb base q) (pow_nonneg infb _) (by positivity)
  apply major.trans
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,Real.exp_le_exp]
  linarith

theorem cola_simultanea_por_las_raices {n} {S : ℕ→X→Atoms ℝ≥0 X} (norm : ∀ t x,total masas (S t x)=1)
    (V : ℕ→X→Prop) (I : Cell n→ℕ→X→X→Prop) (b : ℝ≥0) (b1 : b≤1)
    (drift : ∀ z t x,V t x → b≤avg masas (S t x) (mark masas (I z t x)))
    (q t j : ℕ) (x : X) (threshold : (j:ℝ)≤b*q/3) :
    (avg masas (rutas S t q x) (mark masas (fun l=>∃ z,prefijoRegular V t x l ∧ visitasDeCamino (I z) t x l≤j))).val
       ≤ (n:ℝ)^2*exp (-(b:ℝ)*q/6) := by
  let bad z (l : List X):=prefijoRegular V t x l ∧ visitasDeCamino (I z) t x l≤j
  let law:=rutas S t q x
  have pt (l : List X) : (mark masas (fun l=>∃ z,bad z l) l).val≤∑ z : Cell n,(mark masas (bad z) l).val:=by
    by_cases h : ∃ z,bad z l
    · obtain ⟨z,hz⟩:=h
      have one:=(Finset.single_le_sum (s:=Finset.univ) (f:=fun e : Cell n=>(mark masas (bad e) l).val)
        (fun e _ => NNReal.coe_nonneg _) (Finset.mem_univ z))
      simpa [mark,hz,show ∃ u,bad u l from ⟨z,hz⟩,masas] using one
    · simp only [mark,h,if_false]
      exact Finset.sum_nonneg (fun _ _=>NNReal.coe_nonneg _)
  have p:=media_mono law (fun l=>(mark masas (fun ls=>∃ z,bad z ls) l).val) (fun l=>∑ z : Cell n,(mark masas (bad z) l).val) (fun i _=>pt i.2)
  have sum:=media_de_suma_finita law Finset.univ (fun (z : Cell n) l=>(mark masas (bad z) l).val)
  have per (z : Cell n) : media law (fun l=>(mark masas (bad z) l).val)≤exp (-(b:ℝ)*q/6):=
    (media_coe law (mark masas (bad z))).le.trans
      (cola_de_menos_visitas_bajo_seguimiento norm V (I z) b b1 (drift z) q t j x threshold)
  have all:=Finset.sum_le_sum (s:=Finset.univ) (fun (z : Cell n) _=>per z)
  have finish:=(media_coe law (mark masas (fun l=>∃ z,bad z l))).symm.le.trans (p.trans (sum.le.trans all))
  simpa [law,bad,Cell,pow_two,mul_assoc] using finish
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_simultanea_por_las_raices
#print axioms ArticuloA.Historias.cola_de_menos_visitas_bajo_seguimiento
