import InnovacionesDetenidasEnLasHistoriasDeG
import MediaDeUnaSumaDeMarcas
namespace ArticuloA.Historias
open RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

private theorem union_sobre_una_misma_ley {I X : Type} [Fintype I] (row : Atoms ℝ≥0 X)
    (E : I→X→Prop) {v : ℝ} (each : ∀ i,(avg masas row (mark masas (E i))).val≤v) :
    (avg masas row (mark masas (fun x=>∃ i,E i x))).val≤(Fintype.card I:ℝ)*v := by
  let flag:=fun i x=>(mark masas (E i) x).val
  rw [←media_coe]
  have le:=media_mono row (fun x=>(mark masas (fun y=>∃ i,E i y) x).val)
    (fun x=>∑ i,flag i x) (fun a _=>by
      by_cases exi : ∃ i,E i a.2
      · obtain ⟨i,hi⟩:=exi
        have lower:=Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>flag j a.2)
          (fun j _=>NNReal.coe_nonneg _) (Finset.mem_univ i)
        simpa only [flag,mark,if_pos hi,if_pos (show ∃ j,E j a.2 from ⟨i,hi⟩)] using lower
      · simp only [mark,if_neg exi]
        exact Finset.sum_nonneg (fun _ _=>NNReal.coe_nonneg _))
  rw [media_de_suma_finita] at le
  apply le.trans
  calc _ ≤ ∑ _i : I,v:=Finset.sum_le_sum (fun i _=>(media_coe row (mark masas (E i))).le.trans (each i))
       _ = _:=by simp

theorem innovaciones_simultaneas_de_G {n q} {I : Type} [Fintype I] (v : Cell n→ℝ≥0)
    (ok : I→ℕ→EstadoGuiado n→Prop) (Y : I→ℕ→EstadoGuiado n→EstadoGuiado n→ℝ)
    (B : I→ℝ) (bp : ∀ i,0<B i) (qp : 0<q)
    (jump : ∀ i t x,ok i t x→∀ b∈pasoDeG v q t x,
        |Y i t x b.2-media (pasoDeG v q t x) (Y i t x)|≤B i)
    (x : EstadoGuiado n) (a : ℝ) (ap : 0≤a) (scale : a≤sqrt (q:ℝ)) :
    let D:=fun i=>innovacionActiva (pasoDeG v q) (ok i) (Y i)
    (avg masas (rutas (pasoDeG v q) 0 q x) (mark masas (fun l=>∃ i,∃ m : Fin (q+1),
      2*B i*sqrt (q:ℝ)*a≤|sumarPasos (D i) 0 x 0 (l.take m.val)|))).val≤
      (Fintype.card I:ℝ)*(q+1)*(2*exp (-(a^2))) := by
  let D:=fun i=>innovacionActiva (pasoDeG v q) (ok i) (Y i)
  let E (p : I×Fin (q+1)) (l : List (EstadoGuiado n)):=2*B p.1*sqrt (q:ℝ)*a≤|sumarPasos (D p.1) 0 x 0 (l.take p.2.val)|
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  let s:=sqrt (q:ℝ)
  have sp : 0<s:=Real.sqrt_pos.mpr qr
  have sq : s^2=(q:ℝ):=Real.sq_sqrt qr.le
  have each (p : I×Fin (q+1)) :
      (avg masas (rutas (pasoDeG v q) 0 q x) (mark masas (E p))).val≤2*exp (-(a^2)):=by
    let b:=B p.1
    have bpos : 0<b:=bp _
    let θ:=a/(b*s)
    have id : θ*b=a/s:=by dsimp only [θ]; field_simp [bpos.ne',sp.ne']; ring
    have θpos : 0≤θ:=div_nonneg ap (mul_pos bpos sp).le
    have bound : θ*b≤1:=by rw [id]; exact (div_le_one sp).mpr scale
    have mq : p.2.val≤q:=by have :=p.2.isLt; omega
    have prelim:=cola_bilateral_de_innovaciones_G v q (ok p.1) (Y p.1) bpos.le θpos bound
      (jump p.1) 0 p.2.val q mq x (2*b*s*a)
    have le:=mul_le_mul_of_nonneg_right (show (p.2.val:ℝ)≤q by exact_mod_cast mq) (sq_nonneg (θ*b))
    have algebra : (q:ℝ)*(θ*b)^2-θ*(2*b*s*a)= -(a^2):=by
      rw [id,←sq]; dsimp only [θ]; field_simp [bpos.ne',sp.ne']; ring
    exact prelim.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [le,algebra])) (by norm_num))
  have prod:=union_sobre_una_misma_ley _ E each
  have pair (l : List (EstadoGuiado n)) : (∃ p,E p l)↔(∃ i,∃ m : Fin (q+1),E (i,m) l) :=
    ⟨fun ⟨p,h⟩=>⟨p.1,p.2,h⟩,fun ⟨i,m,h⟩=>⟨(i,m),h⟩⟩
  simp_rw [pair] at prod
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using prod
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.innovaciones_simultaneas_de_G
