import PrimerOrdenDeLasSalidasConReserva
import PrefijosDeUnaMismaTrayectoria
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open Classical
variable {X : Type}

def visitasDeCamino (I : ℕ→X→X→Prop) (t : ℕ) (x : X) : List X→ℕ
  | []=>0
  | y::ys=>(if I t x y then 1 else 0)+visitasDeCamino I (t+1) y ys

def prefijoRegular (V : ℕ→X→Prop) (t : ℕ) (x : X) : List X→Prop
  | []=>True
  | y::ys=>V t x ∧ prefijoRegular V (t+1) y ys

def descuentoDeVisitas (V : ℕ→X→Prop) (I : ℕ→X→X→Prop) (t : ℕ) (x : X) (l : List X) : ℝ≥0 :=
  if prefijoRegular V t x l then (1/2:ℝ≥0)^visitasDeCamino I t x l else 0

theorem momento_de_visitas {S : ℕ→X→Atoms ℝ≥0 X} (norm : ∀ t x,total masas (S t x)=1)
    (V : ℕ→X→Prop) (I : ℕ→X→X→Prop) (b : ℝ≥0) (b1 : b≤1)
    (drift : ∀ t x,V t x → b≤avg masas (S t x) (mark masas (I t x)))
    (q t : ℕ) (x : X) : avg masas (rutas S t q x) (descuentoDeVisitas V I t x)≤(1-b/2)^q := by
  induction q generalizing t x with
  | zero => rw [rutas,avg_point]; simp [descuentoDeVisitas,prefijoRegular,visitasDeCamino]
  | succ q ih =>
    rw [rutas,avg_bind]
    let row:=S t x
    let hit : X→ℝ≥0:=fun y=>if I t x y then 1/2 else 1
    by_cases vx : V t x
    · have factor (y : X) (l : List X) : descuentoDeVisitas V I t x (y::l)=hit y*descuentoDeVisitas V I (t+1) y l:=by
        by_cases v : prefijoRegular V (t+1) y l <;> by_cases h : I t x y <;>
          simp [descuentoDeVisitas,prefijoRegular,visitasDeCamino,v,vx,h,hit,pow_add,mul_comm]
      have term (y : X) : avg masas ((rutas S (t+1) q y).map (fun i=>(i.1,y::i.2)))
          (descuentoDeVisitas V I t x)≤(1-b/2)^q*hit y:=by
        rw [avg_push masas _ (fun l=>y::l),show (fun l=>descuentoDeVisitas V I t x (y::l))=
          (fun l=>masas.mul (hit y) (descuentoDeVisitas V I (t+1) y l)) from funext (factor y),avg_mul]
        exact (mul_le_mul_of_nonneg_left (ih (t+1) y) (zero_le (hit y))).trans_eq (mul_comm _ _)
      have hrow : avg masas row hit≤1-b/2:=by
        apply NNReal.coe_le_coe.mp
        rw [NNReal.coe_sub (by exact (div_le_self (zero_le b) (by norm_num)).trans b1),NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one]
        change (avg masas row hit).val ≤ 1-(b:ℝ)/2
        rw [←media_coe row hit]
        have aff:=media_affine row (fun y=>(mark masas (I t x) y).val) 1 (-1/2)
        have pointw (y : X) : (hit y:ℝ)=1+(-1/2)*(mark masas (I t x) y).val:=by
          by_cases h : I t x y <;> norm_num [hit,mark,h,masas]
        simp_rw [pointw]
        rw [aff,show total masas row=1 from norm t x]
        have h := NNReal.coe_le_coe.mpr (drift t x vx)
        have c : media row (fun y=>(mark masas (I t x) y).val)=(avg masas (S t x) (mark masas (I t x))).val:=media_coe _ _
        change (1:ℝ)*1+ -1/2*(media row (fun y=>(mark masas (I t x) y).val))≤1-(b:ℝ)/2
        rw [c]
        have hb : (b:ℝ)≤(avg masas (S t x) (mark masas (I t x))).val:=h
        linarith only [hb]
      have top:=avg_mono masas row (fun y=>avg masas ((rutas S (t+1) q y).map (fun i=>(i.1,y::i.2))) (descuentoDeVisitas V I t x)) (fun y=>masas.mul ((1-b/2)^q) (hit y)) (fun i _=>term i.2)
      rw [avg_mul] at top
      exact top.trans ((mul_le_mul_of_nonneg_left hrow (zero_le _)).trans_eq (pow_succ _ q).symm)
    · have zero (y : X) : avg masas ((rutas S (t+1) q y).map (fun i=>(i.1,y::i.2)))
          (descuentoDeVisitas V I t x)=0:=by
        rw [avg_push masas _ (fun l=>y::l)]
        simp only [descuentoDeVisitas,prefijoRegular,vx,false_and,if_false]
        rw [avg_constant]; exact mul_zero _
      simp_rw [zero]
      rw [avg_constant]
      exact (mul_zero _).le.trans (zero_le _)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.momento_de_visitas
