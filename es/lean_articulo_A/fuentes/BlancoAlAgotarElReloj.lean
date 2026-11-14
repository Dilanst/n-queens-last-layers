import ErrorDelGeneradorPorRaiz
import ExtremosDeLaReparacionDirecta
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.Adjunto Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
open Classical

private theorem producto_interpolado (y : ℝ) (hy : y∈Set.Icc (0:ℝ) 1) (l : List ℝ)
    (unit : ∀ a∈l,a∈Set.Icc (0:ℝ) 1) :
    let b:=l.prod
    let v:=(l.map (fun a => 1-y+y*a)).prod
    0≤b ∧ b≤1 ∧ b≤v ∧ v≤1-y+y*b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨lo,hi⟩:=unit a (by simp)
    obtain ⟨bp,b1,bv,vle⟩:=ih (fun b hb => unit b (by simp [hb]))
    let b:=l.prod
    let v:=(l.map (fun a => 1-y+y*a)).prod
    change 0≤a*b ∧ a*b≤1 ∧ a*b≤(1-y+y*a)*v ∧ (1-y+y*a)*v≤1-y+y*(a*b)
    have larger : a≤1-y+y*a := by nlinarith only [mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hi)]
    have nn:=lo.trans larger
    refine ⟨mul_nonneg lo bp,(mul_le_mul hi b1 bp zero_le_one).trans_eq (one_mul _),
      mul_le_mul larger bv bp nn,(mul_le_mul_of_nonneg_left vle nn).trans ?_⟩
    have bounds : 0≤y*(1-y)*(1-a)*(1-b) := mul_nonneg (mul_nonneg (mul_nonneg hy.1
      (sub_nonneg.mpr hy.2)) (sub_nonneg.mpr hi)) (sub_nonneg.mpr b1)
    nlinarith only [bounds]

private theorem error_escalar {y b v : ℝ} (hy : y∈Set.Icc (0:ℝ) 1) (b₀ : 0≤b) (b₁ : b≤1)
    (bv : b≤v) (vle : v≤1-y+y*b) : |y*v-b|≤1-y := by
  have room:=mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr b₁)
  have lo:=mul_le_mul_of_nonneg_left bv hy.1
  have up:=mul_le_mul_of_nonneg_right hy.2 (b₀.trans bv)
  have yb:=mul_le_mul_of_nonneg_right hy.2 b₀
  exact abs_le.mpr ⟨by nlinarith only [room,lo],by linarith only [up,yb,vle]⟩

private theorem cuatro_factores (y : ℝ≥0) (hy : y≤1) (p : Fin 4→ℝ≥0) (hp : ∀ j,p j≤1) :
    |(y*masas.four (fun j => 1-y*p j):ℝ≥0).val-(masas.four (fun j => 1-p j):ℝ≥0).val|≤1-(y:ℝ) := by
  let a:Fin 4→ℝ:=fun j => 1-(p j:ℝ)
  have unit (j) : a j∈Set.Icc (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hp j)),sub_le_self _ (p j).property⟩
  let l:List ℝ:=[a 0,a 1,a 2,a 3]
  have ok : ∀ b∈l,b∈Set.Icc (0:ℝ) 1 := by
    intro b mem
    rcases (by simpa [l] using mem : b=a 0 ∨ b=a 1 ∨ b=a 2 ∨ b=a 3) with rfl|rfl|rfl|rfl <;> apply unit
  obtain ⟨b₀,b₁,bv,vle⟩:=producto_interpolado (y:ℝ) ⟨y.property,NNReal.coe_le_coe.mpr hy⟩ l ok
  let v:=(l.map (fun b => 1-(y:ℝ)+y*b)).prod
  have err : |(y:ℝ)*v-l.prod|≤1-y :=
    error_escalar ⟨y.property,NNReal.coe_le_coe.mpr hy⟩ b₀ b₁ bv vle
  have t (j) : 1-(y:ℝ)+y*a j=1-(y:ℝ)*p j := by dsimp [a]; ring
  have live (j) : y*p j≤1 := (mul_le_mul' hy (hp j)).trans_eq (one_mul _)
  simp only [v,l,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,t] at err
  unfold ProfileScale.four
  change |((y*((1-y*p 0)*(1-y*p 1)*((1-y*p 2)*(1-y*p 3)))):ℝ≥0).val-
    (((1-p 0)*(1-p 1)*((1-p 2)*(1-p 3))):ℝ≥0).val|≤_
  have c₁ (i : Fin 4) : ((1-y*p i:ℝ≥0):ℝ)=1-(y:ℝ)*p i := NNReal.coe_sub (live i)
  have c₂ (i : Fin 4) : ((1-p i:ℝ≥0):ℝ)=1-(p i:ℝ) := NNReal.coe_sub (hp i)
  change |(y:ℝ)*((((1-y*p 0:ℝ≥0):ℝ)*((1-y*p 1:ℝ≥0):ℝ))*(((1-y*p 2:ℝ≥0):ℝ)*((1-y*p 3:ℝ≥0):ℝ)))-
    ((((1-p 0:ℝ≥0):ℝ)*((1-p 1:ℝ≥0):ℝ))*(((1-p 2:ℝ≥0):ℝ)*((1-p 3:ℝ≥0):ℝ)))|≤_
  simpa only [c₁,c₂,mul_assoc,a] using err

theorem blanco_hasta_uno {n} (z : Cell n) (y : ℝ≥0) (hy : y≤1)
    (p : Cell n→Fin 4→ℝ≥0) (π : Cell n→ℝ≥0) (hp : ∀ e j,p e j≤1)
    (M : ℝ≥0) (cap : ∀ e,(n:ℝ≥0)*π e≤M) :
    |(blancoDeLaRaiz y z p π:ℝ)-(blancoDeLaRaiz 1 z p π:ℝ)|≤(1-(y:ℝ))*M*n := by
  have np : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt z.1.isLt)
  let w (t : ℝ≥0) (e : Cell n) := (if filterG z e then t*π e else 0)*masas.four (fun i => 1-t*p e i)
  have term (e) : |(w y e:ℝ)-(w 1 e:ℝ)|≤(1-(y:ℝ))*((M:ℝ)/n) := by
    have coef : (π e:ℝ)≤(M:ℝ)/n := (le_div_iff₀ np).mpr (by simpa only [mul_comm,NNReal.coe_mul,NNReal.coe_natCast] using NNReal.coe_le_coe.mpr (cap e))
    have dp:=cuatro_factores y hy (p e) (hp e)
    by_cases g : filterG z e
    · simp only [w,if_pos g,one_mul,NNReal.coe_mul] at dp ⊢
      rw [show (y:ℝ)*π e*(masas.four (fun i => 1-y*p e i):ℝ)-(π e:ℝ)*(masas.four (fun i => 1-p e i):ℝ)=
        (π e:ℝ)*((y:ℝ)*(masas.four (fun i => 1-y*p e i):ℝ)-(masas.four (fun i => 1-p e i):ℝ)) by ring,
        abs_mul]
      have pos : 0≤(π e:ℝ) := (π e).property
      rw [abs_of_nonneg pos]
      change |(y:ℝ)*(masas.four (fun j => 1-y*p e j):ℝ)-(masas.four (fun j => 1-p e j):ℝ)|≤1-(y:ℝ) at dp
      simpa [mul_comm] using mul_le_mul coef dp (abs_nonneg _) (div_nonneg M.property np.le)
    · simp only [w,if_neg g,zero_mul,NNReal.coe_zero,sub_self,abs_zero]
      exact mul_nonneg (sub_nonneg.mpr (show (y:ℝ)≤1 from hy)) (div_nonneg M.property np.le)
  have sum (l : List (Cell n)) :
      |(masas.sum l (w y):ℝ)-(masas.sum l (w 1):ℝ)|≤(l.length:ℝ)*((1-y)*((M:ℝ)/n)) := by
    induction l with
    | nil => simp [MassScale.sum,masas]
    | cons e l ih =>
      change |((w y e:ℝ)+(masas.sum l (w y):ℝ))-((w 1 e:ℝ)+(masas.sum l (w 1):ℝ))|≤_
      rw [show ((w y e:ℝ)+_)-((w 1 e:ℝ)+_)=((w y e:ℝ)-(w 1 e:ℝ))+((masas.sum l (w y):ℝ)-(masas.sum l (w 1):ℝ)) by ring]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; exact (abs_add_le _ _).trans (by linarith [term e])
  apply (sum (board n)).trans
  rw [board_card,Nat.cast_mul]; exact le_of_eq (by field_simp; ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.blanco_hasta_uno
