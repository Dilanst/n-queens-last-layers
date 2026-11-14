import RelojDelPrefijoRegular
import SumasYMargenesDelBalance
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def cargaDeDestino {n} (h : ℕ) (p : FactoresContinuos) (z e : Cell n) (j : Fin 4) :=
  probLinea n h p (side j,key z e j)
def probDeLaCasilla {n} (h : ℕ) (p : FactoresContinuos) (e : Cell n) :=
  probArista n h p e / n

theorem cargas_para_un_cruce {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margen : 2*(C:ℝ)≤κ*n) (z : Cell n) :
    (∀ e j,cargaDeDestino h p z e j≤1) ∧
    (∀ e : Cell n,(n:ℝ≥0)*probDeLaCasilla h p e≤m^4/κ^4) := by
  have nn : 0<n := by omega
  have np : (n:ℝ≥0)≠0 := by exact_mod_cast nn.ne'
  constructor
  · intro e j
    let i:=side j
    let v : Indice n:=⟨key z e j,on_board (dest z e j) (side j)⟩
    have ob : 2 ≤ i.val := by change 2 ≤ (side j).val; fin_cases j <;> decide
    have b:=carga_estricta_en_oblicuas nn sp i v ob margen (bal i v)
    change (probLinea n h p (i,v.val):ℝ)≤1
    rw [carga_identificada nn]
    exact b.trans (sub_le_self _ (by positivity))
  · intro e
    have b:=(cargas_acotadas (h:=h) hn sp kp (0,0) e).2
    change n*(probArista n h p e/n)≤_
    rwa [show (n:ℝ≥0)*(probArista n h p e/n)=probArista n h p e by field_simp]

theorem piso_del_compensador {n t T : ℕ} {ζ : ℝ≥0} (hn : 2≤n) (tT : t<T)
    (hasta : ζ≤fraccionAntes n T) :
    (n:ℝ≥0)*ζ ≤ (↑((2*n-1)-(t+1)):ℝ≥0) := by
  have nN : (n:ℝ≥0)≤(↑(2*n-1):ℝ≥0) := by exact_mod_cast (by omega : n≤2*n-1)
  have np : 0<(↑(2*n-1):ℝ≥0) := by exact_mod_cast (by omega : 0<2*n-1)
  have step:=fraccion_antes_del_horizonte (Nat.succ_le_of_lt tT) hasta
  unfold fraccionAntes at step
  simpa only [mul_comm] using (mul_le_mul_right' nN ζ).trans
    (by simpa only [mul_comm] using (le_div_iff₀ np).mp step)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cargas_para_un_cruce
#print axioms ArticuloA.Historias.piso_del_compensador
