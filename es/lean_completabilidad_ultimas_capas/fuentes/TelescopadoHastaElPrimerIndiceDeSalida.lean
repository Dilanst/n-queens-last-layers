import ColaDeInnovacionesConDependenciaDelPaso
import EnvolventeTemporalDelProcesoGuiado
namespace ArticuloA.Historias
open RealFinita
open scoped BigOperators
noncomputable section
open Classical

def estadoTrasPrefijo {X : Type} (x : X) : List X→ℕ→X
  | [],_=>x
  | _::_,0=>x
  | y::ys,k+1=>estadoTrasPrefijo y ys k

theorem cuenta_de_aristas_del_prefijo {X : Type} (Y : ℕ→X→X→ℝ) (t : ℕ) (l : List X)
    (x : X) (z : ℝ) (m : ℕ) (ok : m≤l.length) :
    sumarPasos Y t x z (l.take m)=z+∑ j∈Finset.range m,
      Y (t+j) (estadoTrasPrefijo x l j) (estadoTrasPrefijo x l (j+1)) := by
  induction m generalizing l t x z with
  | zero=>simp [sumarPasos]
  | succ m ih=>
    cases l with
    | nil=>simp at ok
    | cons y ys=>
      simp only [List.take_succ_cons,sumarPasos]
      rw [ih (t+1) ys y (z+Y t x y) (by simpa using ok),Finset.sum_range_succ']
      simp only [estadoTrasPrefijo,Nat.add_zero,Nat.zero_add]
      have shift (j : ℕ) : t+(j+1)=t+1+j:=by omega
      have sums : (∑ j∈Finset.range m,Y (t+(j+1)) (estadoTrasPrefijo y ys j) (estadoTrasPrefijo y ys (j+1)))=
          ∑ j∈Finset.range m,Y (t+1+j) (estadoTrasPrefijo y ys j) (estadoTrasPrefijo y ys (j+1)):=by
        apply Finset.sum_congr rfl; intro j _; rw [shift j]
      have initial : estadoTrasPrefijo y ys 0=y:=by cases ys <;> rfl
      rw [sums,initial]; ring

theorem diferencia_por_deriva_y_fluctuacion {X : Type} (t m : ℕ) (x : ℕ→X)
    (H : ℕ→X→ℝ) (Y : ℕ→X→X→ℝ) (d : ℕ→ℝ)
    (cambios : ∀ j<m,Y (t+j) (x j) (x (j+1))=H (t+j+1) (x (j+1))-H (t+j) (x j)) :
    H (t+m) (x m)-H t (x 0)=(∑ j∈Finset.range m,d j)+
       ∑ j∈Finset.range m,(Y (t+j) (x j) (x (j+1))-d j) := by
  rw [←Finset.sum_add_distrib]
  calc _ = ∑ j∈Finset.range m,(H (t+(j+1)) (x (j+1))-H (t+j) (x j)):=by
             simpa using (Finset.sum_range_sub (fun j=>H (t+j) (x j)) m).symm
       _ = _:=by
         apply Finset.sum_congr rfl
         intro j hj
         rw [cambios j (Finset.mem_range.mp hj),Nat.add_assoc]; ring

theorem exclusion_de_la_primera_salida {q : ℕ} (X : ℕ→ℝ) {η A r : ℝ} (qp : 0<q)
    (hp : 0<η) (hq : η≤1/4) (ap : 0≤A) (small : A*(1/η)^12≤r)
    (rec : ∀ t≤q,(∀ j<t,X j≤r)→X t≤A+
        ∑ j∈Finset.range t,9/((q:ℝ)-(1-η)*j)*X j) :
    ∀ t≤q,X t≤A*(1/η)^12 := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih=>
    intro tq
    apply envolvente_de_seguimiento_hasta_la_parada qp tq hp hq ap
    intro j jt
    exact rec j (jt.trans tq) (fun k kj=>(ih k (kj.trans_le jt) (kj.le.trans (jt.trans tq))).trans small)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.diferencia_por_deriva_y_fluctuacion
#print axioms ArticuloA.Historias.exclusion_de_la_primera_salida
