import CotaReparaciones
namespace ArticuloA.Capas
open ArticuloA
/-- Integer numerators and denominators of the physical fractions for h≥1. -/
noncomputable def numerator (n j : Nat) := (n-j+1)*count n (n-j+1)
noncomputable def denominator (n j : Nat) := j^2 * count n (n-j)
def prodTo (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | j+1 => prodTo f j * f (j+1)
def falling (n : Nat) := prodTo (fun j => n-j+1)
def fac (j : Nat) := prodTo id j

/-- Multiplying the exact fractions for j=1,...,h and cancelling formally
by equality of cross products. Valid even for a level with zero count. -/
theorem capas (n h : Nat) (inside : h ≤ n) :
    count n (n-h) * (fac h)^2 * prodTo (numerator n) h =
    count n n * falling n h * prodTo (denominator n) h := by
  induction h with
  | zero => simp [prodTo,falling,fac]
  | succ j ih =>
    have cur := ih (by omega)
    have prev : n-(j+1)+1 = n-j := by omega
    let extra := ((j+1)^2 * count n (n-(j+1))) * (n-(j+1)+1)
    have same := congrArg (fun x => x*extra) cur
    change count n (n-(j+1)) * (fac j * (j+1))^2 *
      (prodTo (numerator n) j * ((n-(j+1)+1)*count n (n-(j+1)+1))) =
      count n n * (falling n j*(n-(j+1)+1)) *
        (prodTo (denominator n) j * ((j+1)^2*count n (n-(j+1))))
    dsimp only [extra] at same
    rw [prev] at same ⊢
    simp only [Nat.pow_two] at same ⊢
    exact (by
      calc
        _ = (count n (n-j) * (fac j*fac j) * prodTo (numerator n) j) *
          (((j+1)*(j+1)*count n (n-(j+1)))*(n-j)) := by ac_rfl
        _ = _ := same
        _ = _ := by ac_rfl)
end ArticuloA.Capas
#print axioms ArticuloA.Capas.capas
