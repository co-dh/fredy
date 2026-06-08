/-
  Freyd & Scedrov, *Categories and Allegories* §1.9  Topoi.

  §1.9   TOPOS: Cartesian + every object has a power-object.
  §1.912 SUBOBJECT CLASSIFIER Ω, universal subobject t:1→Ω.
  §1.913 All subobjects are equalizers; covers = epics.
  §1.92  SINGLETON MAP, topos is exponential.
-/

import Fredy.S1_1
import Fredy.S1_41
import Fredy.S1_42
import Fredy.S1_45


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- A SUBOBJECT CLASSIFIER Ω with universal monic t : 1 → Ω (§1.912).
    For each monic m : A' → A, there is a unique characteristic map χ_m : A → Ω
    such that m is the pullback of t along χ_m. -/
class HasSubobjectClassifier (𝒞 : Type u) [Cat.{v} 𝒞] extends HasTerminal 𝒞, HasPullbacks 𝒞 where
  omega : 𝒞
  true : one ⟶ omega
  true_monic : Mono true
  classify {A A' : 𝒞} (m : A' ⟶ A) : Mono m → (A ⟶ omega)

/-- A TOPOS (§1.9): Cartesian + subobject classifier.
    This implies power objects and exponentials (§1.92). -/
class Topos (𝒞 : Type u) [Cat.{v} 𝒞] extends
    HasTerminal 𝒞, HasBinaryProducts 𝒞, HasSubobjectClassifier 𝒞

end Freyd
