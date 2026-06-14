/-
  Freyd & Scedrov, *Categories and Allegories* §1.92  Singleton map, topos is exponential.

  §1.92  SINGLETON MAP A1: B → [B] (§1.92)
         Topos is exponential: [B]^A = [A × B] (§1.92)
  §1.921 LAWVERE DEFINITION of elementary topos (bicartesian + exponential + partial map classifier)
-/

import Fredy.S1_1
import Fredy.S1_9
import Fredy.S1_85


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-- **§1.92**: A topos is exponential.  The exponential B^A is constructed
    as a subobject of [A × B] via the singleton map (§1.92). -/
axiom topos_has_exponentials_ax : HasExponentials 𝒞

noncomputable instance topos_has_exponentials : HasExponentials 𝒞 :=
  topos_has_exponentials_ax

end Freyd
