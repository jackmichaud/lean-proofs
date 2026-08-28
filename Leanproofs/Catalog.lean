/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Registry
import Leanproofs.Fermat

/-!
# Frontier catalog

The durable, version-controlled index of research artifacts in this repository. Every declaration
named here is resolved and audited by `lake exe frontier validate`.
-/

namespace Frontier

def catalog : Array Entry := #[
  {
    id := "fermat-units"
    title := "Fermat in the unit group"
    summary := "Every unit of ZMod p raised to p - 1 is one when p is prime."
    status := .proved
    topic := "number-theory"
    tags := #["fermat", "finite-groups", "zmod", "units"]
    statement := ``FermatFromScratch.units_pow_card_sub_one_eq_one
    certificate? := some ``FermatFromScratch.units_pow_card_sub_one_eq_one
    evidence? := some .proof
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-28"
  },
  {
    id := "fermat-zmod-nonzero"
    title := "Fermat for nonzero residues"
    summary := "A nonzero residue modulo a prime raised to p - 1 is one."
    status := .proved
    topic := "number-theory"
    tags := #["fermat", "finite-fields", "zmod"]
    statement := ``FermatFromScratch.pow_card_sub_one_eq_one
    certificate? := some ``FermatFromScratch.pow_card_sub_one_eq_one
    evidence? := some .proof
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-28"
  },
  {
    id := "fermat-zmod"
    title := "Fermat in ZMod"
    summary := "Every residue modulo a prime satisfies a^p = a."
    status := .proved
    topic := "number-theory"
    tags := #["fermat", "finite-fields", "zmod"]
    statement := ``FermatFromScratch.pow_card
    certificate? := some ``FermatFromScratch.pow_card
    evidence? := some .proof
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-28"
  },
  {
    id := "fermat-integer-coprime"
    title := "Fermat for coprime integers"
    summary := "The integer form a^(p-1) = 1 modulo p when p does not divide a."
    status := .proved
    topic := "number-theory"
    tags := #["fermat", "integers", "congruence", "zmod"]
    statement := ``FermatFromScratch.int_pow_card_sub_one
    certificate? := some ``FermatFromScratch.int_pow_card_sub_one
    evidence? := some .proof
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-28"
  },
  {
    id := "fermat-integer"
    title := "Fermat for every integer"
    summary := "For every integer a and prime p, a^p = a modulo p."
    status := .proved
    topic := "number-theory"
    tags := #["fermat", "integers", "congruence", "zmod"]
    statement := ``FermatFromScratch.int_pow_card
    certificate? := some ``FermatFromScratch.int_pow_card
    evidence? := some .proof
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-28"
  }
]

end Frontier
