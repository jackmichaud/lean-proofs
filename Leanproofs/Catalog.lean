/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Knowledge.LegacyAdapter
import Leanproofs.Catalan
import Leanproofs.Fermat

/-!
# Frontier catalog

The durable, version-controlled index of research artifacts in this repository. Every declaration
named here is resolved and audited by `lake exe frontier validate`.

`status` records what this repository has checked; `literature` records what mathematics
already knows. Read them together: `status := .open` with `literature := .proved` means "known
theorem, not yet formalized here", which is a formalization task rather than a research
frontier.
-/

namespace Frontier

namespace Catalog

open Knowledge

private def claimId (id : String) : ClaimId := ⟨id⟩
private def formalizationId (id : String) : FormalizationId := ⟨id ++ ":formalization:primary"⟩
private def certificateId (id : String) : CertificateId := ⟨id ++ ":certificate"⟩
private def citationId (id : String) : CitationId := ⟨id ++ ":citation"⟩
private def assertionId (id : String) : LiteratureAssertionId := ⟨id ++ ":literature"⟩
private def sanityId (id : String) (index : Nat) : SanityCheckId := ⟨id ++ s!":sanity:{index}"⟩

private def claims : Array Claim := #[
  {
    id := claimId "catalan-conjecture"
    title := "Catalan's conjecture"
    summary := "The only consecutive perfect powers above one are 8 and 9."
    topic := "number-theory"
    tags := #["catalan", "mihailescu", "perfect-powers", "diophantine"]
    authors := #["Jack Michaud"]
    source? := some "Formalizing the proof is open work in this repository."
    created := "2026-08-31"
    updated := "2026-08-31"
  },
  {
    id := claimId "fermat-units"
    title := "Fermat in the unit group"
    summary := "Every unit of ZMod p raised to p - 1 is one when p is prime."
    topic := "number-theory"
    tags := #["fermat", "finite-groups", "zmod", "units"]
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-31"
  },
  {
    id := claimId "fermat-zmod-nonzero"
    title := "Fermat for nonzero residues"
    summary := "A nonzero residue modulo a prime raised to p - 1 is one."
    topic := "number-theory"
    tags := #["fermat", "finite-fields", "zmod"]
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-31"
  },
  {
    id := claimId "fermat-zmod"
    title := "Fermat in ZMod"
    summary := "Every residue modulo a prime satisfies a^p = a."
    topic := "number-theory"
    tags := #["fermat", "finite-fields", "zmod"]
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-31"
  },
  {
    id := claimId "fermat-integer-coprime"
    title := "Fermat for coprime integers"
    summary := "The integer form a^(p-1) = 1 modulo p when p does not divide a."
    topic := "number-theory"
    tags := #["fermat", "integers", "congruence", "zmod"]
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-31"
  },
  {
    id := claimId "fermat-integer"
    title := "Fermat for every integer"
    summary := "For every integer a and prime p, a^p = a modulo p."
    topic := "number-theory"
    tags := #["fermat", "integers", "congruence", "zmod"]
    authors := #["Jack Michaud"]
    created := "2026-08-28"
    updated := "2026-08-31"
  }
]

private def formalizations : Array Formalization := #[
  { id := formalizationId "catalan-conjecture", claimId := claimId "catalan-conjecture",
    statement := ``Catalan.conjecture, status := .open, authors := #["Jack Michaud"],
    tooling := #["Codex"] },
  { id := formalizationId "fermat-units", claimId := claimId "fermat-units",
    statement := ``FermatFromScratch.units_pow_card_sub_one_eq_one, status := .proved,
    authors := #["Jack Michaud"] },
  { id := formalizationId "fermat-zmod-nonzero", claimId := claimId "fermat-zmod-nonzero",
    statement := ``FermatFromScratch.pow_card_sub_one_eq_one, status := .proved,
    authors := #["Jack Michaud"] },
  { id := formalizationId "fermat-zmod", claimId := claimId "fermat-zmod",
    statement := ``FermatFromScratch.pow_card, status := .proved,
    authors := #["Jack Michaud"] },
  { id := formalizationId "fermat-integer-coprime", claimId := claimId "fermat-integer-coprime",
    statement := ``FermatFromScratch.int_pow_card_sub_one, status := .proved,
    authors := #["Jack Michaud"] },
  { id := formalizationId "fermat-integer", claimId := claimId "fermat-integer",
    statement := ``FermatFromScratch.int_pow_card, status := .proved,
    authors := #["Jack Michaud"] }
]

private def certificates : Array Certificate := #[
  { id := certificateId "fermat-units", formalizationId := formalizationId "fermat-units",
    declaration := ``FermatFromScratch.units_pow_card_sub_one_eq_one,
    conclusion := .affirms, method := .directProof, authors := #["Jack Michaud"] },
  { id := certificateId "fermat-zmod-nonzero",
    formalizationId := formalizationId "fermat-zmod-nonzero",
    declaration := ``FermatFromScratch.pow_card_sub_one_eq_one,
    conclusion := .affirms, method := .directProof, authors := #["Jack Michaud"] },
  { id := certificateId "fermat-zmod", formalizationId := formalizationId "fermat-zmod",
    declaration := ``FermatFromScratch.pow_card, conclusion := .affirms,
    method := .directProof, authors := #["Jack Michaud"] },
  { id := certificateId "fermat-integer-coprime",
    formalizationId := formalizationId "fermat-integer-coprime",
    declaration := ``FermatFromScratch.int_pow_card_sub_one, conclusion := .affirms,
    method := .directProof, authors := #["Jack Michaud"] },
  { id := certificateId "fermat-integer", formalizationId := formalizationId "fermat-integer",
    declaration := ``FermatFromScratch.int_pow_card, conclusion := .affirms,
    method := .directProof, authors := #["Jack Michaud"] }
]

private def sanityChecks : Array SanityCheck := #[
  { id := sanityId "catalan-conjecture" 0,
    formalizationId := formalizationId "catalan-conjecture",
    declaration := ``Catalan.exceptional_solution, role := .workedExample },
  { id := sanityId "catalan-conjecture" 1,
    formalizationId := formalizationId "catalan-conjecture",
    declaration := ``Catalan.hypotheses_satisfiable, role := .satisfiable },
  { id := sanityId "catalan-conjecture" 2,
    formalizationId := formalizationId "catalan-conjecture",
    declaration := ``Catalan.no_small_counterexample, role := .boundedSearch }
]

private def citations : Array Citation := #[
  { id := citationId "catalan-conjecture",
    display := "P. Mihăilescu, Primary cyclotomic units and a proof of Catalan's conjecture, \
      J. reine angew. Math. 572 (2004), 167–195.",
    year? := some 2004 },
  { id := citationId "fermat-units",
    display := "Fermat (1640); classical. See also mathlib `ZMod.pow_card_sub_one_eq_one`.",
    year? := some 1640 },
  { id := citationId "fermat-zmod", display := "Fermat (1640); classical.", year? := some 1640 }
]

private def literatureAssertions : Array LiteratureAssertion := #[
  { id := assertionId "catalan-conjecture", claimId := claimId "catalan-conjecture",
    conclusion := .affirmed, citations := #[citationId "catalan-conjecture"],
    observed := "2026-08-31" },
  { id := assertionId "fermat-units", claimId := claimId "fermat-units",
    conclusion := .affirmed, citations := #[citationId "fermat-units"],
    observed := "2026-08-31" },
  { id := assertionId "fermat-zmod-nonzero", claimId := claimId "fermat-zmod-nonzero",
    conclusion := .affirmed, citations := #[citationId "fermat-zmod"],
    observed := "2026-08-31" },
  { id := assertionId "fermat-zmod", claimId := claimId "fermat-zmod",
    conclusion := .affirmed, citations := #[citationId "fermat-zmod"],
    observed := "2026-08-31" },
  { id := assertionId "fermat-integer-coprime", claimId := claimId "fermat-integer-coprime",
    conclusion := .affirmed, citations := #[citationId "fermat-zmod"],
    observed := "2026-08-31" },
  { id := assertionId "fermat-integer", claimId := claimId "fermat-integer",
    conclusion := .affirmed, citations := #[citationId "fermat-zmod"],
    observed := "2026-08-31" }
]

end Catalog

/-- The authoritative, normalized mathematical knowledge catalog. -/
def knowledgeCatalog : Knowledge.Registry := {
  claims := Catalog.claims
  formalizations := Catalog.formalizations
  certificates := Catalog.certificates
  sanityChecks := Catalog.sanityChecks
  citations := Catalog.citations
  literatureAssertions := Catalog.literatureAssertions
}

/-- Temporary projection for the existing CLI and trust-audit boundary. -/
def catalog : Array Entry :=
  let errors := knowledgeCatalog.validationErrors
  if errors.isEmpty then knowledgeCatalog.toEntries
  else panic! s!"invalid normalized knowledge catalog: {"; ".intercalate errors.toList}"

end Frontier
