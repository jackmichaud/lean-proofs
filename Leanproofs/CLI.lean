/-
Copyright (c) 2026 Jack Michaud. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Michaud
-/

import Leanproofs.Frontier.Protocol

/-!
# Frontier CLI

Audits the research catalog against a compiled Lean environment, searches all imported Lean
declarations, records work in progress, and exports a reusable machine-readable theorem index.

This module deliberately does *not* import `Leanproofs.Catalog`. The executable has to import
the project environment at runtime with initializers enabled, and re-initializing modules that
are also statically linked into the binary crashes the process. `Leanproofs.Main` therefore
links only `Lean` and this module, imports the project, and hands the catalog in as data. See
that module for the full explanation.
-/

open Lean

namespace Frontier.CLI

end Frontier.CLI
