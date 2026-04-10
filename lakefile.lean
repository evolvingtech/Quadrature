/-
Copyright (c) 2026 Loren Abdulezer / Evolving Technologies Corporation
Licensed under the Apache License, Version 2.0
-/
import Lake
import Lake.Config

open Lake DSL

package quadrature

lean_lib Quadrature

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "v4.28.0"
