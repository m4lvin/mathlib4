/-
Copyright (c) 2023 Linus A. Sommer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linus A. Sommer.
-/

-- Goals:
  -- Define The a polynomial ring over the
  -- Prove: tropical polynomials are the minimum over a finite piecewise collection of linear functions.
  -- Prove: Tropical Fundamental Theorem of Algebra

import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Real.ENNReal

open Tropical ENNReal

open scoped Polynomial

universe f
variable {f : (Tropical ℝ≥0∞)[X]}

#check f
#check Type f
