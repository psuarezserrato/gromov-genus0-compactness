/-
Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
see LICENSE.md for details.
This project is licensed under non-commercial use. If you wish to use this software in a
commercial product, service, or enterprise environment, please contact the developer to purchase
a commercial license or negotiate royalty terms.
Authors: Pablo Suárez-Serrato (November 2026)
-/

import GromovCompactness.Geometry.Sphere
open GromovCompactness

theorem affine_scaling_fixes_all (z : CP1) :
    (affine_scaling 0 2 (by norm_num)).toHomeo z = z := by
  rfl

#print affine_scaling_fixes_all
