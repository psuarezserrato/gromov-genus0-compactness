import GromovCompactness.Geometry.Sphere

open GromovCompactness

-- 1. Anti-facade verification
#check affine_scaling
#check affine_scaling_toHomeo_ne_id
#check affine_scaling_toHomeo_ne_id_frame
#check dil_homeo_ne_id

-- 2. MoebiusFrame groupoid interface verification
#check MoebiusFrame.comp_id
#check MoebiusFrame.id_comp
#check MoebiusFrame.comp_assoc
#check MoebiusFrame.inv_comp
#check MoebiusFrame.comp_inv
#check MoebiusFrame.inv_comp_toHomeo
#check MoebiusFrame.comp_inv_toHomeo
#check MoebiusFrame.inv_comp_matrix
#check MoebiusFrame.comp_inv_matrix

-- Also check top-level names
#check moebius_frame_comp_id
#check moebius_frame_id_comp
#check moebius_frame_comp_assoc
#check moebius_frame_inv_comp
#check moebius_frame_comp_inv

-- 3. Three-point normalization and uniqueness verification
#check moebius_three_points_unique
#check exists_unique_moebius_three_points
#check PglEquiv

-- 4. Axiom verification
#print axioms affine_scaling
#print axioms affine_scaling_toHomeo_ne_id
#print axioms affine_scaling_toHomeo_ne_id_frame
#print axioms dil_homeo
#print axioms dil_homeo_is_smooth
#print axioms dil_homeo_symm_is_smooth
#print axioms exists_unique_moebius_three_points
#print axioms moebius_three_points_unique
#print axioms MoebiusFrame.comp_id
#print axioms MoebiusFrame.inv_comp
#print axioms MoebiusFrame.comp_inv
#print axioms MoebiusFrame.inv_comp_matrix
#print axioms MoebiusFrame.comp_inv_matrix
#print axioms disk_at
#print axioms is_open_disk_at
#print axioms inversion
#print axioms rotation
