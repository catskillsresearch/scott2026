/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Scott2026.Basic

export Scott2026 (scaffold_placeholder lemma_12 lemma_12_converse
  proposition_27 proposition_27_continuous
  proposition_28_total proposition_28_strict proposition_29 proposition_29_full
  theorem_17_mix
  theorem_17_complete lemma_41_const jech_lemma_14_15 jech_lemma_14_16
  jech_lemma_14_18 jech_lemma_14_19 theorem_1_iii theorem_1_ii jech_lemma_14_21
  jech_lemma_14_17 SetFormula ZFCAxiom ZFCProvable
  extensionalityAxiom pairingAxiom unionAxiom powerAxiom infinityAxiom
  regularityAxiom collectionAxiom separationAxiom choiceAxiom
  axiom_extensionality_valid axiom_pairing_valid axiom_union_valid
  axiom_power_valid axiom_separation_valid axiom_infinity_valid
  axiom_regularity_valid axiom_collection_valid
  regularity_semantic collectB collectB_spec
  hilbertK_sound hilbertS_sound hilbertDNE_sound
  allImp_sound allVac_sound allInst_sound eqRefl_sound eqLeibniz_sound
  bval_isOpairF bval_opairMemF wellOrderB leastIdx
  memB_powerB eqB_singletonB eqB_pairB eqB_opairB
  check_singleton check_pair check_opair check_omega_inductive
  check_omega_least proposition_3
  isFunctionB funsB homB idB compB
  isFunctionB_id isFunctionB_comp compB_congr memB_idB_funsB
  memB_funsB isHom_id isHom_comp
  definition_4 definition_5 definition_6 definition_7 definition_8
  definition_9 definition_10 definition_13 definition_13_iso
  definition_14 definition_15 definition_16
  definition_16_id definition_16_comp
  oid oid_eq oid_eps ePred ePred_val ePredPowerB
  oidRel oidRel_val oidHom oidRel_congr oidRel_id oidRel_comp relCompVal
  functionalOfRel functionalOfRel_functional functionalOfRel_gamma
  theorem_17_va_complete theorem_17_va_total theorem_17_va_full
  proposition_28_va_complete proposition_28_va_total proposition_28_va_canonical_eq
  powerBPoset definition_11_powerB
  CanonicalPowerIdx canonicalPowerSetoid canonicalPowerPoset
  canonicalPowerSetoid_isStrict canonicalPowerSetoid_isTotal
  canonicalPowerSetoid_isComplete canonicalPowerPoset_eq
  normalizePowerIdx normalizePowerIdx_idem normalizePowerIdx_eqB
  normalizePowerIdx_oid_eq normalizePowerIdx_subsetB normalizePowerIdx_eqB_eq
  restrictPowerIdx_restrictName restrictPowerIdx_isCanonical
  proposition_28_va_canonical_strict proposition_28_va_canonical_total
  proposition_28_va_canonical_complete definition_11_canonicalPowerB
  oid_powerB_not_strict
  corollary_18_prod corollary_18_funs corollary_18_prod_full corollary_18_funs_full
  oid_powerB_isComplete oid_funsB_isComplete mixPowerB restrictPowerIdx
  oid_eq_powerB oid_powerB_check_canonical_eq powerBPoset_eq
  engelerE engelerPair engelerPair_injective
  pairApplyB pairDomainB theorem_30_pair_injective
  engelerAppVA engelerLamVA DeterminedByFiniteVA
  AValuedReflexiveDcpo
  theorem_30_retract theorem_30_retract_oid theorem_30_model
  theorem_30_complete theorem_30_total theorem_30_strict theorem_30
  pLamVar pLamAbs pLamApp encodeLam pLamSet
  lamVarB lamAbsB lamAppB encodeLamB lamB lamInductiveB
  example_21 example_21_va
  proposition_22 proposition_22_least proposition_22_check_eq
  encodeEq pLamEqSet encodeEqB lamEqB lamEqInductiveB checkVar
  example_24 example_24_va example_24_subset
  Valuation interp interpClosed interp_var interp_app interp_abs
  interp_closed interp_agree interp_update_scott
  interp_subst interp_sound interp_sound_beta interpClosed_sound
  LamEq LamEqNC definition_23
  interp_sound_full interpClosed_sound_full definition_25_sound_full
  interp_substNaive_captures
  definition_25 definition_25_var definition_25_app definition_25_abs
  definition_25_closed definition_25_subst definition_25_sound
  definition_25_sound_beta definition_25_sound_closed
  engelerReflexiveDcpo
  EngelerCarrier interpVA interpClosedVA
  interpVA_var interpVA_app interpVA_abs interpVA_closed
  interpVA_subst interpVA_sound interpVA_sound_beta interpClosedVA_sound
  interpVA_update_determined
  interpVA_subst_CA interpVA_alpha interpVA_sound_beta_full
  interpVA_sound_full interpClosedVA_sound_full theorem_26_sound_full
  theorem_26 theorem_26_pure theorem_26_var theorem_26_app
  theorem_26_abs theorem_26_closed theorem_26_subst
  theorem_26_sound theorem_26_sound_beta theorem_26_sound_closed
  theorem_26_sound_closed_full
  theorem_26_update_determined
  setPSet setToCanonical checkVal
  lemma_31 lemma_31_closed
  churchTrue churchFalse churchNum churchIf
  churchTrueN churchFalseN churchNumN churchIfN
  churchSucc churchPred churchIsZero
  definition_32
  churchTrue_interp_ne_churchFalse churchNum_interp_injective
  engelerWithNumerals proposition_33
  corollary_34_check
  eqB_interpClosedVA_churchTrue_churchFalse
  churchNum_interpClosedVA_injective
  eqB_interpClosedVA_churchNum_subsingleton
  definition_32_interpClosedVA
  ScottOpen lemma_35 lemma_35_i lemma_35_ii
  MapsNumerals proposition_36 proposition_36_i proposition_36_ii
  manyOneLe_of_proposition_36_i
  exists_nat_fun_not_lambda_definable
  definition_37 lemma_38 G_X proposition_39 proposition_40
  lemma_41
  proposition_42 proposition_42_finite proposition_42_finite_image
  theorem_43 proposition_44)

export Scott2026.Lam (FreeFor subst_fresh freeFor_of_not_mem_fv freeFor_of_closed
  substCA substNaive substNaive_captures substNaive_captures_not_freeFor)

/-!
# Solution to the Challenge

Imports the sorry-free development so Comparator can match source theorems
against the Mathlib-only declarations in `Challenge.lean`.
-/
