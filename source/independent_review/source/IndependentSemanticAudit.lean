import IndependentStatementGuard
import AIM34Audit
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.Sorry
import Lean.Util.FoldConsts
import Lean.PrivateName
import Lean.Meta.Basic
set_option pp.all true
set_option pp.privateNames true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let kernel := env.checked.get
  let modules : List Name := ("AIM34Definitions|JensenIdentities|RealRootGeometry|PolarRealRooted|JensenRootClosure|NonnegativeRootGeometry|JensenPositivity|SequenceBounds|AIMFamilyGrowth|FiniteDifferenceNewton|ForwardDifferenceSign|SchwarzHalfPlane|IntegerZeroUniqueness|ThreeQuarterDamping|NewtonBasis|NewtonDecay|NewtonInterpolation|RadicalPowerAnalytic|RadicalBranchObstruction|RadicalInterpolationObstruction|FullAIM34|AIM34Audit|IndependentStatementGuard".splitOn "|").map String.toName
  let moduleSet : NameSet := modules.foldl (fun s n => s.insert n) {}
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for m in modules do
    unless env.header.moduleNames.contains m do throwError "Missing project module {m}"
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]?).getD `UNKNOWN
    | none => `KERNEL_PRIMITIVE
  let kindOf : ConstantInfo → String
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient_primitive"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
  -- Exhaustive expression-DAG traversal: shared subexpressions are inspected
  -- once per expression, without omitting any constant or projection name.
  let refs (e : Expr) (s : NameSet) : NameSet := Id.run do
    let mut todo : Array Expr := #[e]
    let mut seen : ExprSet := {}
    let mut names := s
    while !todo.isEmpty do
      let a := todo.back!
      todo := todo.pop
      unless seen.contains a do
        seen := seen.insert a
        match a with
        | .const n _ => names := names.insert n
        | .proj n _ b => names := names.insert n; todo := todo.push b
        | .forallE _ t b _ | .lam _ t b _ => todo := (todo.push t).push b
        | .letE _ t v b _ => todo := ((todo.push t).push v).push b
        | .app f a => todo := (todo.push f).push a
        | .mdata _ b => todo := todo.push b
        | _ => pure ()
    return names
  let valid (e : Expr) (rs : NameSet) : Bool :=
    !rs.contains ``sorryAx && !e.hasMVar && !e.hasFVar && !e.hasLooseBVars
  let mut selected : Array (Name × ConstantInfo) := #[]
  for (n,ci) in kernel.constants.toList do
    if moduleSet.contains (moduleOf n) then selected := selected.push (n,ci)
  let expectedRows := "AIM34Definitions,AIM34.RealRooted,def|AIM34Definitions,AIM34.diagonal,def|AIM34Definitions,AIM34.IsMultiplierSequence,def|AIM34Definitions,AIM34.shiftedRadicalPower,def|AIM34Definitions,AIM34.FullProblem34,def|AIM34Definitions,AIM34.jensen,def|AIM34Definitions,AIM34.AllJensenRealRooted,def|AIM34Definitions,AIM34.forwardDifference,def|AIM34Definitions,AIM34.iteratedDifference,def|AIM34Definitions,AIM34.NotPolynomiallyBounded,def|AIM34Definitions,AIM34.diagonal_coeff,theorem|AIM34Definitions,AIM34.one_add_X_pow_realRooted,theorem|AIM34Definitions,AIM34.multiplier_allJensen,theorem|JensenIdentities,AIM34.jensen_coeff,theorem|JensenIdentities,AIM34.jensen_natDegree_le,theorem|JensenIdentities,AIM34.jensen_derivative,theorem|JensenIdentities,AIM34.jensen_forwardDifference,theorem|RealRootGeometry,AIM34.rootProduct,def|RealRootGeometry,AIM34.rootProduct_nonreal_eval_ne_zero,theorem|RealRootGeometry,AIM34.im_mul_inv_sub_neg,theorem|RealRootGeometry,AIM34.rootProduct_cons_logDerivative,theorem|RealRootGeometry,AIM34.rootProduct_logDerivative_im_mul_nonpos,theorem|RealRootGeometry,AIM34.rootProduct_logDerivative_im_mul_neg,theorem|RealRootGeometry,AIM34.eq_leadingCoeff_rootProduct,theorem|RealRootGeometry,AIM34.logDerivative_eq_rootProduct,theorem|RealRootGeometry,AIM34.complex_derivative_roots_real,theorem|RealRootGeometry,AIM34.realRooted_derivative,theorem|PolarRealRooted,AIM34.polarLinearSum,def|PolarRealRooted,AIM34.polarSquareSum,def|PolarRealRooted,AIM34.polar_factor_im,theorem|PolarRealRooted,AIM34.polar_factor_re,theorem|PolarRealRooted,AIM34.rootProduct_polar_log_im,theorem|PolarRealRooted,AIM34.rootProduct_polar_log_re,theorem|PolarRealRooted,AIM34.polarSquareSum_nonneg,theorem|PolarRealRooted,AIM34.roots_eq_neg_one_of_polarSquareSum_zero,theorem|PolarRealRooted,AIM34.complexPolar,def|PolarRealRooted,AIM34.complexPolar_leading_pow_zero,theorem|PolarRealRooted,AIM34.complexPolar_roots_real,theorem|JensenRootClosure,AIM34.realRooted_of_C_mul,theorem|JensenRootClosure,AIM34.realRooted_polar,theorem|JensenRootClosure,AIM34.allJensen_shift,theorem|JensenRootClosure,AIM34.allJensen_shift_add,theorem|JensenRootClosure,AIM34.allJensen_forwardDifference,theorem|NonnegativeRootGeometry,AIM34.re_inv_pos,theorem|NonnegativeRootGeometry,AIM34.rootProduct_eval_ne_zero_of_re_lt,theorem|NonnegativeRootGeometry,AIM34.rootProduct_logDerivative_re_nonneg_of_re_lt,theorem|NonnegativeRootGeometry,AIM34.rootProduct_logDerivative_re_pos_of_re_lt,theorem|NonnegativeRootGeometry,AIM34.eval_pos_of_nonneg_coeff_pos_constant,theorem|NonnegativeRootGeometry,AIM34.nonnegative_realRooted_roots_neg,theorem|NonnegativeRootGeometry,AIM34.eq_constant_of_nonnegative_realRooted_coeff_one_zero,theorem|JensenPositivity,AIM34.jensen_two,theorem|JensenPositivity,AIM34.jensen_two_logconcave,theorem|JensenPositivity,AIM34.allJensen_logconcave,theorem|JensenPositivity,AIM34.allJensen_zero_tail,theorem|JensenPositivity,AIM34.allJensen_interval_support,theorem|SequenceBounds,AIM34.SequenceBounds.AdjacentLogConcave,def|SequenceBounds,AIM34.SequenceBounds.IntervalPositiveSupport,def|SequenceBounds,AIM34.SequenceBounds.zero_of_zero_after_pos,theorem|SequenceBounds,AIM34.SequenceBounds.tail_adjacent_le_of_strict_drop,theorem|SequenceBounds,AIM34.SequenceBounds.tail_le_of_strict_drop,theorem|SequenceBounds,AIM34.SequenceBounds.bounded_of_strict_drop,theorem|SequenceBounds,AIM34.SequenceBounds.terminal_zero_of_drop_to_zero,theorem|SequenceBounds,AIM34.SequenceBounds.iteratedDifference_succ_right,theorem|SequenceBounds,AIM34.SequenceBounds.iteratedDifference_succ_left,theorem|SequenceBounds,AIM34.SequenceBounds.telescope_forwardDifference,theorem|SequenceBounds,AIM34.SequenceBounds.abs_polynomial_bound_of_forwardDifference,theorem|SequenceBounds,AIM34.SequenceBounds.abs_polynomial_bound_of_bounded_iteratedDifference,theorem|SequenceBounds,AIM34.SequenceBounds.polynomial_upper_bound_of_bounded_iteratedDifference,theorem|SequenceBounds,AIM34.SequenceBounds.iteratedDifference_monotone_of_notPolynomiallyBounded,theorem|SequenceBounds,AIM34.SequenceBounds.iteratedDifference_succ_nonneg_of_notPolynomiallyBounded,theorem|AIMFamilyGrowth,AIM34.shiftedRadicalPower_pos,theorem|AIMFamilyGrowth,AIM34.shiftedRadicalPower_gt_polynomial_of_bounds,theorem|AIMFamilyGrowth,AIM34.shiftedRadicalPower_notPolynomiallyBounded,theorem|AIMFamilyGrowth,AIM34.eventually_log_mul_sqrt_le,theorem|AIMFamilyGrowth,AIM34.shiftedRadicalPower_eventually_le_geometric,theorem|AIMFamilyGrowth,AIM34.shiftedRadicalPower_subexponential,theorem|FiniteDifferenceNewton,AIM34.iteratedDifference_succ_right,theorem|FiniteDifferenceNewton,AIM34.iteratedDifference_succ_left,theorem|FiniteDifferenceNewton,AIM34.finiteDifference_newton_inversion,theorem|ForwardDifferenceSign,AIM34.allJensen_iteratedDifference,theorem|ForwardDifferenceSign,AIM34.iteratedDifference_nonneg_of_allJensen,theorem|ForwardDifferenceSign,AIM34.multiplier_shiftedRadicalPower_all_differences_nonneg,theorem|SchwarzHalfPlane,AIM34.rightHalfPlane,def|SchwarzHalfPlane,AIM34.isOpen_rightHalfPlane,theorem|SchwarzHalfPlane,AIM34.halfPlaneToDisk,def|SchwarzHalfPlane,AIM34.diskToHalfPlane,def|SchwarzHalfPlane,AIM34.add_ofReal_ne_zero,theorem|SchwarzHalfPlane,AIM34.halfPlaneToDisk_mem_ball,theorem|SchwarzHalfPlane,AIM34.one_sub_ne_zero,theorem|SchwarzHalfPlane,AIM34.diskToHalfPlane_mem,theorem|SchwarzHalfPlane,AIM34.diskToHalfPlane_halfPlaneToDisk,theorem|SchwarzHalfPlane,AIM34.differentiableOn_halfPlaneToDisk,theorem|SchwarzHalfPlane,AIM34.differentiableOn_diskToHalfPlane,theorem|SchwarzHalfPlane,AIM34.schwarzQuotient,def|SchwarzHalfPlane,AIM34.differentiableOn_schwarzQuotient,theorem|SchwarzHalfPlane,AIM34.halfPlaneToDisk_mul_schwarzQuotient,theorem|SchwarzHalfPlane,AIM34.norm_schwarzQuotient_le,theorem|IntegerZeroUniqueness,AIM34.removeIntegerRoots,def|IntegerZeroUniqueness,AIM34.removeIntegerRoots_properties,theorem|IntegerZeroUniqueness,AIM34.removeIntegerRoots_factorization,theorem|IntegerZeroUniqueness,AIM34.norm_halfPlaneToDisk_sq_le,theorem|IntegerZeroUniqueness,AIM34.prod_norm_halfPlaneToDisk_sq_le,theorem|IntegerZeroUniqueness,AIM34.norm_sq_le_of_integer_zeros,theorem|IntegerZeroUniqueness,AIM34.eq_zero_on_lens_of_integer_zeros,theorem|IntegerZeroUniqueness,AIM34.eq_zero_of_bounded_rightHalfPlane_integer_zeros,theorem|ThreeQuarterDamping,AIM34.threeQuarterCos,def|ThreeQuarterDamping,AIM34.threeQuarterCos_pos,theorem|ThreeQuarterDamping,AIM34.re_cpow_threeQuarter_lower,theorem|ThreeQuarterDamping,AIM34.add_one_mem_slitPlane,theorem|ThreeQuarterDamping,AIM34.threeQuarterDamping,def|ThreeQuarterDamping,AIM34.differentiableOn_threeQuarterDamping,theorem|ThreeQuarterDamping,AIM34.norm_mul_threeQuarterDamping_le,theorem|ThreeQuarterDamping,AIM34.eq_zero_of_rightHalfPlane_threeQuarter_growth,theorem|NewtonBasis,AIM34.newtonBasis,def|NewtonBasis,AIM34.newtonBasis_zero,theorem|NewtonBasis,AIM34.newtonBasis_succ,theorem|NewtonBasis,AIM34.newtonBasis_natCast,theorem|NewtonBasis,AIM34.differentiable_newtonBasis,theorem|NewtonBasis,AIM34.norm_newtonBasis_le_pow,theorem|NewtonBasis,AIM34.norm_newtonBasis_le_choose,theorem|NewtonBasis,AIM34.norm_newtonBasis_le_eight_pow,theorem|NewtonDecay,AIM34.SubexponentialUpper,def|NewtonDecay,AIM34.NewtonInversion,def|NewtonDecay,AIM34.descFactorial_mul_lower,theorem|NewtonDecay,AIM34.pow_le_choose_mul,theorem|NewtonDecay,AIM34.coefficient_mul_pow_le,theorem|NewtonDecay,AIM34.subexponential_scaled_two,theorem|NewtonDecay,AIM34.summable_newton_coefficients_mul_pow,theorem|NewtonInterpolation,AIM34.newtonInterpolant,def|NewtonInterpolation,AIM34.norm_newtonTerm_le,theorem|NewtonInterpolation,AIM34.summable_newtonTerms,theorem|NewtonInterpolation,AIM34.differentiable_newtonInterpolant,theorem|NewtonInterpolation,AIM34.newtonInterpolant_natCast,theorem|NewtonInterpolation,AIM34.hasSum_choose_newton,theorem|NewtonInterpolation,AIM34.norm_newtonInterpolant_le,theorem|NewtonInterpolation,AIM34.entire_newton_interpolation_and_growth,theorem|RadicalPowerAnalytic,AIM34.radicalPowerCore,def|RadicalPowerAnalytic,AIM34.radicalPowerAnalytic,def|RadicalPowerAnalytic,AIM34.shiftedRightHalfPlane,def|RadicalPowerAnalytic,AIM34.isOpen_shiftedRightHalfPlane,theorem|RadicalPowerAnalytic,AIM34.isPreconnected_shiftedRightHalfPlane,theorem|RadicalPowerAnalytic,AIM34.shifted_mem_slitPlane,theorem|RadicalPowerAnalytic,AIM34.differentiableOn_radicalPowerAnalytic,theorem|RadicalPowerAnalytic,AIM34.radicalPowerCore_ofReal,theorem|RadicalPowerAnalytic,AIM34.radicalPowerAnalytic_ofReal,theorem|RadicalPowerAnalytic,AIM34.sqrt_mul_log_le_threeQuarter,theorem|RadicalPowerAnalytic,AIM34.radicalPowerReal_le_threeQuarter,theorem|RadicalPowerAnalytic,AIM34.norm_radicalPowerCore_le,theorem|RadicalPowerAnalytic,AIM34.one_le_norm_add_one,theorem|RadicalPowerAnalytic,AIM34.norm_le_norm_add_one,theorem|RadicalPowerAnalytic,AIM34.norm_radicalPowerAnalytic_threeQuarter,theorem|RadicalBranchObstruction,AIM34.radicalRealDerivative,def|RadicalBranchObstruction,AIM34.hasDerivAt_radicalReal,theorem|RadicalBranchObstruction,AIM34.tendsto_radicalRealDerivative_atBot,theorem|RadicalBranchObstruction,AIM34.no_entire_radicalPower_extension,theorem|RadicalInterpolationObstruction,AIM34.norm_entire_radical_interpolant_threeQuarter,theorem|RadicalInterpolationObstruction,AIM34.radical_interpolant_eq_on_halfPlane,theorem|RadicalInterpolationObstruction,AIM34.radical_interpolant_eq_on_shiftedHalfPlane,theorem|RadicalInterpolationObstruction,AIM34.no_entire_radicalPower_interpolant,theorem|FullAIM34,AIM34.not_multiplier_shiftedRadicalPower,theorem|FullAIM34,AIM34.exists_counterexample_polynomial,theorem|FullAIM34,AIM34.fullProblem34,theorem|FullAIM34,AIM34.problem34_positive_integer_shift,theorem|FullAIM34,AIM34.problem34_one_indexed_shift,theorem|IndependentStatementGuard,AIM34Independent.actualAllRealShifts,theorem|IndependentStatementGuard,AIM34Independent.actualFiniteWitness,theorem|IndependentStatementGuard,AIM34Independent.actualIntegerShifts,theorem|IndependentStatementGuard,AIM34Independent.actualOneIndexedShifts,theorem|IndependentStatementGuard,AIM34Independent.actualFullAlias,theorem|IndependentStatementGuard,AIM34Independent.actualCoefficient,theorem".splitOn "|"
  for row in expectedRows do
    match row.splitOn "," with
    | [m,n,k] =>
      let name := n.toName
      let some ci := kernel.find? name | throwError "MISSING_SOURCE_DECLARATION {n}"
      unless moduleOf name == m.toName do throwError "WRONG_SOURCE_MODULE {n}"
      unless kindOf ci == k && !ci.isUnsafe && !ci.isPartial do throwError "WRONG_SOURCE_KIND_OR_SAFETY {n}"
      logInfo m!"EXPECTED_SOURCE_PRESENT|{m}|{n}|{k}"
    | _ => throwError "MALFORMED_INVENTORY"
  let mut safeSelected : Array (Name × ConstantInfo) := #[]
  let mut unsafeCount := 0
  for (n,ci) in selected do
    if ci.isUnsafe || ci.isPartial then
      unsafeCount := unsafeCount + 1
      logInfo m!"COMPILER_IMPLEMENTATION_NOT_PROOF|{moduleOf n}|{n}|{kindOf ci}|unsafe={ci.isUnsafe}|partial={ci.isPartial}"
    else
      unless !ci.isPartial do throwError "Partial mathematical project record {n}"
      safeSelected := safeSelected.push (n,ci)
  let mut bodyCount := 0
  for (n,ci) in safeSelected do
    liftIO <| IO.println s!"AUDIT_PROGRESS|PROJECT|{n}"
    let typerefs := refs ci.type {}
    unless valid ci.type typerefs do throwError "Invalid full type {n}"
    let mut allrefs := typerefs
    let mut bodyHash := "primitive/no-value"
    if let some v := ci.value? true then
      let bodyrefs := refs v {}
      unless valid v bodyrefs do throwError "Invalid full body {n}"
      bodyCount := bodyCount + 1
      bodyHash := toString (hash v).toNat
      for ref in bodyrefs.toList do allrefs := allrefs.insert ref
      logInfo m!"FULL_BODY_REFERENCES|{n}|{bodyrefs.toList}"
      logInfo m!"BODY_CHECKED|{n}|complete_expr_hash={bodyHash}"
    else
      unless (["inductive", "constructor", "recursor"] : List String).contains (kindOf ci) do
        throwError "Unexpected mathematical record without body {n}"
      logInfo m!"KERNEL_PRIMITIVE_NO_VALUE|{moduleOf n}|{n}|{kindOf ci}"
    for ref in allrefs.toList do
      let some rci := kernel.find? ref | throwError "Unresolved reference {n} -> {ref}"
      unless !rci.isUnsafe && !rci.isPartial do throwError "Unsafe/partial reference {n} -> {ref}"
    logInfo m!"RECORD|{moduleOf n}|{n}|{kindOf ci}|{(hash ci.type).toNat}|{bodyHash}"
    logInfo m!"FULL_TYPE_REFERENCES|{n}|{typerefs.toList}"
    -- The complete union closure below includes EVERY safe project declaration.
    -- Thus its axiom whitelist check certifies every source without repeatedly
    -- traversing the same large proof once per downstream declaration.
    logInfo m!"SAFE_AXIOMS_COVERED_BY_COMPLETE_CLOSURE|{n}"
    let ty ← liftTermElabM (Lean.Meta.ppExpr ci.type)
    logInfo m!"TYPE_BEGIN|{n}"
    logInfo ty
    logInfo m!"TYPE_END|{n}"
  let mut codegen := 0
  for (n,idx) in env.const2ModIdx.toList do
    if moduleSet.contains ((env.header.moduleNames[idx.toNat]?).getD `UNKNOWN) &&
        (kernel.find? n).isNone then
      codegen := codegen + 1
      logInfo m!"EXTRA_CODEGEN_IMPLEMENTATION|{n}"
  -- Walk the complete logical dependency closure, including
  -- projection structure names and recursor rule bodies, not only final-theorem axioms.
  let mut todo := safeSelected.map Prod.fst
  let mut seen : NameSet := {}
  let mut closureCount := 0
  let mut closureBodies := 0
  let mut closureRules := 0
  let mut closureAxioms : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      seen := seen.insert n
      let some ci := kernel.find? n | throwError "Unresolved transitive constant {n}"
      unless !ci.isUnsafe && !ci.isPartial do throwError "Unsafe/partial transitive constant {n}"
      closureCount := closureCount + 1
      if closureCount % 1000 == 0 then
        liftIO <| IO.println s!"AUDIT_PROGRESS|CLOSURE|{closureCount}|{n}"
      let mut rs := refs ci.type {}
      unless valid ci.type rs do throwError "Invalid transitive type {n}"
      let mut bodyHash := "primitive/no-value"
      if let some v := ci.value? true then
        let br := refs v {}
        unless valid v br do throwError "Invalid transitive body {n}"
        closureBodies := closureBodies + 1
        bodyHash := toString (hash v).toNat
        for ref in br.toList do rs := rs.insert ref
      match ci with
      | .axiomInfo _ =>
        unless allowed.contains n do throwError "Nonstandard transitive axiom {n}"
        closureAxioms := closureAxioms.insert n
      | .inductInfo v =>
        for c in v.ctors ++ v.all do rs := rs.insert c
      | .ctorInfo v => rs := rs.insert v.induct
      | .recInfo v =>
        for c in v.all do rs := rs.insert c
        for rule in v.rules do
          let rr := refs rule.rhs {}
          unless valid rule.rhs rr do throwError "Invalid recursor rule {n}"
          closureRules := closureRules + 1
          logInfo m!"CLOSURE_RECURSOR_RULE|{n}|{rule.ctor}|{(hash rule.rhs).toNat}|{rr.toList}"
          rs := rs.insert rule.ctor
          for ref in rr.toList do rs := rs.insert ref
      | _ => pure ()
      for ref in rs.toList do
        unless seen.contains ref do todo := todo.push ref
      logInfo m!"CLOSURE_REFERENCES|{n}|{rs.toList}"
      logInfo m!"CLOSURE_RECORD|{moduleOf n}|{n}|{kindOf ci}|{(hash ci.type).toNat}|{bodyHash}"
  unless closureAxioms.toList.length == 3 do throwError "Unexpected axiom inventory {closureAxioms.toList}"
  logInfo m!"CLOSURE_COMPLETE|{seen.toList.length}|{closureBodies}|{closureRules}|{closureAxioms.toList}"
  logInfo m!"INDEPENDENT_AUDIT_COMPLETE|source_modules={modules.length}|kernel={selected.size}|safe={safeSelected.size}|bodies={bodyCount}|compiler_unsafe={unsafeCount}|mathematical_unsafe=0|partial=0|codegen={codegen}"
