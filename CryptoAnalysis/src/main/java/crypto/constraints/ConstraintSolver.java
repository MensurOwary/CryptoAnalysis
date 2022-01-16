package crypto.constraints;

import boomerang.jimple.Statement;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import crypto.analysis.*;
import crypto.analysis.errors.AbstractError;
import crypto.analysis.errors.ImpreciseValueExtractionError;
import crypto.extractparameter.CallSiteWithParamIndex;
import crypto.extractparameter.ExtractedValue;
import crypto.interfaces.ICrySLPredicateParameter;
import crypto.interfaces.ISLConstraint;
import crypto.rules.CrySLComparisonConstraint;
import crypto.rules.CrySLConstraint;
import crypto.rules.CrySLPredicate;
import crypto.rules.CrySLValueConstraint;
import soot.Type;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

public class ConstraintSolver {

    public final static List<String> PREDEFINED_PREDICATE_NAMES = Arrays.asList("callTo", "noCallTo", "neverTypeOf", "length", "notHardCoded", "instanceOf", "callToEarlier");

    private final Set<ISLConstraint> relConstraints = Sets.newHashSet();
    private final List<ISLConstraint> requiredPredicates = Lists.newArrayList();
    private final Collection<Statement> collectedCalls;
    private final Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals;
    private final CrySLResultsReporter reporter;
    private final AnalysisSeedWithSpecification object;
    private final ClassSpecification classSpec;
    private final Collection<CallSiteWithParamIndex> parameterAnalysisQuerySites;
    private final Multimap<CallSiteWithParamIndex, Type> propagatedTypes;

    public ConstraintSolver(AnalysisSeedWithSpecification object, Collection<Statement> collectedCalls, CrySLResultsReporter crySLResultsReporter) {
        this.object = object;
        this.classSpec = object.getSpec();
        this.parsAndVals = object.getParameterAnalysis().getCollectedValues();
        this.propagatedTypes = object.getParameterAnalysis().getPropagatedTypes();
        this.parameterAnalysisQuerySites = object.getParameterAnalysis().getAllQuerySites();
        this.collectedCalls = collectedCalls;
        List<ISLConstraint> allConstraints = this.classSpec.getRule().getConstraints();
        for (ISLConstraint cons : allConstraints) {

            Set<String> involvedVarNames = cons.getInvolvedVarNames();
            for (CallSiteWithParamIndex cwpi : this.parameterAnalysisQuerySites) {
                involvedVarNames.remove(cwpi.getVarName());
            }

            if (involvedVarNames.isEmpty() || (cons.toString().contains("speccedKey") && involvedVarNames.size() == 1)) {
                if (cons instanceof CrySLPredicate) {
                    RequiredCrySLPredicate pred = retrieveValuesForPred(cons);
                    if (pred != null) {
                        CrySLPredicate innerPred = pred.getPred();
                        if (innerPred != null) {
                            relConstraints.add(innerPred);
                            requiredPredicates.add(pred);
                        }
                    }
                } else if (cons instanceof CrySLConstraint) {
                    ISLConstraint right = ((CrySLConstraint) cons).getRight();
                    if (right instanceof CrySLPredicate && !PREDEFINED_PREDICATE_NAMES.contains(((CrySLPredicate) right).getPredName())) {
                        requiredPredicates.add(collectAlternativePredicates((CrySLConstraint) cons, null));
                    } else {
                        relConstraints.add(cons);
                    }
                } else {
                    relConstraints.add(cons);
                }
            }
        }
        this.reporter = crySLResultsReporter;
    }

    private ISLConstraint collectAlternativePredicates(CrySLConstraint cons, AlternativeReqPredicate alt) {
        CrySLPredicate right = (CrySLPredicate) cons.getRight();
        if (alt == null) {
            alt = new AlternativeReqPredicate(right, right.getLocation());
        } else {
            alt.addAlternative(right);
        }

        if (cons.getLeft() instanceof CrySLPredicate) {
            alt.addAlternative((CrySLPredicate) cons.getLeft());
        } else {
            return collectAlternativePredicates((CrySLConstraint) cons.getLeft(), alt);
        }

        return alt;
    }

    private RequiredCrySLPredicate retrieveValuesForPred(ISLConstraint cons) {
        CrySLPredicate pred = (CrySLPredicate) cons;
        for (CallSiteWithParamIndex cwpi : this.parameterAnalysisQuerySites) {
            for (ICrySLPredicateParameter p : pred.getParameters()) {
                // TODO: FIX Cipher rule
                if (p.getName().equals("transformation"))
                    continue;
                if (cwpi.getVarName().equals(p.getName())) {
                    return new RequiredCrySLPredicate(pred, cwpi.stmt());
                }
            }
        }
        return null;
    }

    public int evaluateRelConstraints() {
        int fail = 0;
        for (ISLConstraint con : relConstraints) {
            EvaluableConstraint currentConstraint = createConstraint(con);
            currentConstraint.evaluate();
            for (AbstractError e : currentConstraint.getErrors()) {
                if (e instanceof ImpreciseValueExtractionError) {
                    reporter.reportError(object, new ImpreciseValueExtractionError(con, e.getErrorLocation(), e.getRule()));
                    break;
                } else {
                    fail++;
                    reporter.reportError(object, e);
                }
            }
        }
        return fail;
    }

    public EvaluableConstraint createConstraint(ISLConstraint con) {
        if (con instanceof CrySLComparisonConstraint) {
            final Function<CrySLPredicate, PredicateConstraint> predicateCreator = predicate ->
                    new PredicateConstraint(predicate, parsAndVals, parameterAnalysisQuerySites, propagatedTypes, classSpec, object, collectedCalls);

            return new ComparisonConstraint(
                    (CrySLComparisonConstraint) con, parsAndVals,
                    predicateCreator,
                    classSpec, object
            );
        } else if (con instanceof CrySLValueConstraint) {
            return new ValueConstraint((CrySLValueConstraint) con, parsAndVals, classSpec, object);
        } else if (con instanceof CrySLPredicate) {
            return new PredicateConstraint((CrySLPredicate) con, parsAndVals, parameterAnalysisQuerySites, propagatedTypes, classSpec, object, collectedCalls);
        } else if (con instanceof CrySLConstraint) {
            return new BinaryConstraint((CrySLConstraint) con, parsAndVals, this::createConstraint);
        }
        return null;
    }

    /**
     * @return the relConstraints
     */
    public Set<ISLConstraint> getRelConstraints() {
        return relConstraints;
    }

    public List<ISLConstraint> getRequiredPredicates() {
        return requiredPredicates;
    }


}
