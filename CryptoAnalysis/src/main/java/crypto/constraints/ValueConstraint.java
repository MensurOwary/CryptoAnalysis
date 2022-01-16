package crypto.constraints;

import com.google.common.collect.Multimap;
import crypto.analysis.AnalysisSeedWithSpecification;
import crypto.analysis.ClassSpecification;
import crypto.analysis.errors.ConstraintError;
import crypto.extractparameter.CallSiteWithExtractedValue;
import crypto.extractparameter.CallSiteWithParamIndex;
import crypto.extractparameter.ExtractedValue;
import crypto.interfaces.ISLConstraint;
import crypto.rules.CrySLObject;
import crypto.rules.CrySLSplitter;
import crypto.rules.CrySLValueConstraint;

import java.util.*;
import java.util.stream.Collectors;

public class ValueConstraint extends EvaluableConstraint {

    private final ClassSpecification classSpec;
    private final AnalysisSeedWithSpecification object;

    public ValueConstraint(CrySLValueConstraint c,
                           Multimap<CallSiteWithParamIndex, ExtractedValue> parsAndVals,
                           ClassSpecification classSpec,
                           AnalysisSeedWithSpecification object) {
        super(c, parsAndVals);
        this.classSpec = classSpec;
        this.object = object;
    }

    @Override
    public void evaluate() {
        CrySLValueConstraint valCons = (CrySLValueConstraint) origin;

        CrySLObject var = valCons.getVar();
        final List<Map.Entry<String, CallSiteWithExtractedValue>> vals = getValFromVar(var, valCons);
        if (vals.isEmpty()) {
            // TODO: Check whether this works as desired
            return;
        }
        for (Map.Entry<String, CallSiteWithExtractedValue> val : vals) {
            List<String> values = valCons.getValueRange().parallelStream().map(e -> e.toLowerCase()).collect(Collectors.toList());
            if (!values.contains(val.getKey().toLowerCase())) {
                errors.add(new ConstraintError(val.getValue(), classSpec.getRule(), object, valCons));
            }
        }
        return;
    }

    private List<Map.Entry<String, CallSiteWithExtractedValue>> getValFromVar(CrySLObject var, ISLConstraint cons) {
        final String varName = var.getVarName();
        final Map<String, CallSiteWithExtractedValue> valueCollection = extractValueAsString(varName, cons);
        List<Map.Entry<String, CallSiteWithExtractedValue>> vals = new ArrayList<>();
        if (valueCollection.isEmpty()) {
            return vals;
        }
        for (Map.Entry<String, CallSiteWithExtractedValue> e : valueCollection.entrySet()) {
            CrySLSplitter splitter = var.getSplitter();
            final CallSiteWithExtractedValue location = e.getValue();
            String val = e.getKey();
            if (splitter != null) {
                int ind = splitter.getIndex();
                String splitElement = splitter.getSplitter();
                if (ind > 0) {
                    String[] splits = val.split(splitElement);
                    if (splits.length > ind) {
                        vals.add(new AbstractMap.SimpleEntry<>(splits[ind], location));
                    } else {
                        vals.add(new AbstractMap.SimpleEntry<>("", location));
                    }
                } else {
                    vals.add(new AbstractMap.SimpleEntry<>(val.split(splitElement)[ind], location));
                }
            } else {
                vals.add(new AbstractMap.SimpleEntry<>(val, location));
            }
        }
        return vals;
    }

}
