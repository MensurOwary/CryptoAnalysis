package crypto.reporting;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.collect.Table;

import crypto.analysis.IAnalysisSeed;
import crypto.analysis.errors.AbstractError;
import crypto.analysis.errors.ErrorWithObjectAllocation;
import crypto.rules.CrySLRule;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.Stmt;

public class ReporterHelper {

    /**
     * Generates analysis report content for {@link CommandLineReporter} and {@link TXTReporter}
     *
     * @param rules            a {@link List} with {@link CrySLRule} rules
     * @param objects          a{@link Collection} with {@link IAnalysisSeed} objects
     * @param secureObjects    a {@link List} with {@link IAnalysisSeed} secureObjects
     * @param errorMarkers     a {@link Table} containing {@link SootClass},{@link SootMethod}
     *                         and a {@link Set} of {@link AbstractError} of the errors found during analysis
     * @param errorMarkerCount a {@link Map} containing {@link Class} class of error and
     *                         {@link Integer} number of errors
     * @return report {@link String} of the analysis
     */
    public static String generateReport(List<CrySLRule> rules, Collection<IAnalysisSeed> objects,
                                        List<IAnalysisSeed> secureObjects, Table<SootClass, SootMethod, Set<AbstractError>> errorMarkers,
                                        Map<Class, Integer> errorMarkerCount) {
        StringBuilder report = new StringBuilder();

        report.append("Ruleset: \n");
        for (CrySLRule r : rules) {
            report.append(String.format("\t%s\n", r.getClassName()));
        }

        report.append("\n");

        report.append("Analyzed Objects: \n");
        for (IAnalysisSeed r : objects) {
            report.append("\tObject:\n")
                    .append(String.format("\t\tVariable: %s\n", r.var().value()))
                    .append(String.format("\t\tType: %s\n", r.getType()))
                    .append(String.format("\t\tStatement: %s\n", r.stmt().getUnit().get()))
                    .append(String.format("\t\tMethod: %s\n", r.getMethod()))
                    .append(String.format("\t\tSHA-256: %s\n", r.getObjectId()))
                    .append(String.format("\t\tSecure: %s\n", secureObjects.contains(r)));
        }


        report.append("\n");
        for (SootClass c : errorMarkers.rowKeySet()) {
            // filters out Java lib classes
            if (c.getName().startsWith("java.")) continue;

            report.append(String.format("Findings in Java Class: %s\n", c.getName()));
            for (Entry<SootMethod, Set<AbstractError>> e : errorMarkers.row(c).entrySet()) {
                report.append(String.format("\n\t in Method: %s\n", e.getKey().getSubSignature()));
                for (AbstractError marker : e.getValue()) {
                    report.append(String.format("\t\t%s violating CrySL rule for %s", marker.getClass().getSimpleName(), marker.getRule().getClassName()));
                    if (marker instanceof ErrorWithObjectAllocation) {
                        report.append(String.format(" (on Object #%s)\n", ((ErrorWithObjectAllocation) marker).getObjectLocation().getObjectId()));
                    } else {
                        report.append("\n");
                    }
                    report.append(String.format("\t\t\t%s\n", marker.toErrorMarkerString()));
                    final Stmt stmt = marker.getErrorLocation().getUnit().get();
                    final String lineNumberTag = stmt.getTag("LineNumberTag").toString();
                    report.append(String.format("\t\t\tat statement: [%s] %s\n\n", lineNumberTag, stmt));
                }
            }
            report.append("\n");
        }
        report.append("======================= CryptoAnalysis Summary ==========================\n");
        report.append(String.format("\tNumber of CrySL rules: %s\n", rules.size()));
        report.append(String.format("\tNumber of Objects Analyzed: %s\n", objects.size()));
        if (errorMarkers.rowKeySet().isEmpty()) {
            report.append("No violation of any of the rules found.\n");
        } else {
            report.append("\n\tCryptoAnalysis found the following violations. For details see description above.\n");
            for (Entry<Class, Integer> e : errorMarkerCount.entrySet()) {
                report.append(String.format("\t%s: %s\n", e.getKey().getSimpleName(), e.getValue()));
            }
        }
        report.append("=====================================================================");
        return report.toString();
    }

}
