package crypto;

import boomerang.callgraph.ObservableDynamicICFG;
import boomerang.callgraph.ObservableICFG;
import boomerang.debugger.Debugger;
import boomerang.debugger.IDEVizDebugger;
import boomerang.jimple.Statement;
import boomerang.preanalysis.BoomerangPretransformer;
import com.google.common.base.Stopwatch;
import crypto.analysis.*;
import crypto.analysis.CryptoScannerSettings.ControlGraph;
import crypto.analysis.CryptoScannerSettings.ReportFormat;
import crypto.analysis.errors.AbstractError;
import crypto.analysis.errors.ErrorWithObjectAllocation;
import crypto.exceptions.CryptoAnalysisException;
import crypto.exceptions.CryptoAnalysisParserException;
import crypto.preanalysis.SeedFactory;
import crypto.providerdetection.ProviderDetection;
import crypto.reporting.*;
import crypto.rules.CrySLRule;
import crypto.rules.CrySLRuleReader;
import de.tu_darmstadt.stg.mubench.cli.*;
import ideal.IDEALSeedSolver;
import org.apache.commons.io.FileUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.core.io.Resource;
import org.springframework.core.io.support.PathMatchingResourcePatternResolver;
import soot.*;
import soot.jimple.Stmt;
import soot.options.Options;
import soot.tagkit.SourceFileTag;
import typestate.TransitionFunction;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Runner {

    public static void main(String[] args) throws Exception {
        List<DetectorFinding> detectorOutput = getDetectorOutput(args);
        System.out.println(detectorOutput.size());
    }

    public static List<DetectorFinding> getDetectorOutput(String[] args) {
        CrySLResultsReporter reporter = CogniCryptScanner.run(args);

        List<DetectorFinding> findings = new ArrayList<>();

        for (ICrySLResultsListener listener : reporter.getListeners()) {
            if (listener instanceof CollectErrorListener) {
                CollectErrorListener cel = (CollectErrorListener) listener;

                for (AbstractError error : cel.getErrors()) {
                    Statement errorLocation = error.getErrorLocation();

                    // getting method name
                    String name = errorLocation.getMethod().getName();
                    String subSignature = errorLocation.getMethod().getSubSignature();
                    int startFrom = subSignature.indexOf(name);
                    subSignature = subSignature.substring(startFrom);

                    // getting file name
                    SootClass aClass = errorLocation.getMethod().getDeclaringClass();
                    SourceFileTag sourceFileTag = (SourceFileTag) aClass.getTag("SourceFileTag");
                    String sourceFile = sourceFileTag.getSourceFile();

                    DetectorFinding violation = new DetectorFinding(
                            sourceFile, subSignature
                    );

                    if (errorLocation.getUnit().isPresent()) {
                        final Stmt stmt = errorLocation.getUnit().get();
                        final String lineNumberTag = stmt.getTag("LineNumberTag").toString();
                        violation.put("line_number", lineNumberTag);
                    }

                    violation.put("description", toString(error));

                    findings.add(violation);
                }
            }
        }

        return findings;
    }

    private static String toString(AbstractError marker) {
        StringBuilder report = new StringBuilder();
        report.append(String.format("%s violating CrySL rule for %s", marker.getClass().getSimpleName(), marker.getRule().getClassName()));
        if (marker instanceof ErrorWithObjectAllocation) {
            report.append(String.format(" (on Object #%s)\n", ((ErrorWithObjectAllocation) marker).getObjectLocation().getObjectId()));
        } else {
            report.append("\n");
        }
        report.append(String.format("\t%s\n", marker.toErrorMarkerString()));
        final Stmt stmt = marker.getErrorLocation().getUnit().get();
        final String lineNumberTag = stmt.getTag("LineNumberTag").toString();
        report.append(String.format("\tat statement: [%s] %s\n\n", lineNumberTag, stmt));

        return report.toString();
    }

}

abstract class CogniCryptScanner {

    private static final CryptoScannerSettings settings = new CryptoScannerSettings();
    private boolean hasSeeds;
    private static Stopwatch callGraphWatch;
    private static List<CrySLRule> rules = new ArrayList<>();
    private static String rulesetRootPath;
    private static final Logger LOGGER = LoggerFactory.getLogger(CogniCryptScanner.class);
    private CryptoScanner scanner;

    public static CrySLResultsReporter run(String[] args) {
        CogniCryptScanner runner = createFromCLISettings(args);
        runner.exec();
        return runner.getScanner().getAnalysisListener();
    }

    public static CogniCryptScanner createFromCLISettings(String[] args) {
        try {
            settings.parseSettingsFromCLI(args);
        } catch (CryptoAnalysisParserException e) {
            LOGGER.error("Parser failed with error: " + e.getClass().toString(), e);
        }

        return new CogniCryptScanner() {

            @Override
            protected String applicationClassPath() {
                return settings.getApplicationPath();
            }

            @Override
            protected List<CrySLRule> getRules() {
                try {
                    rules.addAll(loadAllRules());
                    System.out.println(rules.size());
                } catch (URISyntaxException | CryptoAnalysisException | IOException e) {
                    e.printStackTrace();
                }
                return rules;
            }
        };
    }

    public List<CrySLRule> loadAllRules() throws URISyntaxException, CryptoAnalysisException, IOException {
        return Stream.of(new PathMatchingResourcePatternResolver().getResources("/Rules/*"))
                .map(resource -> {
                    try {
                        String[] pieces = resource.getFilename().split("\\.");
                        File newPath = File.createTempFile(
                                pieces[0],
                                "." + pieces[1],
                                null
                        );
                        FileUtils.copyInputStreamToFile(resource.getInputStream(), newPath);
                        return CrySLRuleReader.readFromSourceFile(newPath);
                    } catch (CryptoAnalysisException | IOException e) {
                        e.printStackTrace();
                    }
                    return null;
                }).filter(Objects::nonNull).collect(Collectors.toList());
    }

    public void exec() {
        Stopwatch stopwatch = Stopwatch.createStarted();
        if (isPreAnalysis()) {
            try {
                initializeSootWithEntryPointAllReachable(false);
            } catch (CryptoAnalysisException e) {
                LOGGER.error("Error happened when executing HeadlessCryptoScanner.", e);
            }
            LOGGER.info("Pre-Analysis soot setup done in {} ", stopwatch);
            checkIfUsesObject();
            LOGGER.info("Pre-Analysis  finished in {}", stopwatch);
        }
        if (!isPreAnalysis() || hasSeeds()) {
            LOGGER.info("Using call graph algorithm {}", callGraphAlgorithm());
            try {
                initializeSootWithEntryPointAllReachable(true);
            } catch (CryptoAnalysisException e) {
                LOGGER.error("Error happened when executing HeadlessCryptoScanner.", e);
            }
            LOGGER.info("Analysis soot setup done in {} ", stopwatch);
            analyse();
            LOGGER.info("Analysis finished in {}", stopwatch);
        }
    }

    public boolean hasSeeds() {
        return hasSeeds;
    }

    private void checkIfUsesObject() {
        final SeedFactory seedFactory = new SeedFactory(CogniCryptScanner.rules);
        PackManager.v().getPack("jap").add(new Transform("jap.myTransform", new BodyTransformer() {
            protected void internalTransform(Body body, String phase, Map options) {
                if (!body.getMethod().getDeclaringClass().isApplicationClass()) {
                    return;
                }
                for (Unit u : body.getUnits()) {
                    seedFactory.generate(body.getMethod(), u);
                }
            }
        }));
        PhaseOptions.v().setPhaseOption("jap.npc", "on");
        PackManager.v().runPacks();
        hasSeeds = seedFactory.hasSeeds();
    }

    private void analyse() {
        Transform transform = new Transform("wjtp.ifds", createAnalysisTransformer());
        PackManager.v().getPack("wjtp").add(transform);
        callGraphWatch = Stopwatch.createStarted();
        PackManager.v().getPack("cg").apply();
        PackManager.v().getPack("wjtp").apply();
    }

    public String toString() {
        String s = "HeadllessCryptoScanner: \n";
        s += "\tSoftwareIdentifier: " + softwareIdentifier() + "\n";
        s += "\tApplicationClassPath: " + applicationClassPath() + "\n";
        s += "\tSootClassPath: " + sootClassPath() + "\n\n";
        return s;
    }

    private Transformer createAnalysisTransformer() {
        return new SceneTransformer() {

            @Override
            protected void internalTransform(String phaseName, Map<String, String> options) {
                BoomerangPretransformer.v().reset();
                BoomerangPretransformer.v().apply();
                ObservableDynamicICFG observableDynamicICFG = new ObservableDynamicICFG(false);
                List<CrySLRule> rules = CogniCryptScanner.rules;
                ErrorMarkerListener fileReporter;
                if (reportFormat() != null) {
                    switch (reportFormat()) {
                        case SARIF:
                            fileReporter = new SARIFReporter(getOutputFolder(), rules);
                            break;
                        case CSV:
                            fileReporter = new CSVReporter(getOutputFolder(), softwareIdentifier(), rules, callGraphWatch.elapsed(TimeUnit.MILLISECONDS));
                            break;
                        default:
                            fileReporter = new TXTReporter(getOutputFolder(), rules);
                    }
                } else {
                    fileReporter = new CommandLineReporter(rules);
                }
                final CrySLResultsReporter reporter = new CrySLResultsReporter();
                if (getAdditionalListener() != null)
                    reporter.addReportListener(getAdditionalListener());
                reporter.addReportListener(new CollectErrorListener());
                CryptoScanner scanner = new CryptoScanner() {

                    @Override
                    public ObservableICFG<Unit, SootMethod> icfg() {
                        return observableDynamicICFG;
                    }

                    @Override
                    public CrySLResultsReporter getAnalysisListener() {
                        return reporter;
                    }

                    @Override
                    public Debugger<TransitionFunction> debugger(IDEALSeedSolver<TransitionFunction> solver, IAnalysisSeed seed) {
                        if (enableVisualization()) {
                            if (getOutputFolder() == null) {
                                LOGGER.error("The visualization requires the --reportDir option.");
                            }
                            File vizFile = new File(getOutputFolder() + "/viz/ObjectId#" + seed.getObjectId() + ".json");
                            vizFile.getParentFile().mkdirs();
                            return new IDEVizDebugger<>(vizFile, icfg());
                        }
                        return super.debugger(solver, seed);
                    }
                };

                reporter.addReportListener(fileReporter);

                if (providerDetection()) {
                    ProviderDetection providerDetection = new ProviderDetection();

                    if (rulesetRootPath == null) {
                        rulesetRootPath = System.getProperty("user.dir") + File.separator + "src" + File.separator + "main" + File.separator + "resources";
                    }
                    String detectedProvider = providerDetection.doAnalysis(observableDynamicICFG, rulesetRootPath);
                    if (detectedProvider != null) {
                        rules.clear();
                        switch (settings.getRulesetPathType()) {
                            case DIR:
                                rules.addAll(providerDetection.chooseRules(rulesetRootPath + File.separator + detectedProvider));
                                break;
                            case ZIP:
                                rules.addAll(providerDetection.chooseRulesZip(rulesetRootPath + File.separator + detectedProvider + ".zip"));
                                break;
                            default:
                                rules.addAll(providerDetection.chooseRules(rulesetRootPath + File.separator + detectedProvider));
                        }
                    }
                }

                scanner.scan(rules);

                CogniCryptScanner.this.scanner = scanner;
            }
        };
    }

    protected CrySLAnalysisListener getAdditionalListener() {
        return null;
    }

    private void initializeSootWithEntryPointAllReachable(boolean wholeProgram) throws CryptoAnalysisException {
        G.v().reset();
        Options.v().set_whole_program(wholeProgram);
        switch (callGraphAlgorithm()) {
            case CHA:
                Options.v().setPhaseOption("cg.cha", "on");
                break;
            case SPARKLIB:
                Options.v().setPhaseOption("cg.spark", "on");
                Options.v().setPhaseOption("cg", "library:any-subtype");
                break;
            case SPARK:
                Options.v().setPhaseOption("cg.spark", "on");
                break;
            default:
                throw new CryptoAnalysisException("No call graph option selected out of: CHA, SPARK_LIBRARY and SPARK");
        }
        Options.v().set_output_format(Options.output_format_none);
        Options.v().set_no_bodies_for_excluded(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_keep_line_number(true);
        // JAVA 8
        if (getJavaVersion() < 9) {
            Options.v().set_prepend_classpath(true);
            Options.v().set_soot_classpath(sootClassPath() + File.pathSeparator + pathToJCE());
        }
        // JAVA VERSION 9 && IS A CLASSPATH PROJECT
        else if (getJavaVersion() >= 9 && !isModularProject()) {
            Options.v().set_soot_classpath("VIRTUAL_FS_FOR_JDK" + File.pathSeparator + sootClassPath());
        }
        // JAVA VERSION 9 && IS A MODULEPATH PROJECT
        else if (getJavaVersion() >= 9 && isModularProject()) {
            Options.v().set_prepend_classpath(true);
            Options.v().set_soot_modulepath(sootClassPath());
        }
        Options.v().set_process_dir(Arrays.asList(applicationClassPath().split(File.pathSeparator)));
        Options.v().set_include(getIncludeList());
        Options.v().set_exclude(getExcludeList());
        Options.v().set_full_resolver(true);
        Scene.v().loadNecessaryClasses();
        Scene.v().setEntryPoints(getEntryPoints());
    }

    private List<SootMethod> getEntryPoints() {
        List<SootMethod> entryPoints = new ArrayList<>();
        entryPoints.addAll(EntryPoints.v().application());
        entryPoints.addAll(EntryPoints.v().methodsOfApplicationClasses());
        return entryPoints;
    }

    private List<String> getIncludeList() {
        List<String> includeList = new LinkedList<String>();
        includeList.add("java.lang.AbstractStringBuilder");
        includeList.add("java.lang.Boolean");
        includeList.add("java.lang.Byte");
        includeList.add("java.lang.Class");
        includeList.add("java.lang.Integer");
        includeList.add("java.lang.Long");
        includeList.add("java.lang.Object");
        includeList.add("java.lang.String");
        includeList.add("java.lang.StringCoding");
        includeList.add("java.lang.StringIndexOutOfBoundsException");
        return includeList;
    }

    private List<String> getExcludeList() {
        List<String> exList = new LinkedList<String>();
        List<CrySLRule> rules = getRules();
        for (CrySLRule r : rules) {
            exList.add(r.getClassName());
        }
        return exList;
    }

    protected abstract List<CrySLRule> getRules();

    // used to set the rules when they are loaded from headless
    // tests and not from CLI
    public static void setRules(List<CrySLRule> rules) {
        CogniCryptScanner.rules = rules;
    }

    protected abstract String applicationClassPath();

    protected ControlGraph callGraphAlgorithm() {
        return settings.getControlGraph();
    }

    protected String sootClassPath() {
        return settings.getSootPath();
    }

    protected String softwareIdentifier() {
        return settings.getSoftwareIdentifier();
    }

    protected String getOutputFolder() {
        return settings.getReportDirectory();
    }

    protected boolean isPreAnalysis() {
        return settings.isPreAnalysis();
    }

    protected boolean enableVisualization() {
        return settings.isVisualization();
    }

    protected ReportFormat reportFormat() {
        return settings.getReportFormat();
    }

    protected boolean providerDetection() {
        return settings.isProviderDetectionAnalysis();
    }

    private static String pathToJCE() {
        // When whole program mode is disabled, the classpath misses jce.jar
        return System.getProperty("java.home") + File.separator + "lib" + File.separator + "jce.jar";
    }

    private static int getJavaVersion() {
        String version = System.getProperty("java.version");
        if (version.startsWith("1.")) {
            version = version.substring(2, 3);
        } else {
            int dot = version.indexOf(".");
            if (dot != -1) {
                version = version.substring(0, dot);
            }
        }
        return Integer.parseInt(version);
    }

    private boolean isModularProject() {
        String applicationClassPath = applicationClassPath();
        File dirName = new File(applicationClassPath);
        String moduleFile = dirName + File.separator + "module-info.class";
        boolean check = new File(moduleFile).exists();
        return check;
    }

    public CryptoScanner getScanner() {
        return scanner;
    }
}
